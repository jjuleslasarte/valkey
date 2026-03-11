# Proposal: Clean Up Durability Provider Registration & Add DEBUG Pause

## Problem Statement

When testing the AOF durability provider with:
```
--sync-replication yes --appendonly yes --appendfsync no
```
...the AOF provider acts as if it's **not registered**. Writes don't block, and the test's trick of flipping `appendfsync` from `no` → `always` to trigger an unblock doesn't work as expected.

### Root Cause Analysis

The problem is a **chicken-and-egg issue** in `aofProviderIsEnabled()`:

```c
static bool aofProviderIsEnabled(void) {
    return server.aof_state != AOF_OFF && server.aof_fsync == AOF_FSYNC_ALWAYS;
}
```

The AOF provider is *always registered* (via `registerBuiltinDurabilityProviders()` at `syncReplicationInit()` time), but `isEnabled()` requires **both** `aof_state != AOF_OFF` **and** `aof_fsync == AOF_FSYNC_ALWAYS`.

When you start with `--appendfsync no`, here's what happens:

1. **Server boots** → `syncReplicationInit()` → registers the AOF provider.
2. **Client sends `SET durable:blocked value`** → `postCommandExec()` calls `blockClientAndMonitorsOnReplOffset()`.
3. Inside `blockClientOnReplOffset()` → `isBlockingNeededForOffset()` calls `anyDurabilityProviderEnabled()`.
4. `anyDurabilityProviderEnabled()` iterates providers → calls `aofProviderIsEnabled()` → returns **false** (because `aof_fsync == AOF_FSYNC_NO`).
5. Since no provider is enabled, `isBlockingNeededForOffset()` returns 0 → **the write is NOT blocked**.
6. The reply goes through immediately — the test fails because it expected the reply to be held.

Even when the test later does `$primary config set appendfsync always`, the damage is already done — the write reply was never blocked in the first place, so there's nothing to unblock.

### Why the replica mode works fine

In replica mode, when you start with `--sync-replication yes` and no replica connected, there are no durability providers enabled initially... but the key difference is that the **replica provider isn't even in the registry** — it's expected to be registered externally. The test's `unblock_with_provider` connects a replica, which causes `postReplicaAck()` to fire — but more importantly, in replica mode the system relies on `clients_waiting_replica_ack` having entries and `hasUncommittedKeys()` returning true, which drives the blocking offset calculation differently.

Wait — actually re-reading `getSingleCommandBlockingOffsetForConsistentWrites()`:

```c
if ((listLength(server.durability.clients_waiting_replica_ack) > 0 ||
     hasUncommittedKeys() || isDurableFunctionStoreUncommitted())) {
    blocking_repl_offset = server.primary_repl_offset;
}
```

This path doesn't even check `anyDurabilityProviderEnabled()` — it checks the waiting list. But the first client to write hits a different path and the blocking decision happens in `blockClientOnReplOffset()` → `isBlockingNeededForOffset()`:

```c
static int isBlockingNeededForOffset(const client *c, const long long offset) {
    if (offset == -1 || anyDurabilityProviderEnabled() == 0) {
        return 0;  // <--- THIS IS THE GATE
    }
    ...
}
```

**This is the critical gate.** If `anyDurabilityProviderEnabled()` returns 0, no client ever gets blocked, regardless of the offset calculation. The AOF provider IS registered, but it reports itself as disabled when `appendfsync != always`.

---

## Proposed Solution

### Part 1: Always-Registered AOF Provider (Decouple Registration from `appendfsync` Policy)

**Change `aofProviderIsEnabled()` to only check if AOF is on, not the fsync policy:**

```c
static bool aofProviderIsEnabled(void) {
    return server.aof_state != AOF_OFF;
}
```

**Change `aofProviderGetAckedOffset()` to be fsync-policy-aware:**

```c
static long long aofProviderGetAckedOffset(void) {
    /* If appendfsync is not "always", we cannot guarantee data is on disk.
     * Return the primary repl offset to indicate "no constraint" —
     * effectively making this provider a pass-through that doesn't block. */
    if (server.aof_fsync != AOF_FSYNC_ALWAYS) {
        return server.primary_repl_offset;
    }
    
    long long fsynced_offset = atomic_load_explicit(
        &server.fsynced_reploff_pending, memory_order_relaxed);
    if (fsynced_offset == 0 && server.fsynced_reploff > 0) {
        fsynced_offset = server.fsynced_reploff;
    }
    return fsynced_offset;
}
```

**Why this is better:**
- The AOF provider is "enabled" whenever AOF is on — this means `anyDurabilityProviderEnabled()` returns true, so writes actually get blocked.
- When `appendfsync != always`, `getAckedOffset()` returns `primary_repl_offset` (i.e., "everything is acked"), making it a transparent pass-through in the MIN consensus.
- When `appendfsync` is flipped to `always`, the provider immediately starts returning the actual fsynced offset, which is behind `primary_repl_offset` — so the consensus tightens and writes block.
- This is still correct for the AND-semantics: other providers (replica) would set the actual blocking bound.

**However**, this alone doesn't solve the test problem — because with `appendfsync no` and no replica, the AOF provider would return `primary_repl_offset` as acked, so nothing blocks. The test needs *something* to block against.

### Part 2: Add a "Paused" / Debug Mode for Durability Providers

Add a per-provider `paused` flag (or a global debug mechanism) that artificially makes a provider report offset 0 (i.e., "nothing is acked"), causing writes to block until the pause is lifted.

**Option A: Per-provider pause flag (preferred — clean, general)**

```c
typedef struct durabilityProvider {
    const char *name;
    bool (*isEnabled)(void);
    long long (*getAckedOffset)(void);
    bool paused;  /* When true, getAckedOffset() returns 0 (blocks everything) */
} durabilityProvider;
```

And in `getDurabilityConsensusOffset()`:

```c
long long getDurabilityConsensusOffset(void) {
    long long consensus = server.primary_repl_offset;
    bool any_enabled = false;

    for (int i = 0; i < num_durability_providers; i++) {
        durabilityProvider *p = durability_providers[i];
        if (!p->isEnabled()) continue;
        any_enabled = true;
        
        long long offset;
        if (p->paused) {
            offset = 0;  /* Paused provider blocks all progress */
        } else {
            offset = p->getAckedOffset();
        }
        
        if (offset == -1) return -1;
        if (offset < consensus) consensus = offset;
    }

    return any_enabled ? consensus : server.primary_repl_offset;
}
```

**Option B: Global debug pause (simpler, test-only)**

Add a `server.durability.debug_pause_providers` flag that, when set, makes `getDurabilityConsensusOffset()` return 0.

**Recommendation: Option A** — it's more general, allows pausing individual providers, and integrates cleanly with the existing provider architecture.

### Part 3: Expose via DEBUG Command

Add a `DEBUG DURABILITY-PROVIDER-PAUSE <name>` and `DEBUG DURABILITY-PROVIDER-RESUME <name>` subcommand:

```c
// In debug.c debugCommand():
} else if (!strcasecmp(c->argv[1]->ptr, "durability-provider-pause") && c->argc == 3) {
    if (pauseDurabilityProvider(c->argv[2]->ptr)) {
        addReply(c, shared.ok);
    } else {
        addReplyError(c, "No such durability provider");
    }
} else if (!strcasecmp(c->argv[1]->ptr, "durability-provider-resume") && c->argc == 3) {
    if (resumeDurabilityProvider(c->argv[2]->ptr)) {
        addReply(c, shared.ok);
    } else {
        addReplyError(c, "No such durability provider");
    }
}
```

New functions in `durability_provider.c`:

```c
bool pauseDurabilityProvider(const char *name) {
    for (int i = 0; i < num_durability_providers; i++) {
        if (!strcasecmp(durability_providers[i]->name, name)) {
            durability_providers[i]->paused = true;
            serverLog(LL_NOTICE, "Paused durability provider: %s", name);
            return true;
        }
    }
    return false;
}

bool resumeDurabilityProvider(const char *name) {
    for (int i = 0; i < num_durability_providers; i++) {
        if (!strcasecmp(durability_providers[i]->name, name)) {
            durability_providers[i]->paused = false;
            /* Trigger a durability check to unblock any clients that can now proceed */
            notifyDurabilityProgress();
            serverLog(LL_NOTICE, "Resumed durability provider: %s", name);
            return true;
        }
    }
    return false;
}
```

### Part 4: Simplified Test Pattern

With these changes, the test becomes much cleaner:

```tcl
# AOF mode: start with appendonly yes, appendfsync always (provider is always active)
# Use DEBUG to pause/resume the provider for blocking control
set server_overrides {sync-replication yes appendonly yes appendfsync always}

# Helper: trigger durability acknowledgement
proc unblock_with_provider {} {
    if {$provider_mode eq "replica"} {
        # ... existing replica logic ...
    } else {
        # Resume the AOF provider — the next beforeSleep will fsync and unblock
        $primary DEBUG durability-provider-resume aof
        $primary ping  ;# Force a beforeSleep cycle
    }
}

# Helper: reset provider state after test
proc cleanup_provider {} {
    if {$provider_mode eq "replica"} {
        # ... existing replica logic ...
    } else {
        # Pause the AOF provider so next write blocks
        $primary DEBUG durability-provider-pause aof
    }
}
```

And at test setup:
```tcl
if {$provider_mode eq "aof"} {
    # Pause the AOF provider at the start so writes block
    $primary DEBUG durability-provider-pause aof
}
```

---

## Summary of Changes

| File | Change |
|------|--------|
| `src/durability_provider.h` | Add `bool paused` to `durabilityProvider` struct; declare `pauseDurabilityProvider()` / `resumeDurabilityProvider()` |
| `src/durability_provider.c` | (1) Change `aofProviderIsEnabled()` to only check `aof_state`; (2) Change `aofProviderGetAckedOffset()` to return `primary_repl_offset` when `fsync != always`; (3) Handle `paused` flag in `getDurabilityConsensusOffset()`; (4) Add `pauseDurabilityProvider()` / `resumeDurabilityProvider()`; (5) Init `paused = false` in `builtinAofProvider` |
| `src/debug.c` | Add `DEBUG DURABILITY-PROVIDER-PAUSE <name>` and `DEBUG DURABILITY-PROVIDER-RESUME <name>` subcommands |
| `tests/durability/reply_blocking.tcl` | Simplify AOF mode: start with `appendfsync always`, use `DEBUG durability-provider-pause/resume aof` instead of toggling `appendfsync` |

### Benefits
1. **AOF provider is always active when AOF is on** — no more silent "not registered" behavior.
2. **Clean separation of concerns**: registration/enablement is about whether the persistence layer exists; fsync policy determines the acked offset.
3. **DEBUG pause is general-purpose**: works for any provider, useful for testing without config hacks.
4. **Test is more explicit**: instead of relying on the side-effect of `appendfsync no` meaning "provider disabled", the test explicitly pauses/resumes providers.
5. **No production behavior change**: in production, `paused` is always false, and the AOF provider with `appendfsync always` works exactly as before.

### Risks / Considerations
- The `paused` flag is mutable state on a static struct — safe in single-threaded command processing, but should **not** be accessed from IO threads. Since `getDurabilityConsensusOffset()` is only called from the main thread (in `postDurabilityAck()`), this is fine.
- `DEBUG` commands are not replicated to replicas, so pausing on the primary doesn't affect replica behavior. This is the correct behavior.
- If someone starts with `appendfsync everysec` + `sync-replication yes`, the AOF provider will be "enabled" but will pass-through (return `primary_repl_offset`). This means writes won't block on AOF durability unless `appendfsync` is set to `always`. This is correct behavior — `everysec` doesn't provide per-write durability guarantees.
