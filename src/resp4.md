# Customer Idempotency Token

## 1. Intro

### 1.1 Problem statement

(From [More Expressive RESP](https://quip-amazon.com/FnzOAQAlbaKq))

Netflix infrastructure team built a key-value store abstraction layer on top of various databases. Some details on it’s use cases and infrastructure can be found [here](https://netflixtechblog.com/introducing-netflixs-key-value-data-abstraction-layer-1ea8a0a11b30) (Netflix’s engineering blog), but at a high level, Netflix’s engineering teams built this **Key-Value Data Abstraction Layer (KV DAL)** to address the complexity and operational load of directly using multiple distributed key-value stores across the company’s systems. As Netflix’s platform scaled, different stores (like Cassandra, EVCache, DynamoDB, RocksDB, and others) each had their own APIs, consistency semantics, and performance characteristics. Developers needed to understand these differences to model data correctly, leading to increased cognitive load, repeated work on consistency, durability, and performance tuning, and frequent changes when underlying APIs evolved. A unified abstraction was built to **** simplify data access, reduce mistakes, and improve reliability across diverse use cases. 

This KV layer **requires the underlying databases to be idempotent** to support features such as 1) request hedging, where KV layer submits multiple attempts of the same request in parallel to underlying database to achieve best-of-N latency and availability, or 2) retry after timeouts, where KV layer retains a queue of timed out requests and retry them later safely.

**ElastiCache (and MemoryDB) are not idempotent because Valkey isn’t idempotent.** Valkey clients employs RESP (REdis Serialization Protocol) protocol to send commands to server over wire. Neither RESP protocol nor Valkey server allow clients to assign unique identifier to commands.

To our knowledge, Netflix has been working around this limitation by maintaining per-key timestamps in dedicated data structures separate from actual keys. They further use LUA scripts where both keys and their timestamps are checked atomically to achieve compare-and-set(CAS) and last-writer-win (LLW) semantics to simulate idempotency.

This workaround breaks in multi-region active-active setup because client-timestamp comparisons are region-local operations and not cross-region replicated.

### 1.2 Scope

The document presents some high level ideas of how we can implement this, and some directional recommendations and estimations. Items below, though required for releasing any of these options to prod, is out of scope for this document and will be addressed in other documents. 

1. Detailed execution plans 
2. Test plans 
3. Metrics, alarms and other ORR requirements.

## 2. Background

### 2.1 Refresher: Synchronaa sequence numbers and conflict resolution

(See [4.C Sequence number generation deep dive](https://quip-amazon.com/AQVJADSWQbAa#temp:C:FMQ6a0d754853bc4e099cacc944f) for a step by step walkthrough)

When bootstrapping, the CRDT module registers an interceptor per supported command (**1**). When receiving a write command, valkey uses the interceptor to forward the command (**2**) it to the CRDT module. 

The CRDT module generates a sequence number using a system time and a region identifier (**3**). It also prevents (**4**) the engine from propagating the command as is. It stores the sequence number in thread-local context (**5**) for the command execution. The module then executes the command locally, storing in memory this seqNo, and replicates it to other regions wrapped in a (**6**) MULTI/EXEC transaction block that includes an internal-only `CRDTMETA` command containing the sequence number.  The Journal agent (**7**) replicates this to journal in the “public” topic.
[Image: Image.jpg]

On the remote region (PDX), the (**8**) Journal Agent receives the (public) replication stream from the other region (IAD). The agent forwards it to the engine **(9).** The engine processes the MULTI command (without forwarding). It then processes the CRDTMETA command, and forwards it to the CRDT module (**10**). The module processes the command, extracting and storing the sequence number from CRDTMETA (**11**). The engine processes the `SET key value` (**12**) , forwarding them to the CRDT module. The SET command handler then uses that sequence number (**14**) to apply the actual write command using Last-Writer-Wins conflict resolution if needed (**15**)  by comparing the received sequence number with any existing sequence number.

## 3. Proposal

### 3.1 Executive summary

There’s a few different ways to achieve this. Based on the current infrastructure, the simplest possible thing (~1w of effort, not accounting for deployment related work) we can do is **expose this through a custom command wrapped in `MULI/EXEC`** ([3.2 Option I: MULTI/EXEC with custom command [recommended short term]](https://quip-amazon.com/AQVJADSWQbAa#temp:C:FMQ305d660226db442d9b65ddd4f)). 

A more extensive, long-term approach is to expand RESP to allow for modules **to define and make use of custom metadata headers** ([3.3 Option II: RESP4 (VASP1?)](https://quip-amazon.com/AQVJADSWQbAa#temp:C:FMQcb82133a5e1942b29accaf376)). This extension would benefit the valkey modules community as a whole, so it is proposed as the long-term investment for Meridian. An “in-between” option is also explored in the appendix, in which a new hook is added into valkey internally to implement a poor man’s version of RESP4 ([4.A Option III: minimal engine changes [not recommended]](https://quip-amazon.com/AQVJADSWQbAa#temp:C:FMQf4493357c34b4c58972a04055)), though it is not recommended as it increases both development and maintenance costs without significant benefits for the customer.  

Either option I or III would require Netflix to eventually migrate to Option II, but Option I doesn’t introduce any version currency concerns, so the recommendation is to **release Option I to Netflix, and propose RESP4 to the valkey OSS community to implement Option II for Meridian**. A **risk** of this proposal is that given this proposal would require alignment with open source; and then a new major version of Valkey (as it introduces a new client protocol) and client upgrades (which should include `GLIDE`), it will be challenging to have this available in the re:invent timeline with valkey 10. 

### 3.2 Option I: MULTI/EXEC with custom command [recommended short term]

#### 3.2.1 High level idea

Recall how [2.1 Refresher: Synchronaa sequence numbers and conflict resolution](https://quip-amazon.com/AQVJADSWQbAa#temp:C:FMQd368b762f2df4c48a7e93bfaf) work: by using the **CRDTMETA** command wrapped in a MULTI/EXEC block. The idea is to piggy back of this implementation, to essentially provide a customer facing version of this command, which needs to be used in a transaction context (wrapped in MULTI/EXEC), and which applies the timestamp provided to the sequence number of the next immediate command. 

When bootstrapping, the CRDT module registers an interceptor per supported command (**1**) Here, we will register our **new interceptor for CUSTOM_TS**. The customer now sends the set command wrapped in MULTI/EXEC, including this new command. 

When receiving the `MULTI` block, the engine processes it. Then, it processes the CUSTOM_TS command, valkey uses the interceptor to forward the command (**2**) it to the CRDT module. The CRDT module extracts the timestamp value, and stores the sequence number in thread-local context (**3**), and prevents replication for this command (**4**). As opposed to ‘regular’ commands, CUSTOM_TS behaves as CRDTMETA in that the seqNo context is *not* cleared after the command.

The engine then processes the SET command, it forwards it to the CRDT Module (**5**). The SET command handler uses the stored timestamp (just as it would, before, in the remote region). If it finds a conflict with a stored seqNo for the key, it resolves it using LWW **(7).** 

[Image: Image.jpg]
From then on, **the path is the same as it is today** (see [2.1 Refresher: Synchronaa sequence numbers and conflict resolution](https://quip-amazon.com/AQVJADSWQbAa#temp:C:FMQd368b762f2df4c48a7e93bfaf)). We replicate to the public stream (**8**), replacing CUSTOM_TS by CRDTMETA, and using the customer timestamp. This is put in the replication stream (**9**), passed to Journal by the agent (**10**) and eventually received by the remote region (**11**). 

Journal Agent forwards to the engine (**12**), which in turn forwards to the CRDT package (**13**). The package stores the customer provided timestamp in thread local (**14**) and prevents replication. The engine forwards `SET key value` to the module (**15**), and the set command handler (**16**) is executed. The handler uses the stored seqNO (17), resolves conflicts if needed (**18**) and applies the command. 

#### 3.2.2 CUSTOM_TS Definition

1. **CUSTOM_TS** command must be used within a transaction context. I.e within a MULTI/EXEC block.
2. A **CUSTOM_TS** command applies to the **very next write command encountered within the transaction**. The timestamp is stored in thread-local context and consumed by the subsequent write operation.
3. Each **CUSTOM_TS** command is consumed by exactly one write command. After the timestamp is used for sequence number generation, it is immediately cleared from thread-local storage.
4. If a write command is **executed without a preceding CUSTOM_TS**, the system automatically generates a sequence number using the current system timestamp as we do today. 
5. **CUSTOM_TS** commands do not affect read-only commands. If a CUSTOM_TS precedes a read command, **it still will be applied to the next immediate write command.**
    1. Note that, because READ commands are not forwarded to the CRDT module (we have no interceptors for them), the above behaviour follows from “doing nothing” about it. We can also error out “CUSTOM_TS cannot precede a write command” but that involves either engine logic, or intercepting all read commands as well.
6. **Customer timestamps do not persist beyond transaction boundaries**. Any unused CUSTOMER_TIMESTAMP at the end of EXEC is cleared during transaction cleanup.
7. I**nvalid timestamps (non-numeric values)** cause an error. E.g `“CUSTOM_TS is not a valid UNIX timestamp”`. 
    1. We could also “ignore” them, but the silent failure will most likely cause issues for customers.


_Example_

```
MULTI
CUSTOMER_TIMESTAMP 1698776172000000  # Applies to next SET
SET key1 value1                      # Uses customer timestamp
CUSTOMER_TIMESTAMP 1698776173000000  # Applies to next SET  
SET key2 value2                      # Uses different customer timestamp
SET key3 value3                      # No CUSTOMER_TIMESTAMP, uses auto-generated timestamp
EXEC
```

**The example above also illustrates an important point.** If the customer is currently doing

```
MULTI
SET A, B
SET C, D
EXEC
```

They cannot simply wrap this in another multi-exec, and have that timestamp apply to the whole transaction:

```
#this doesnt work
MULTI
    CUSTOMER_TIMESTAMP 1234
        MULTI
            SET A, B
            SET C, D
        EXEC
EXEC

```

This would be non-trivial to support (and arguably, undesirable), for two main reasons:

1. Valkey doesn’t support nested MULTI/EXEC blocks, and we let Valkey handle the “transaction context”. So this would require some changes (unscoped in depth, but likely medium to large) in how MULTI/EXEC works. 
2. Our current CRDT implementation ([ref1](https://code.amazon.com/packages/SynchronaaCRDT/blobs/eaa7b7e4f1c38c50943c03fcdeb75a8380f1fd9d/--/amztests/test_db_commands.py#L52-L77), [ref2](https://code.amazon.com/packages/SynchronaaCRDT/blobs/0da0ff8219fbb20f3dd2880bdc5b1a365e6b6df0/--/src/hook.rs#L40-L41)) **creates different sequence numbers for each cmd in a transaction**, and they monotonically increase. Reason was documented [here](https://quip-amazon.com/fj8VAXhKJcCU/High-Level-Design-Transactions-for-CRDT#temp:C:KIZ97b135daf87a423a9e5a14539). 
    1. Supporting “one timestamp per transaction” (i.e we apply the same timestamp until we see an EXEC or a different one) would be a moderate amount of effort, but without more intrusive changes, we cannot guarantee that all commands in a transaction “win” or “lose” together. **When allowing the customer to provide one timestamp for the whole transaction, customers might assume this is the behaviour.** 

#### 3.2.3 Pros and cons

There’s two major advantages of this solution:

1. **It is very simple to implement.** Because it piggy backs of the current infrastructure to handle `CRDT_META` , the functional code-changes are small. See a POC in this branch (todo). The bulk of the effort is likely to revolve around making the code prod ready: testing, figuring out if new metrics or alarms are needed, cherry picking, etc.  Estimate is around 2w of effort. 
2. Because **it can be implemented directly in the SynchronaaCRDT package**, we don’t require any changes to engine code, which makes this a lot easier to maintain long term, if needed. It also doesn’t interfere with version currency effort.


The main drawbacks are two

1. We believe that the more extensible, long term approach is [3.3 Option II: RESP4 (VASP1?)](https://quip-amazon.com/AQVJADSWQbAa#temp:C:FMQcb82133a5e1942b29accaf376). Meaning that **we’d give this to Netflix and, after a “short” time, ask them to migrate *off* this implementation and onto the new one**. We also must mantain both solutions until that happens.
    1. We do have an advantage that we can make this “breaking change” part of the Meridian migration story for them, if that is a viable path. 
    2. Another caveat is that Netflix built the KV value store in part to be able to more readily handle API changes in their dependencies. So even if we provide this to Netflix, it won’t be used across many different things needing to then upgrade. Rather, it would be handled centrally by the KV infrastructure. 
    3. The final caveat is that this simple solution should not incur too much maintenance overhead. (Famous last words)
2. **If netflix is using transactions today (or it they want to), the Key value store needs to deal with the behaviour above**. I.e they can just “Wrap” any other calls in a MULTI/EXEC block, but if they have a transaction, they need to prepend a CUSTOM_TS to every write command. 

### 3.3 Option II: RESP4 *(VASP1?)*

#### 3.3.1  High level idea

The Valkey **Redis Serialization Protocol (RESP)** defines how clients talk to the server. RESP 2 and RESP 3 are widely used, and the [official specification](https://valkey.io/topics/protocol/) explains their data types and handshake mechanism. RESP 3 added support for new aggregate types and **attributes**. The attribute type is similar to a map but is prefixed with the `|` character instead of `%`; it represents auxiliary metadata that accompanies a response and isn’t considered part of the reply. The protocol specification notes that attributes describe a dictionary and the client should treat them as auxiliary data. Attributes may appear before a reply type and apply only to the part of the response that immediately follows. Valkey modules can already add such attributes to replies using `ValkeyModule_ReplyWithAttribute`, which must be called before the actual reply.

However, **RESP3 does not allow clients to send attributes to the server**, so modules cannot receive request-side metadata. A mechanism for this was proposed in Redis, though it focused on a specific correctness concern rather than general metadata transport. In practice, most modern protocols provide some notion of headers or envelopes for out-of-band metadata—HTTP headers, gRPC metadata, and messaging-system properties are typical examples. Supporting client-side attributes in RESP would therefore be a conventional and predictable extension.

Building on this idea and the existing attribute type, **RESP 4** would extend RESP 3 to support **request‑side attributes** (called *command headers* hereafter). These headers are parsed by the Valkey engine before the command itself and are exposed to modules as **command attributes**.  A module can then register a set of headers, and get them from the engine through a new module API, to handle them according to its business logic. 


[Image: Image.jpg]

The goal is to allow modules to implement correlation IDs, idempotency keys, tracing metadata, or domain‑specific information in a structured way without changing command syntax (See Appendix [4.D Other use-cases for RESP4](https://quip-amazon.com/AQVJADSWQbAa#temp:C:FMQ681f7db8ee0e494cba746d670) and [More Expressive RESP](https://quip-amazon.com/FnzOAQAlbaKq) for more details on the use cases). The diagram above represents a typical a use case (e.g OpenTelemetry on gRCP), where the module implements distributed tracing via `trace-id` headers. The server remains backward‑compatible: **clients that speak RESP 2/3 continue to work as before, while clients that negotiate RESP 4 can use headers.** 

#### 3.3.2 RESP4 definition

**Header encoding**

A command header uses the existing RESP 3 **attribute** type (prefix `|`), encoded as a map of key/value pairs. The attribute is sent *immediately before* the command array. The general form is:

```
|<n>\r\n
  <key‑type> <key> <value‑type> <value> ... (repeated for n key/value pairs)
*<m>\r\n
  $<len>\r\n
  <command name>\r\n
  $<len>\r\n
  <arg1>\r\n
  ...
```

where `<n>` is the number of header fields, `<key>` is a bulk or simple string identifying the header name, and `<value>` is any RESP data type allowed for attribute values (simple/bulk strings, integers, doubles, booleans, arrays, maps). `<m>` is the number of command elements (command name plus arguments).

A header **applies only to the *next* command array**. When commands are pipelined, each command that needs attributes must be preceded by its own header. Headers do not apply to subsequent commands.  

**Unregistered headers** – Header names that are not registered by any module are ignored (or, optionally, produce a `-ERR unknown header` error). This prevents clients from inadvertently sending unrecognized metadata.

#### 3.3.3 Suggested Module APIs

Modules MAY use these APIs only when the connection has negotiated RESP4. If RESP4 is not active, these APIs behave as if no headers were supplied.

A module may declare interest in specific headers so the server can optionally validate or optimize handling. Registration does not make a header mandatory; it only defines recognition and optional type constraints.

```
int ValkeyModule_RegisterRequestHeader(
    ValkeyModuleCtx *ctx,
    const char *name,
    int flags,
    int expected_type);
```

This function registers a header name that the module can consume. `expected_type` MAY constrain the RESP type (e.g., integer, bulk string, simple string). If a type is declared and a client sends a mismatched type, the server SHOULD reject the command with an error before execution. If no type is declared, any RESP scalar type is accepted. Header names are case-insensitive. If multiple modules register the same header, registration fails for later modules.

Modules retrieve header values from the current command via:

```
int ValkeyModule_RequestHeaderExists(
    ValkeyModuleCtx *ctx,
    const char *name);
```

This returns non-zero if the header was present on the request, zero otherwise.

```
ValkeyModuleString *ValkeyModule_GetRequestHeader(
    ValkeyModuleCtx *ctx,
    const char *name);
```

This returns the header value as a `ValkeyModuleString*` if present, or NULL if absent. The returned value is owned by the server and remains valid only for the duration of the command callback. Modules MUST NOT free or retain it beyond the callback lifetime.

We can also consider offering typed helpers such as:

```
int ValkeyModule_GetRequestHeaderLongLong(
    ValkeyModuleCtx *ctx,
    const char *name,
    long long *ll);
```

This attempts to coerce the header value to an integer and stores it in `ll`. It returns `VALKEYMODULE_OK` on success or `VALKEYMODULE_ERR` on absence or type mismatch.

Modules may also want to iterate over all supplied headers:

```
ValkeyModuleHeaderIter *ValkeyModule_RequestHeaderIterStart(
    ValkeyModuleCtx *ctx);

int ValkeyModule_RequestHeaderIterNext(
    ValkeyModuleHeaderIter *iter,
    ValkeyModuleString **name,
    ValkeyModuleString **value);

void ValkeyModule_RequestHeaderIterStop(
    ValkeyModuleHeaderIter *iter);
```

This allows generic middleware-style modules (e.g., logging, tracing, policy engines) to inspect all headers without prior registration.

Request headers are immutable from the module’s perspective. Modules cannot modify or inject request headers, and they are not replicated or propagated unless a module explicitly encodes related information into normal command arguments or replies. **Reply attributes continue to use the existing RESP3 attribute APIs and are unaffected by these additions.**

If a client sends a header that no module has registered or queried, the server ignores it by default. This preserves forward compatibility and allows incremental deployment of new headers. We can choose to provide an optional, configurable, “STRICT” policy, as well. 

**Notes**

* Headers are strictly scoped to a single command. After the command completes (successfully or with error), the server clears the stored header map from the client as part of normal command cleanup. 
* If a client sends a header that no loaded module has registered or claimed, the server simply ignores it and continues processing the command normally. This makes headers forward-compatible and safe to deploy incrementally. An alternative policy is to reject unknown headers with an error, but the default behavior is to ignore them so that clients and modules can evolve independently.

#### 3.3.5 Pros and cons

There are several advantages of this solution:

1. **Extensible** - opens the door to support all sorts of things (even full Idempotency token behaviour and not just LWW) without needing engine-side changes. Future metadata like request IDs, auth tokens, routing context can all use the same header infrastructure.
2. **Useful for OSS Valkey as much as EC Valkey** - this becomes a general protocol enhancement that benefits the entire ecosystem, not just our specific use case.
3. **Doesn't add the overhead of an extra command, improving latency and CPU utilization** compared to the MULTI/EXEC approach.
4. **Headers are separated from command logic, making client implementation more straightforward** and less error-prone.
5. Follows established patterns from HTTP headers, gRPC metadata, SQS queues attributes, etc, making it familiar to developers.

The main drawbacks are:

1. **Big effort -** requires a new protocol version, new code in the Valkey engine, updates to GLIDE and other client libraries. This is likely a large effort (see [4.B RESP4 High Level estimations [DRAFT]](https://quip-amazon.com/AQVJADSWQbAa#temp:C:FMQcf51cde6e9874fd091143aa83)) across multiple teams and the open source community.
2. **Dependency on open source** - we need Valkey community approval for RESP4, which introduces timeline risks outside our control. The collaborative process could extend delivery beyond re:Invent or other target dates, especially with how much we are already attempting to open source at once. 
3. **Client ecosystem coordination** - requires updates to GLIDE, redis-py, jedis, and other major clients before customers can actually use it. 
4. **Overhead of keeping headers in memory during command processing**, though this should be minimal for typical use cases.


### 4.D Other use-cases for RESP4

>**Note** the section below *isn’t* recommending we implement any of these beyond idempotency token in Synchronaa/Meridian, though the extension would allow us to refactor some of our modules/interfaces to make use of it. It is meant to illustrate the use cases it would allow modules to implement in OSS. 


**Authentication / Authorization context**

Many protocols carry auth context in headers rather than in the main payload.  HTTP has `Authorization: Bearer <token>` , gRPC provides `authorization` metadata, AMQP allow for message properties for user/app identity. 

_RESP4 example_

A module registers `authorization`:

```
|1\r\n
+authorization\r\n$18\r\nBearer abc123...\r\n
*2\r\n$3\r\nGET\r\n$3\r\nfoo\r\n
```

A security module validates the token and applies ACLs without changing command syntax.

**Request correlation / tracing**

This is widely used for distributed tracing. HTTP has `X-Request-ID`, `traceparent` , gRPC has tracing metadata, etc. Many telemetry frameworks (such as open-telemetry) make use of these for tracing and debugging.

_RESP4 example_

```
|1\r\n
+request-id\r\n$12\r\nreq-9f812aa2\r\n
*2\r\n$4\r\nINCR\r\n$7\r\ncounter\r\n
```

A tracing module logs and propagates the ID across services.

**Routing / tenancy context**

Common in multi-tenanted environments or proxy setups. Equivalent are `Host` headers in http, or routing keys in AMQP. 

_RESP example_

```
|1\r\n
+tenant\r\n$6\r\nacme01\r\n
*2\r\n$3\r\nGET\r\n$8\r\nuser:123\r\n
```

A module enforces tenant isolation or routes internally to specific dbs. 







