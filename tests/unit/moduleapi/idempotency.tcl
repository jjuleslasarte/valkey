# Test Idempotency Token Module (RESP4) via the idempotency module.

set testmodule [file normalize src/modules/idempotency.so]

# Helper: create a raw TCP socket, negotiate RESP4, and return the fd.
proc resp4_raw_client {host port} {
    set fd [socket $host $port]
    fconfigure $fd -translation binary -buffering none -blocking 1
    return $fd
}

proc resp4_send {fd data} {
    puts -nonewline $fd $data
}

proc resp4_readline {fd} {
    set line ""
    while {1} {
        set ch [read $fd 1]
        if {$ch eq ""} {
            error "resp4_readline: EOF"
        }
        if {$ch eq "\r"} {
            read $fd 1
            break
        }
        append line $ch
    }
    return $line
}

proc resp4_readn {fd n} {
    set data ""
    while {[string length $data] < $n} {
        set chunk [read $fd [expr {$n - [string length $data]}]]
        if {$chunk eq ""} {
            error "resp4_readn: EOF"
        }
        append data $chunk
    }
    return $data
}

proc resp4_read_value {fd} {
    set line [resp4_readline $fd]
    set type [string index $line 0]
    set rest [string range $line 1 end]
    switch $type {
        "+" - "-" - ":" {
            return $rest
        }
        "#" {
            return $rest
        }
        "$" {
            set blen [expr {int($rest)}]
            if {$blen == -1} { return "(nil)" }
            set data [resp4_readn $fd [expr {$blen + 2}]]
            return [string range $data 0 end-2]
        }
        "*" {
            set n [expr {int($rest)}]
            if {$n == -1} { return "(nil)" }
            set result [list]
            for {set i 0} {$i < $n} {incr i} {
                lappend result [resp4_read_value $fd]
            }
            return $result
        }
        "%" {
            set n [expr {int($rest)}]
            set result [list]
            for {set i 0} {$i < [expr {$n * 2}]} {incr i} {
                lappend result [resp4_read_value $fd]
            }
            return $result
        }
        "|" {
            # Reply attribute: read and discard, then read the actual value
            set n [expr {int($rest)}]
            for {set i 0} {$i < [expr {$n * 2}]} {incr i} {
                resp4_read_value $fd
            }
            return [resp4_read_value $fd]
        }
        "~" {
            set n [expr {int($rest)}]
            set result [list]
            for {set i 0} {$i < $n} {incr i} {
                lappend result [resp4_read_value $fd]
            }
            return $result
        }
        "_" {
            return "(nil)"
        }
        "," {
            return $rest
        }
        default {
            return "${type}${rest}"
        }
    }
}

# Read a reply attribute block and return it as a dict, then read the actual value.
# Returns a two-element list: {attributes_dict actual_value}
proc resp4_read_value_with_attrs {fd} {
    set line [resp4_readline $fd]
    set type [string index $line 0]
    set rest [string range $line 1 end]

    if {$type eq "|"} {
        # This is an attribute block
        set n [expr {int($rest)}]
        set attrs [list]
        for {set i 0} {$i < [expr {$n * 2}]} {incr i} {
            lappend attrs [resp4_read_value $fd]
        }
        # Now read the actual value
        set val [resp4_read_value $fd]
        return [list $attrs $val]
    } else {
        # Not an attribute, parse as normal value
        switch $type {
            "+" - "-" - ":" {
                return [list {} $rest]
            }
            "#" {
                return [list {} $rest]
            }
            "$" {
                set blen [expr {int($rest)}]
                if {$blen == -1} { return [list {} "(nil)"] }
                set data [resp4_readn $fd [expr {$blen + 2}]]
                return [list {} [string range $data 0 end-2]]
            }
            "_" {
                return [list {} "(nil)"]
            }
            default {
                return [list {} "${type}${rest}"]
            }
        }
    }
}

proc resp4_negotiate {fd} {
    resp4_send $fd "*2\r\n\$5\r\nHELLO\r\n\$1\r\n4\r\n"
    resp4_read_value $fd
    resp4_send $fd "*1\r\n\$4\r\nPING\r\n"
    set pong [resp4_readline $fd]
    if {$pong ne "+PONG"} {
        error "resp4_negotiate: expected +PONG, got '$pong'"
    }
}

# Helper to build RESP bulk string
proc bulk {s} {
    set len [string length $s]
    return "\$$len\r\n$s\r\n"
}

# Helper to build a RESP array command from a list of strings
proc resp_cmd {args} {
    set n [llength $args]
    set result "*$n\r\n"
    foreach a $args {
        append result [bulk $a]
    }
    return $result
}

# Helper to build a header block with one header key-value pair
proc resp4_header1 {key val} {
    return "|1\r\n[bulk $key][bulk $val]"
}

# Helper to build a header block with idempotency-token
proc idem_header {token} {
    return [resp4_header1 "idempotency-token" $token]
}

start_server {tags {"modules"}} {
    r module load $testmodule

    # ========== Basic module loading ==========

    test {Idempotency module loads successfully} {
        set modules [r MODULE LIST]
        set found 0
        foreach m $modules {
            if {[dict get $m name] eq "idempotency"} {
                set found 1
            }
        }
        assert_equal $found 1
    }

    # ========== IDEMPOTENT.EXEC — new execution ==========

    test {IDEMPOTENT.EXEC executes command and returns result with new token} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Send idempotency-token header + IDEMPOTENT.EXEC SET mykey myval
        set token "tok-new-exec-001"
        resp4_send $fd "[idem_header $token][resp_cmd IDEMPOTENT.EXEC SET mykey myval]"

        # Read: attribute block + actual reply
        set result [resp4_read_value_with_attrs $fd]
        set attrs [lindex $result 0]
        set val [lindex $result 1]

        # The actual command result should be OK
        assert_equal $val "OK"

        # Check attributes contain token-status=new
        set attr_dict [dict create]
        foreach {k v} $attrs { dict set attr_dict $k $v }
        assert_equal [dict get $attr_dict "token-status"] "new"

        # Verify the key was actually set
        resp4_send $fd "[resp_cmd GET mykey]"
        set getval [resp4_read_value $fd]
        assert_equal $getval "myval"

        # Cleanup
        resp4_send $fd "[resp_cmd DEL mykey]"
        resp4_read_value $fd
        close $fd
    }

    # ========== IDEMPOTENT.EXEC — cached replay ==========

    test {IDEMPOTENT.EXEC returns cached result for duplicate token} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        set token "tok-dup-001"

        # First call: new execution
        resp4_send $fd "[idem_header $token][resp_cmd IDEMPOTENT.EXEC SET dupkey dupval1]"
        set result [resp4_read_value_with_attrs $fd]
        set attrs1 [lindex $result 0]
        set val1 [lindex $result 1]
        assert_equal $val1 "OK"
        set ad1 [dict create]
        foreach {k v} $attrs1 { dict set ad1 $k $v }
        assert_equal [dict get $ad1 "token-status"] "new"

        # Second call: same token, different args — should return cached result
        resp4_send $fd "[idem_header $token][resp_cmd IDEMPOTENT.EXEC SET dupkey dupval2]"
        set result [resp4_read_value_with_attrs $fd]
        set attrs2 [lindex $result 0]
        set val2 [lindex $result 1]

        set ad2 [dict create]
        foreach {k v} $attrs2 { dict set ad2 $k $v }
        assert_equal [dict get $ad2 "token-status"] "cached"

        # The key should still have the FIRST value (second execution was skipped)
        resp4_send $fd "[resp_cmd GET dupkey]"
        set getval [resp4_read_value $fd]
        assert_equal $getval "dupval1"

        # Cleanup
        resp4_send $fd "[resp_cmd DEL dupkey]"
        resp4_read_value $fd
        close $fd
    }

    # ========== IDEMPOTENT.EXEC — different tokens execute independently ==========

    test {IDEMPOTENT.EXEC with different tokens execute independently} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # First token
        resp4_send $fd "[idem_header tok-diff-001][resp_cmd IDEMPOTENT.EXEC SET diffkey val1]"
        set result [resp4_read_value_with_attrs $fd]
        assert_equal [lindex $result 1] "OK"

        # Different token, same key — should execute (overwrites)
        resp4_send $fd "[idem_header tok-diff-002][resp_cmd IDEMPOTENT.EXEC SET diffkey val2]"
        set result [resp4_read_value_with_attrs $fd]
        set ad [dict create]
        foreach {k v} [lindex $result 0] { dict set ad $k $v }
        assert_equal [dict get $ad "token-status"] "new"

        # The key should have the second value
        resp4_send $fd "[resp_cmd GET diffkey]"
        assert_equal [resp4_read_value $fd] "val2"

        resp4_send $fd "[resp_cmd DEL diffkey]"
        resp4_read_value $fd
        close $fd
    }

    # ========== IDEMPOTENT.EXEC — error without token ==========

    test {IDEMPOTENT.EXEC errors without idempotency-token header} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Send without any headers
        resp4_send $fd "[resp_cmd IDEMPOTENT.EXEC SET notoken val]"
        set reply [resp4_readline $fd]
        assert_match {-ERR*idempotency-token*} $reply

        close $fd
    }

    # ========== IDEMPOTENT.EXEC — error with empty token ==========

    test {IDEMPOTENT.EXEC errors with empty token} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        resp4_send $fd "[resp4_header1 idempotency-token {}][resp_cmd IDEMPOTENT.EXEC SET emptytoken val]"
        set reply [resp4_readline $fd]
        assert_match {-ERR*} $reply

        close $fd
    }

    # ========== IDEMPOTENT.EXEC — INCR is idempotent ==========

    test {IDEMPOTENT.EXEC makes INCR idempotent} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Set counter to 10
        resp4_send $fd "[resp_cmd SET counter 10]"
        resp4_read_value $fd

        set token "tok-incr-001"

        # INCR with token — should return 11
        resp4_send $fd "[idem_header $token][resp_cmd IDEMPOTENT.EXEC INCR counter]"
        set result [resp4_read_value_with_attrs $fd]
        # INCR returns integer, value might come as string from our parser
        set val [lindex $result 1]

        # Retry INCR with same token — should return cached 11, not 12
        resp4_send $fd "[idem_header $token][resp_cmd IDEMPOTENT.EXEC INCR counter]"
        set result2 [resp4_read_value_with_attrs $fd]
        set ad [dict create]
        foreach {k v} [lindex $result2 0] { dict set ad $k $v }
        assert_equal [dict get $ad "token-status"] "cached"

        # Counter should be 11, not 12
        resp4_send $fd "[resp_cmd GET counter]"
        assert_equal [resp4_read_value $fd] "11"

        resp4_send $fd "[resp_cmd DEL counter]"
        resp4_read_value $fd
        close $fd
    }

    # ========== IDEMPOTENT.STATS ==========

    test {IDEMPOTENT.STATS returns valid statistics} {
        set stats [r idempotent.stats]
        assert {[dict exists $stats tokens_stored]}
        assert {[dict exists $stats cache_hits]}
        assert {[dict exists $stats cache_misses]}
        assert {[dict exists $stats tokens_expired]}
        assert {[dict exists $stats tokens_invalidated]}
        assert {[dict exists $stats exec_errors]}
        # After previous tests, we should have some hits and misses
        assert {[dict get $stats cache_misses] > 0}
    }

    # ========== IDEMPOTENT.INFO ==========

    test {IDEMPOTENT.INFO returns info for stored token} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        set token "tok-info-001"
        resp4_send $fd "[idem_header $token][resp_cmd IDEMPOTENT.EXEC SET infokey infoval]"
        resp4_read_value_with_attrs $fd

        close $fd

        # Now query info
        set info [r idempotent.info tok-info-001]
        assert {$info ne {}}
        assert_equal [dict get $info token] "tok-info-001"
        assert_equal [dict get $info namespace] "default"
        assert {[dict get $info cached_result_bytes] > 0}

        # Cleanup
        r DEL infokey
    }

    test {IDEMPOTENT.INFO returns nil for unknown token} {
        set result [r idempotent.info nonexistent-token]
        assert_equal $result {}
    }

    # ========== IDEMPOTENT.INVALIDATE ==========

    test {IDEMPOTENT.INVALIDATE removes a token allowing re-execution} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        set token "tok-inval-001"

        # Execute with token
        resp4_send $fd "[idem_header $token][resp_cmd IDEMPOTENT.EXEC SET invalkey val1]"
        resp4_read_value_with_attrs $fd

        close $fd

        # Invalidate the token
        set result [r idempotent.invalidate tok-inval-001]
        assert_equal $result "OK"

        # Re-execute with same token — should be a NEW execution
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        resp4_send $fd "[idem_header $token][resp_cmd IDEMPOTENT.EXEC SET invalkey val2]"
        set result [resp4_read_value_with_attrs $fd]
        set ad [dict create]
        foreach {k v} [lindex $result 0] { dict set ad $k $v }
        assert_equal [dict get $ad "token-status"] "new"

        # Key should now have val2
        resp4_send $fd "[resp_cmd GET invalkey]"
        assert_equal [resp4_read_value $fd] "val2"

        resp4_send $fd "[resp_cmd DEL invalkey]"
        resp4_read_value $fd
        close $fd
    }

    test {IDEMPOTENT.INVALIDATE returns nil for unknown token} {
        set result [r idempotent.invalidate nonexistent-token]
        assert_equal $result {}
    }

    # ========== IDEMPOTENT.FLUSH ==========

    test {IDEMPOTENT.FLUSH removes all tokens} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Store a few tokens
        resp4_send $fd "[idem_header tok-flush-001][resp_cmd IDEMPOTENT.EXEC SET fk1 v1]"
        resp4_read_value_with_attrs $fd
        resp4_send $fd "[idem_header tok-flush-002][resp_cmd IDEMPOTENT.EXEC SET fk2 v2]"
        resp4_read_value_with_attrs $fd

        close $fd

        # Flush
        set count [r idempotent.flush]
        assert {$count >= 2}

        # Tokens should be gone — re-execute is a new execution
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        resp4_send $fd "[idem_header tok-flush-001][resp_cmd IDEMPOTENT.EXEC SET fk1 newv1]"
        set result [resp4_read_value_with_attrs $fd]
        set ad [dict create]
        foreach {k v} [lindex $result 0] { dict set ad $k $v }
        assert_equal [dict get $ad "token-status"] "new"

        # Cleanup
        resp4_send $fd "[resp_cmd DEL fk1 fk2]"
        resp4_read_value $fd
        close $fd
    }

    # ========== Unload ==========

    test {IDEMPOTENT.FLUSH before unload to clean internal keys} {
        r idempotent.flush
        r DEL __idempotency:default __idempotency_ttl:default
    }

    test "Unload the module - idempotency" {
        assert_equal {OK} [r module unload idempotency]
    }
}
