start_server {tags {"resp4"}} {
    test {HELLO 4 negotiation succeeds} {
        set reply [r HELLO 4]
        assert_equal [dict get $reply proto] 4
        assert_equal [dict get $reply server] valkey
    }

    test {HELLO 4 returns correct fields} {
        set reply [r HELLO 4]
        assert {[dict exists $reply server]}
        assert {[dict exists $reply version]}
        assert {[dict exists $reply proto]}
        assert {[dict exists $reply id]}
        assert {[dict exists $reply mode]}
        assert {[dict exists $reply role]}
        assert {[dict exists $reply modules]}
        assert_equal [dict get $reply proto] 4
    }

    test {HELLO 5 is rejected} {
        catch {r HELLO 5} err
        assert_match {*NOPROTO*} $err
    }

    test {HELLO 1 is rejected} {
        catch {r HELLO 1} err
        assert_match {*NOPROTO*} $err
    }

    test {HELLO 2 downgrades from RESP4} {
        r HELLO 4
        set reply [r HELLO 2]
        # RESP2 returns an array, not a map, so proto field is at index 5
        assert_equal [lindex $reply 5] 2
    }

    test {HELLO 3 works after HELLO 4} {
        r HELLO 4
        set reply [r HELLO 3]
        assert_equal [dict get $reply proto] 3
    }

    test {HELLO 4 then basic commands work} {
        r HELLO 4
        r SET foo bar
        assert_equal [r GET foo] bar
        r DEL foo
    }

    test {HELLO 4 then PING works} {
        r HELLO 4
        assert_equal [r PING] PONG
    }

    test {CLIENT INFO shows resp=4 after HELLO 4} {
        r HELLO 4
        set info [r CLIENT INFO]
        assert_match {*resp=4*} $info
    }

    # Phase 2: Request Header Parsing Tests
    # Use a raw socket for sending RESP4 headers since the Tcl client
    # library doesn't support RESP4 request-side attributes.

    proc resp4_raw_client {host port} {
        set fd [socket $host $port]
        fconfigure $fd -translation binary -buffering none -blocking 1
        return $fd
    }

    proc resp4_send {fd data} {
        puts -nonewline $fd $data
    }

    proc resp4_readline {fd} {
        # Read a line terminated by \r\n from a binary-mode channel.
        set line ""
        while {1} {
            set ch [read $fd 1]
            if {$ch eq ""} {
                error "resp4_readline: EOF"
            }
            if {$ch eq "\r"} {
                set next [read $fd 1]
                if {$next eq "\n"} {
                    return $line
                }
                append line $ch
                append line $next
            } else {
                append line $ch
            }
        }
    }

    # Read exactly N bytes from the channel.
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

    # Read a single RESP value from the fd, consuming all its bytes.
    proc resp4_read_value {fd} {
        set line [resp4_readline $fd]
        set type [string index $line 0]
        if {$type eq "+" || $type eq "-" || $type eq ":" || $type eq "_" || $type eq ","} {
            # Simple string, error, integer, null, double - single line
            return $line
        } elseif {$type eq "\$"} {
            # Bulk string: $N\r\n<data>\r\n
            set blen [string range $line 1 end]
            if {$blen >= 0} {
                # Read exactly blen bytes of data + \r\n
                resp4_readn $fd [expr {$blen + 2}]
            }
            return $line
        } elseif {$type eq "*" || $type eq "~"} {
            # Array or set: read N elements
            set n [string range $line 1 end]
            for {set i 0} {$i < $n} {incr i} {
                resp4_read_value $fd
            }
            return $line
        } elseif {$type eq "%" || $type eq "|"} {
            # Map or attribute: read 2*N elements (key-value pairs)
            set n [string range $line 1 end]
            for {set i 0} {$i < [expr {$n * 2}]} {incr i} {
                resp4_read_value $fd
            }
            return $line
        } elseif {$type eq ">"} {
            # Push: read N elements
            set n [string range $line 1 end]
            for {set i 0} {$i < $n} {incr i} {
                resp4_read_value $fd
            }
            return $line
        }
        return $line
    }

    # Read a bulk string's data (after the $N line has been read).
    # Returns the string data without the trailing \r\n.
    proc resp4_read_bulk_data {fd blen} {
        set data [resp4_readn $fd [expr {$blen + 2}]]
        return [string range $data 0 end-2]
    }

    proc resp4_negotiate {fd} {
        # Send HELLO 4 and fully drain the reply
        resp4_send $fd "*2\r\n\$5\r\nHELLO\r\n\$1\r\n4\r\n"
        resp4_read_value $fd
        # Verify with a PING roundtrip to ensure resp=4 took effect
        resp4_send $fd "*1\r\n\$4\r\nPING\r\n"
        set pong [resp4_readline $fd]
        if {$pong ne "+PONG"} {
            error "resp4_negotiate: expected +PONG after HELLO 4, got '$pong'"
        }
    }

    test {RESP4 headers + SET command executes correctly} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Send: |1 header then SET mykey myval
        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$7\r\nabc-123\r\n*3\r\n\$3\r\nSET\r\n\$5\r\nmykey\r\n\$5\r\nmyval\r\n"
        set reply [resp4_readline $fd]
        assert_equal $reply "+OK"

        # Verify the value
        resp4_send $fd "*2\r\n\$3\r\nGET\r\n\$5\r\nmykey\r\n"
        set lenline [resp4_readline $fd]
        set reply [resp4_readline $fd]
        assert_equal $reply "myval"

        # Cleanup
        resp4_send $fd "*2\r\n\$3\r\nDEL\r\n\$5\r\nmykey\r\n"
        resp4_readline $fd
        close $fd
    }

    test {RESP4 command without headers works after HELLO 4} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        resp4_send $fd "*1\r\n\$4\r\nPING\r\n"
        set reply [resp4_readline $fd]
        assert_equal $reply "+PONG"

        close $fd
    }

    test {RESP4 multiple header key-value pairs} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # |2 with trace-id=xyz and request-id=42, then PING
        resp4_send $fd "|2\r\n\$8\r\ntrace-id\r\n\$3\r\nxyz\r\n\$10\r\nrequest-id\r\n\$2\r\n42\r\n*1\r\n\$4\r\nPING\r\n"
        set reply [resp4_readline $fd]
        assert_equal $reply "+PONG"

        close $fd
    }

    test {RESP4 empty headers |0 followed by command} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        resp4_send $fd "|0\r\n*1\r\n\$4\r\nPING\r\n"
        set reply [resp4_readline $fd]
        assert_equal $reply "+PONG"

        close $fd
    }

    test {RESP4 headers then multiple sequential commands} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # First: headers + SET k1 v1
        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$5\r\nfirst\r\n*3\r\n\$3\r\nSET\r\n\$2\r\nk1\r\n\$2\r\nv1\r\n"
        assert_equal [resp4_readline $fd] "+OK"

        # Second: plain PING (no headers)
        resp4_send $fd "*1\r\n\$4\r\nPING\r\n"
        assert_equal [resp4_readline $fd] "+PONG"

        # Third: headers + SET k2 v2
        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$6\r\nsecond\r\n*3\r\n\$3\r\nSET\r\n\$2\r\nk2\r\n\$2\r\nv2\r\n"
        assert_equal [resp4_readline $fd] "+OK"

        # Cleanup
        resp4_send $fd "*2\r\n\$3\r\nDEL\r\n\$2\r\nk1\r\n"
        resp4_readline $fd
        resp4_send $fd "*2\r\n\$3\r\nDEL\r\n\$2\r\nk2\r\n"
        resp4_readline $fd
        close $fd
    }

    test {RESP2/3 client does not interpret | as headers} {
        r HELLO 2
        r SET testkey testval
        assert_equal [r GET testkey] testval
        r DEL testkey
    }

    # Phase 3: Header Storage Lifecycle Tests

    test {RESP4 headers are cleared between commands - no leakage} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # First command with headers
        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$5\r\nfirst\r\n*3\r\n\$3\r\nSET\r\n\$7\r\nhdrkey1\r\n\$4\r\nval1\r\n"
        assert_equal [resp4_readline $fd] "+OK"

        # Second command WITHOUT headers - should work fine (headers from first cmd cleared)
        resp4_send $fd "*3\r\n\$3\r\nSET\r\n\$7\r\nhdrkey2\r\n\$4\r\nval2\r\n"
        assert_equal [resp4_readline $fd] "+OK"

        # Verify both values are set correctly
        resp4_send $fd "*2\r\n\$3\r\nGET\r\n\$7\r\nhdrkey1\r\n"
        set lenline [resp4_readline $fd]
        assert_equal [resp4_read_bulk_data $fd [string range $lenline 1 end]] "val1"

        resp4_send $fd "*2\r\n\$3\r\nGET\r\n\$7\r\nhdrkey2\r\n"
        set lenline [resp4_readline $fd]
        assert_equal [resp4_read_bulk_data $fd [string range $lenline 1 end]] "val2"

        # Cleanup
        resp4_send $fd "*3\r\n\$3\r\nDEL\r\n\$7\r\nhdrkey1\r\n\$7\r\nhdrkey2\r\n"
        resp4_readline $fd
        close $fd
    }

    test {RESP4 headers do not persist across MULTI/EXEC boundary} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # MULTI
        resp4_send $fd "*1\r\n\$5\r\nMULTI\r\n"
        assert_equal [resp4_readline $fd] "+OK"

        # Command with headers inside MULTI
        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$8\r\ntx-trace\r\n*3\r\n\$3\r\nSET\r\n\$5\r\ntxkey\r\n\$5\r\ntxval\r\n"
        assert_equal [resp4_readline $fd] "+QUEUED"

        # EXEC
        resp4_send $fd "*1\r\n\$4\r\nEXEC\r\n"
        # EXEC returns an array with results
        resp4_read_value $fd

        # After EXEC, headers should be cleared. Verify the key was set.
        resp4_send $fd "*2\r\n\$3\r\nGET\r\n\$5\r\ntxkey\r\n"
        set lenline [resp4_readline $fd]
        assert_equal [resp4_read_bulk_data $fd [string range $lenline 1 end]] "txval"

        # Send another command without headers - should work fine
        resp4_send $fd "*1\r\n\$4\r\nPING\r\n"
        assert_equal [resp4_readline $fd] "+PONG"

        # Cleanup
        resp4_send $fd "*2\r\n\$3\r\nDEL\r\n\$5\r\ntxkey\r\n"
        resp4_readline $fd
        close $fd
    }

    test {RESP4 different headers on consecutive commands} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # First command with trace-id=aaa
        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$3\r\naaa\r\n*3\r\n\$3\r\nSET\r\n\$2\r\nha\r\n\$1\r\n1\r\n"
        assert_equal [resp4_readline $fd] "+OK"

        # Second command with trace-id=bbb (different value)
        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$3\r\nbbb\r\n*3\r\n\$3\r\nSET\r\n\$2\r\nhb\r\n\$1\r\n2\r\n"
        assert_equal [resp4_readline $fd] "+OK"

        # Third command with NO headers at all
        resp4_send $fd "*3\r\n\$3\r\nSET\r\n\$2\r\nhc\r\n\$1\r\n3\r\n"
        assert_equal [resp4_readline $fd] "+OK"

        # All three should have their values set correctly
        resp4_send $fd "*2\r\n\$3\r\nGET\r\n\$2\r\nha\r\n"
        set lenline [resp4_readline $fd]
        assert_equal [resp4_read_bulk_data $fd [string range $lenline 1 end]] "1"

        resp4_send $fd "*2\r\n\$3\r\nGET\r\n\$2\r\nhb\r\n"
        set lenline [resp4_readline $fd]
        assert_equal [resp4_read_bulk_data $fd [string range $lenline 1 end]] "2"

        resp4_send $fd "*2\r\n\$3\r\nGET\r\n\$2\r\nhc\r\n"
        set lenline [resp4_readline $fd]
        assert_equal [resp4_read_bulk_data $fd [string range $lenline 1 end]] "3"

        # Cleanup
        resp4_send $fd "*4\r\n\$3\r\nDEL\r\n\$2\r\nha\r\n\$2\r\nhb\r\n\$2\r\nhc\r\n"
        resp4_readline $fd
        close $fd
    }

    test {RESP4 header names are case-insensitive} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Send header with UPPER case name, then command
        resp4_send $fd "|1\r\n\$8\r\nTRACE-ID\r\n\$5\r\nupper\r\n*1\r\n\$4\r\nPING\r\n"
        assert_equal [resp4_readline $fd] "+PONG"

        # Send header with mixed case name, then command
        resp4_send $fd "|1\r\n\$8\r\nTrace-Id\r\n\$5\r\nmixed\r\n*1\r\n\$4\r\nPING\r\n"
        assert_equal [resp4_readline $fd] "+PONG"

        close $fd
    }

    test {RESP4 max 8 headers enforced} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Try to send |9 headers (exceeds max of 8) followed by enough
        # dummy data so the server can parse and reject the request.
        # We need to send 9 key-value bulk string pairs and a command.
        set data "|9\r\n"
        for {set i 0} {$i < 9} {incr i} {
            append data "\$1\r\nk\r\n\$1\r\nv\r\n"
        }
        append data "*1\r\n\$4\r\nPING\r\n"
        resp4_send $fd $data

        # The server should reject this with a header error and close
        # the connection. Read whatever response comes back.
        # Use a timeout to avoid hanging if the connection was just closed.
        fconfigure $fd -blocking 0
        after 500
        set reply [read $fd 1024]
        close $fd

        # The reply should contain an error about header limits
        assert_match {*ERR*} $reply
    }

    # Phase 5: Header Lifecycle, Config & Cleanup Tests

    test {RESP4 config resp4-max-headers is readable and writable} {
        r HELLO 2
        set orig [lindex [r CONFIG GET resp4-max-headers] 1]
        assert_equal $orig 8

        r CONFIG SET resp4-max-headers 4
        assert_equal [lindex [r CONFIG GET resp4-max-headers] 1] 4

        # Restore
        r CONFIG SET resp4-max-headers $orig
    }

    test {RESP4 config resp4-max-header-value-len is readable and writable} {
        set orig [lindex [r CONFIG GET resp4-max-header-value-len] 1]
        assert_equal $orig 4096

        r CONFIG SET resp4-max-header-value-len 512
        assert_equal [lindex [r CONFIG GET resp4-max-header-value-len] 1] 512

        # Restore
        r CONFIG SET resp4-max-header-value-len $orig
    }

    test {RESP4 config resp4-max-header-key-len is readable and writable} {
        set orig [lindex [r CONFIG GET resp4-max-header-key-len] 1]
        assert_equal $orig 64

        r CONFIG SET resp4-max-header-key-len 32
        assert_equal [lindex [r CONFIG GET resp4-max-header-key-len] 1] 32

        # Restore
        r CONFIG SET resp4-max-header-key-len $orig
    }

    test {RESP4 config resp4-unknown-header-policy defaults to ignore} {
        set val [lindex [r CONFIG GET resp4-unknown-header-policy] 1]
        assert_equal $val "ignore"
    }

    test {RESP4 config resp4-unknown-header-policy can be set to error} {
        r CONFIG SET resp4-unknown-header-policy error
        assert_equal [lindex [r CONFIG GET resp4-unknown-header-policy] 1] "error"
        # Restore
        r CONFIG SET resp4-unknown-header-policy ignore
    }

    test {RESP4 dynamic max-headers limit enforcement} {
        # Lower the limit to 2
        r CONFIG SET resp4-max-headers 2

        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Sending |3 should exceed the limit of 2
        set data "|3\r\n"
        for {set i 0} {$i < 3} {incr i} {
            append data "\$1\r\nk\r\n\$1\r\nv\r\n"
        }
        append data "*1\r\n\$4\r\nPING\r\n"
        resp4_send $fd $data

        fconfigure $fd -blocking 0
        after 500
        set reply [read $fd 1024]
        close $fd
        assert_match {*ERR*} $reply

        # Restore
        r CONFIG SET resp4-max-headers 8
    }

    test {RESP4 dynamic max-headers allows within new limit} {
        # Set limit to 2
        r CONFIG SET resp4-max-headers 2

        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Sending |2 headers should work fine
        resp4_send $fd "|2\r\n\$1\r\na\r\n\$1\r\n1\r\n\$1\r\nb\r\n\$1\r\n2\r\n*1\r\n\$4\r\nPING\r\n"
        set reply [resp4_readline $fd]
        assert_equal $reply "+PONG"

        close $fd

        # Restore
        r CONFIG SET resp4-max-headers 8
    }

    test {RESP4 dynamic max-header-value-len enforcement} {
        # Lower the value limit to 64
        r CONFIG SET resp4-max-header-value-len 64

        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Send a header value that's 65 bytes (exceeds 64 limit)
        set bigval [string repeat "x" 65]
        set vlen [string length $bigval]
        resp4_send $fd "|1\r\n\$3\r\nfoo\r\n\$$vlen\r\n$bigval\r\n*1\r\n\$4\r\nPING\r\n"

        fconfigure $fd -blocking 0
        after 500
        set reply [read $fd 1024]
        close $fd
        assert_match {*ERR*} $reply

        # Restore
        r CONFIG SET resp4-max-header-value-len 4096
    }

    test {RESP4 headers cleared after CLIENT RESET} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Send headers + command
        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$4\r\ntest\r\n*3\r\n\$3\r\nSET\r\n\$8\r\nresetkey\r\n\$8\r\nresetval\r\n"
        assert_equal [resp4_readline $fd] "+OK"

        # Now send RESET command (which calls clearClientConnectionState)
        resp4_send $fd "*1\r\n\$5\r\nRESET\r\n"
        set reply [resp4_readline $fd]
        assert_match {*RESET*} $reply

        # After RESET, resp is downgraded to 2, but connection works
        # Send a plain command to verify the connection is healthy
        resp4_send $fd "*1\r\n\$4\r\nPING\r\n"
        set reply [resp4_readline $fd]
        assert_equal $reply "+PONG"

        # Cleanup
        resp4_send $fd "*2\r\n\$3\r\nDEL\r\n\$8\r\nresetkey\r\n"
        resp4_readline $fd
        close $fd
    }

    test {RESP4 all config entries appear in CONFIG GET resp4-*} {
        set configs [r CONFIG GET "resp4-*"]
        # Should have at least 4 config entries (8 items: key value pairs)
        assert {[llength $configs] >= 8}

        # Verify all expected configs are present
        set config_dict [dict create]
        foreach {k v} $configs {
            dict set config_dict $k $v
        }
        assert {[dict exists $config_dict "resp4-max-headers"]}
        assert {[dict exists $config_dict "resp4-max-header-key-len"]}
        assert {[dict exists $config_dict "resp4-max-header-value-len"]}
        assert {[dict exists $config_dict "resp4-unknown-header-policy"]}
    }
}
