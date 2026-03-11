# Test RESP4 request header Module API via the helloheaders module.

set testmodule [file normalize tests/modules/helloheaders.so]

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
            read $fd 1 ;# consume \n
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
        default {
            return "${type}${rest}"
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

start_server {tags {"modules"}} {
    r module load $testmodule

    test {HEADERS.TRACEID returns nil without headers (RESP2/3)} {
        set result [r headers.traceid]
        assert_equal $result {}
    }

    test {HEADERS.EXISTS returns 0 without headers (RESP2/3)} {
        set result [r headers.exists trace-id]
        assert_equal $result 0
    }

    test {HEADERS.TRACEID returns trace-id value with RESP4 headers} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Send |1 header (trace-id=hello-world) + HEADERS.TRACEID
        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$11\r\nhello-world\r\n*1\r\n\$15\r\nHEADERS.TRACEID\r\n"
        set reply [resp4_read_value $fd]
        assert_equal $reply "hello-world"
        close $fd
    }

    test {HEADERS.TRACEID returns nil when no trace-id header sent} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Send |1 header with a DIFFERENT header name, then HEADERS.TRACEID
        resp4_send $fd "|1\r\n\$10\r\nrequest-id\r\n\$3\r\n999\r\n*1\r\n\$15\r\nHEADERS.TRACEID\r\n"
        set reply [resp4_read_value $fd]
        assert_equal $reply "(nil)"
        close $fd
    }

    test {HEADERS.EXISTS returns 1 when header is present} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$3\r\nfoo\r\n*2\r\n\$14\r\nHEADERS.EXISTS\r\n\$8\r\ntrace-id\r\n"
        set reply [resp4_read_value $fd]
        assert_equal $reply "1"
        close $fd
    }

    test {HEADERS.EXISTS returns 0 when header not present} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # No headers, just the command
        resp4_send $fd "*2\r\n\$14\r\nHEADERS.EXISTS\r\n\$8\r\ntrace-id\r\n"
        set reply [resp4_read_value $fd]
        assert_equal $reply "0"
        close $fd
    }

    test {HEADERS.ECHO returns all headers} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Send 2 headers + HEADERS.ECHO
        resp4_send $fd "|2\r\n\$8\r\ntrace-id\r\n\$5\r\nabc12\r\n\$6\r\ncustom\r\n\$3\r\nval\r\n*1\r\n\$12\r\nHEADERS.ECHO\r\n"
        set reply [resp4_read_value $fd]
        # reply is a flat array of key value key value ...
        assert {[llength $reply] == 4}
        # Check both headers are present (order may vary)
        set found_trace 0
        set found_custom 0
        for {set i 0} {$i < [llength $reply]} {incr i 2} {
            set k [lindex $reply $i]
            set v [lindex $reply [expr {$i+1}]]
            if {$k eq "trace-id" && $v eq "abc12"} { set found_trace 1 }
            if {$k eq "custom" && $v eq "val"} { set found_custom 1 }
        }
        assert_equal $found_trace 1
        assert_equal $found_custom 1
        close $fd
    }

    test {HEADERS.ECHO returns empty when no headers} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        resp4_send $fd "*1\r\n\$12\r\nHEADERS.ECHO\r\n"
        set reply [resp4_read_value $fd]
        # Empty map or empty array
        assert {[llength $reply] == 0}
        close $fd
    }

    test {HEADERS.GETLL returns integer header value} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        resp4_send $fd "|1\r\n\$9\r\ntimestamp\r\n\$13\r\n1698776172000\r\n*2\r\n\$13\r\nHEADERS.GETLL\r\n\$9\r\ntimestamp\r\n"
        set reply [resp4_read_value $fd]
        assert_equal $reply "1698776172000"
        close $fd
    }

    test {HEADERS.GETLL returns nil for non-existent header} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        resp4_send $fd "*2\r\n\$13\r\nHEADERS.GETLL\r\n\$9\r\ntimestamp\r\n"
        set reply [resp4_read_value $fd]
        assert_equal $reply "(nil)"
        close $fd
    }

    test {Headers are cleared between commands} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # First command with headers
        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$5\r\nfirst\r\n*1\r\n\$15\r\nHEADERS.TRACEID\r\n"
        set reply1 [resp4_read_value $fd]
        assert_equal $reply1 "first"

        # Second command WITHOUT headers - trace-id should be gone
        resp4_send $fd "*1\r\n\$15\r\nHEADERS.TRACEID\r\n"
        set reply2 [resp4_read_value $fd]
        assert_equal $reply2 "(nil)"
        close $fd
    }

    test {Header names are case-insensitive in module API} {
        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Send with UPPER case TRACE-ID, query with lower case
        resp4_send $fd "|1\r\n\$8\r\nTRACE-ID\r\n\$5\r\nupper\r\n*1\r\n\$15\r\nHEADERS.TRACEID\r\n"
        set reply [resp4_read_value $fd]
        assert_equal $reply "upper"
        close $fd
    }

    # --- Commandlog (slowlog) metadata integration tests ---

    test {Commandlog entry includes trace-id metadata when header sent} {
        # Set slowlog threshold to 0 to capture all commands
        r CONFIG SET commandlog-execution-slower-than 0

        # Reset slowlog
        r SLOWLOG RESET

        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # Send a SET command with trace-id header
        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$10\r\nmy-trace-1\r\n*3\r\n\$3\r\nSET\r\n\$7\r\nslowkey\r\n\$7\r\nslowval\r\n"
        set reply [resp4_read_value $fd]
        assert_equal $reply "OK"
        close $fd

        # Get slowlog entries - look for the SET command
        set entries [r SLOWLOG GET 10]
        set found 0
        foreach entry $entries {
            # Each entry is: id, timestamp, duration, [args...], peer, cname [, metadata]
            set args [lindex $entry 3]
            if {[lindex $args 0] eq "SET" && [lindex $args 1] eq "slowkey"} {
                # Entry should have 7 elements (with metadata)
                assert {[llength $entry] == 7}
                # The 7th element is the metadata array
                set metadata [lindex $entry 6]
                # metadata is [key, value, ...] flat array
                assert {[llength $metadata] == 2}
                assert_equal [lindex $metadata 0] "trace-id"
                assert_equal [lindex $metadata 1] "my-trace-1"
                set found 1
                break
            }
        }
        assert_equal $found 1

        # Cleanup
        r DEL slowkey
        r CONFIG SET commandlog-execution-slower-than 10000
    }

    test {Commandlog entry has no metadata when no header sent} {
        r CONFIG SET commandlog-execution-slower-than 0
        r SLOWLOG RESET

        # Normal command without headers
        r SET noheadkey noheadval

        set entries [r SLOWLOG GET 10]
        set found 0
        foreach entry $entries {
            set args [lindex $entry 3]
            if {[lindex $args 0] eq "SET" && [lindex $args 1] eq "noheadkey"} {
                # Entry should have 6 elements (no metadata)
                assert {[llength $entry] == 6}
                set found 1
                break
            }
        }
        assert_equal $found 1

        r DEL noheadkey
        r CONFIG SET commandlog-execution-slower-than 10000
    }

    test {Commandlog metadata is per-command, not sticky} {
        r CONFIG SET commandlog-execution-slower-than 0
        r SLOWLOG RESET

        set fd [resp4_raw_client [srv host] [srv port]]
        resp4_negotiate $fd

        # First command with trace-id
        resp4_send $fd "|1\r\n\$8\r\ntrace-id\r\n\$7\r\nfirst-t\r\n*3\r\n\$3\r\nSET\r\n\$4\r\nsk-a\r\n\$1\r\n1\r\n"
        resp4_read_value $fd

        # Second command WITHOUT trace-id
        resp4_send $fd "*3\r\n\$3\r\nSET\r\n\$4\r\nsk-b\r\n\$1\r\n2\r\n"
        resp4_read_value $fd

        close $fd

        set entries [r SLOWLOG GET 20]
        set found_a 0
        set found_b 0
        foreach entry $entries {
            set args [lindex $entry 3]
            if {[lindex $args 0] eq "SET" && [lindex $args 1] eq "sk-a"} {
                # Should have metadata (7 elements)
                assert {[llength $entry] == 7}
                set metadata [lindex $entry 6]
                assert_equal [lindex $metadata 0] "trace-id"
                assert_equal [lindex $metadata 1] "first-t"
                set found_a 1
            }
            if {[lindex $args 0] eq "SET" && [lindex $args 1] eq "sk-b"} {
                # Should NOT have metadata (6 elements)
                assert {[llength $entry] == 6}
                set found_b 1
            }
        }
        assert_equal $found_a 1
        assert_equal $found_b 1

        r DEL sk-a sk-b
        r CONFIG SET commandlog-execution-slower-than 10000
    }

    test "Unload the module - helloheaders" {
        assert_equal {OK} [r module unload helloheaders]
    }
}
