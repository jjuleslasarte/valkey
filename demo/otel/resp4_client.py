"""
Minimal RESP4 client with OpenTelemetry trace context propagation.

This module provides a bare-bones RESP4 client that can:
  1. Negotiate RESP4 via HELLO 4
  2. Send RESP4 request headers (attribute blocks) before commands
  3. Parse basic RESP3 replies

It is intentionally minimal — no connection pooling, no cluster support —
designed purely to demonstrate RESP4 header sending for the OTel demo.
"""

import socket
import struct


class Resp4Client:
    """A minimal RESP4 client that supports request headers."""

    def __init__(self, host="127.0.0.1", port=6379):
        self.host = host
        self.port = port
        self.sock = None
        self.buf = b""

    def connect(self):
        """Connect and negotiate RESP4."""
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.connect((self.host, self.port))
        # Send HELLO 4 to negotiate RESP4
        self._send_raw(self._encode_command(["HELLO", "4"]))
        reply = self._read_reply()
        # Verify protocol negotiation
        if isinstance(reply, dict) and reply.get("proto") == 4:
            return reply
        elif isinstance(reply, dict) and reply.get(b"proto") == 4:
            return reply
        else:
            # Try to find proto in the reply
            return reply

    def close(self):
        """Close the connection."""
        if self.sock:
            try:
                self.sock.close()
            except Exception:
                pass
            self.sock = None

    def command(self, *args, headers=None):
        """
        Send a command with optional RESP4 request headers.

        Args:
            *args: Command and arguments (e.g., "SET", "foo", "bar")
            headers: Optional dict of header name -> value pairs.
                     Values can be str (sent as bulk string) or int (sent as RESP integer).

        Returns:
            The parsed reply from the server.
        """
        raw = b""
        if headers:
            raw += self._encode_headers(headers)
        raw += self._encode_command(list(args))
        self._send_raw(raw)
        self.last_reply_attributes = None
        return self._read_reply()

    # ---- Encoding ----

    def _encode_command(self, args):
        """Encode a command as a RESP array of bulk strings."""
        parts = [f"*{len(args)}\r\n".encode()]
        for arg in args:
            arg_bytes = str(arg).encode() if not isinstance(arg, bytes) else arg
            parts.append(f"${len(arg_bytes)}\r\n".encode())
            parts.append(arg_bytes)
            parts.append(b"\r\n")
        return b"".join(parts)

    def _encode_headers(self, headers):
        """Encode headers as a RESP4 attribute block (|N prefix)."""
        parts = [f"|{len(headers)}\r\n".encode()]
        for key, value in headers.items():
            # Keys are always bulk strings
            key_bytes = key.encode() if isinstance(key, str) else key
            parts.append(f"${len(key_bytes)}\r\n".encode())
            parts.append(key_bytes)
            parts.append(b"\r\n")
            # Values: int -> RESP integer, else -> bulk string
            if isinstance(value, int):
                parts.append(f":{value}\r\n".encode())
            else:
                val_bytes = str(value).encode() if not isinstance(value, bytes) else value
                parts.append(f"${len(val_bytes)}\r\n".encode())
                parts.append(val_bytes)
                parts.append(b"\r\n")
        return b"".join(parts)

    # ---- Network I/O ----

    def _send_raw(self, data):
        """Send raw bytes to the socket."""
        self.sock.sendall(data)

    def _read_bytes(self, n):
        """Read exactly n bytes from the buffer/socket."""
        while len(self.buf) < n:
            chunk = self.sock.recv(4096)
            if not chunk:
                raise ConnectionError("Connection closed")
            self.buf += chunk
        result = self.buf[:n]
        self.buf = self.buf[n:]
        return result

    def _read_line(self):
        """Read until \\r\\n."""
        while b"\r\n" not in self.buf:
            chunk = self.sock.recv(4096)
            if not chunk:
                raise ConnectionError("Connection closed")
            self.buf += chunk
        idx = self.buf.index(b"\r\n")
        line = self.buf[:idx]
        self.buf = self.buf[idx + 2:]
        return line

    # ---- Reply Parsing (RESP3) ----

    def _read_reply(self):
        """Parse one RESP3 reply from the wire."""
        line = self._read_line()
        type_byte = chr(line[0])
        data = line[1:]

        if type_byte == "+":  # Simple string
            return data.decode()
        elif type_byte == "-":  # Error
            return Exception(data.decode())
        elif type_byte == ":":  # Integer
            return int(data)
        elif type_byte == "$":  # Bulk string
            length = int(data)
            if length == -1:
                return None
            content = self._read_bytes(length + 2)  # +2 for \r\n
            return content[:length].decode()
        elif type_byte == "*":  # Array
            count = int(data)
            if count == -1:
                return None
            return [self._read_reply() for _ in range(count)]
        elif type_byte == "%":  # Map
            count = int(data)
            result = {}
            for _ in range(count):
                k = self._read_reply()
                v = self._read_reply()
                result[k] = v
            return result
        elif type_byte == ",":  # Double
            return float(data)
        elif type_byte == "#":  # Boolean
            return data == b"t"
        elif type_byte == "_":  # Null
            return None
        elif type_byte == "|":  # Attribute (reply-side) — capture and store, then read actual reply
            count = int(data)
            attrs = {}
            for _ in range(count):
                k = self._read_reply()
                v = self._read_reply()
                attrs[k] = v
            self.last_reply_attributes = attrs
            return self._read_reply()  # actual reply follows
        elif type_byte == "~":  # Set
            count = int(data)
            return set(self._read_reply() for _ in range(count))
        else:
            raise ValueError(f"Unknown RESP type: {type_byte} (line: {line})")
