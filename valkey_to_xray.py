#!/usr/bin/env python3
"""
Valkey SLOWLOG to AWS X-Ray Converter

Transforms Valkey SLOWLOG GET output into AWS X-Ray trace segments.
Each slow command becomes a separate X-Ray trace with timing and metadata.

Usage:
    python valkey_to_xray.py <file_path_or_s3_uri>

Examples:
    # Local file
    python valkey_to_xray.py slowlog.txt
    
    # S3 location
    python valkey_to_xray.py s3://my-bucket/slowlog.txt
    
    # Send to X-Ray
    python valkey_to_xray.py slowlog.txt | python -c "
    import sys, json, boto3
    client = boto3.client('xray')
    for seg in json.load(sys.stdin):
        client.put_trace_segments(TraceSegmentDocuments=[json.dumps(seg)])
    "

Requirements:
    pip install boto3

Input Format:
    Plain text output from Valkey SLOWLOG GET command
    
Output Format:
    JSON array of X-Ray trace segments ready for PutTraceSegments API
"""
import json
import sys
import time
from urllib.parse import urlparse
import boto3


def parse_slowlog(content):
    """
    Parse Valkey SLOWLOG GET plain text output.
    
    Args:
        content: String containing SLOWLOG output
        
    Returns:
        List of dictionaries with keys: id, timestamp, duration, command, client, client_name
        
    Example input:
        1) 1) (integer) 22
           2) (integer) 1773232466
           3) (integer) 14
           4) 1) "SET"
              2) "foo"
              3) "bar"
           5) "127.0.0.1:54515"
           6) "my-app"
    """
    lines = [l.rstrip() for l in content.split('\n')]
    entries = []
    i = 0
    
    while i < len(lines):
        # Look for entry start (any number followed by parenthesis at start of line)
        if lines[i] and lines[i][0].isdigit() and ')' in lines[i] and not lines[i].startswith('   '):
            entry = {}
            i += 1
            
            # Parse field 1: ID
            if i < len(lines) and lines[i].strip().startswith('1)'):
                val = lines[i].split(')', 1)[1].replace('(integer)', '').strip()
                if val:
                    entry['id'] = val
                i += 1
            
            # Parse field 2: timestamp
            if i < len(lines) and lines[i].strip().startswith('2)'):
                val = lines[i].split(')', 1)[1].replace('(integer)', '').strip()
                entry['timestamp'] = int(val)
                i += 1
            
            # Parse field 3: duration
            if i < len(lines) and lines[i].strip().startswith('3)'):
                val = lines[i].split(')', 1)[1].replace('(integer)', '').strip()
                entry['duration'] = int(val)
                i += 1
            
            # Parse field 4: command array
            if i < len(lines) and lines[i].strip().startswith('4)'):
                i += 1
                cmd_parts = []
                while i < len(lines) and lines[i].strip():
                    line = lines[i].strip()
                    if line.startswith('5)'):
                        break
                    if '"' in line:
                        cmd_parts.append(line.split('"')[1])
                    i += 1
                entry['command'] = ' '.join(cmd_parts)
            
            # Parse field 5: client
            if i < len(lines) and lines[i].strip().startswith('5)'):
                entry['client'] = lines[i].split('"')[1] if '"' in lines[i] else ''
                i += 1
            
            # Parse field 6: client name
            if i < len(lines) and lines[i].strip().startswith('6)'):
                entry['client_name'] = lines[i].split('"')[1] if '"' in lines[i] else ''
                i += 1
            
            entries.append(entry)
        else:
            i += 1
    
    return entries


def generate_trace_id():
    """
    Generate X-Ray trace ID.
    
    Format: 1-{hex_timestamp}-{24_hex_chars}
    Example: 1-69b19180-0000000000064cc1ba6df38e
    """
    hex_time = hex(int(time.time()))[2:]
    hex_random = hex(int(time.time() * 1000000) % 0xFFFFFFFFFFFFFFFFFFFFFFFF)[2:].zfill(24)
    return f"1-{hex_time}-{hex_random}"


def generate_segment_id():
    """
    Generate X-Ray segment ID.
    
    Format: 16 hex characters
    Example: 00064cc1ba6df38e
    """
    return hex(int(time.time() * 1000000) % 0xFFFFFFFFFFFFFFFF)[2:].zfill(16)


def slowlog_to_xray(entry):
    """
    Convert slowlog entry to X-Ray trace segment.
    
    Args:
        entry: Dictionary with slowlog fields (id, timestamp, duration, command, client, client_name)
        
    Returns:
        Dictionary representing X-Ray trace segment with:
        - trace_id: Unique trace identifier
        - id: Segment identifier
        - name: Service name (valkey-slowlog)
        - start_time/end_time: Unix timestamps
        - annotations: Command and duration for filtering
        - metadata: Additional slowlog details
    """
    start_time = entry['timestamp']
    duration_seconds = entry['duration'] / 1000000.0
    
    segment = {
        "trace_id": generate_trace_id(),
        "id": generate_segment_id(),
        "name": "valkey-slowlog",
        "start_time": start_time,
        "end_time": start_time + duration_seconds,
        "annotations": {
            "command": entry['command'],
            "duration_us": entry['duration']
        },
        "metadata": {
            "valkey": {
                "slowlog_id": entry.get('id', ''),
                "client": entry.get('client', ''),
                "client_name": entry.get('client_name', '')
            }
        }
    }
    
    return segment


def read_from_s3(s3_path):
    """
    Read content from S3.
    
    Args:
        s3_path: S3 URI (s3://bucket/key)
        
    Returns:
        String content of the S3 object
    """
    parsed = urlparse(s3_path)
    bucket = parsed.netloc
    key = parsed.path.lstrip('/')
    
    s3 = boto3.client('s3')
    response = s3.get_object(Bucket=bucket, Key=key)
    return response['Body'].read().decode('utf-8')


def read_input(source):
    """
    Read from file or S3.
    
    Args:
        source: File path or S3 URI (s3://bucket/key)
        
    Returns:
        String content from the source
    """
    if source.startswith('s3://'):
        return read_from_s3(source)
    else:
        with open(source, 'r') as f:
            return f.read()


def main():
    """
    Main entry point.
    
    Reads Valkey SLOWLOG from file or S3, converts to X-Ray format,
    and outputs JSON to stdout.
    """
    if len(sys.argv) != 2:
        print("Usage: python valkey_to_xray.py <file_path_or_s3_uri>", file=sys.stderr)
        print("\nExamples:", file=sys.stderr)
        print("  python valkey_to_xray.py slowlog.txt", file=sys.stderr)
        print("  python valkey_to_xray.py s3://bucket/slowlog.txt", file=sys.stderr)
        sys.exit(1)
    
    source = sys.argv[1]
    
    if source in ['--help', '-h']:
        print(__doc__)
        sys.exit(0)
    content = read_input(source)
    entries = parse_slowlog(content)
    
    xray_traces = [slowlog_to_xray(entry) for entry in entries]
    
    print(json.dumps(xray_traces, indent=2))


if __name__ == '__main__':
    main()
