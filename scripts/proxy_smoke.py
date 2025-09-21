#!/usr/bin/env python3
import socket, struct, sys, time

HOST = '127.0.0.1'
PORT = 9123

def be32(x):
    return struct.pack('>I', x)

def be64(x):
    return struct.pack('>Q', x)

def request(sock, payload: bytes, typ: int = 1, req_id: int = 1):
    hdr = be32(typ) + be64(req_id) + be32(len(payload))
    sock.sendall(hdr + payload)
    rh = sock.recv(16)
    if len(rh) != 16:
        raise RuntimeError('short response header')
    r_type, r_req, r_len = struct.unpack('>I Q I', rh)
    body = b''
    while len(body) < r_len:
        chunk = sock.recv(r_len - len(body))
        if not chunk:
            break
        body += chunk
    if len(body) != r_len:
        raise RuntimeError('short body')
    return r_type, r_req, body

def parse_status_payload(body: bytes):
    if len(body) == 13:
        status, n_tokens, issues_len = struct.unpack('>III', body[:12])
        origin = body[12]
        return status, n_tokens, issues_len, origin
    elif len(body) == 20:
        # Backward compatibility if a 20-byte variant appears (all u32)
        status, n_tokens, issues_len, origin, _pad = struct.unpack('>IIIII', body)
        return status, n_tokens, issues_len, origin & 0xFF
    else:
        raise RuntimeError(f'unexpected payload length: {len(body)}')

def main():
    s = socket.create_connection((HOST, PORT), timeout=2.0)
    for i in range(3):
        typ, rid, body = request(s, b" ", typ=1, req_id=i+1)
        status, n_tokens, issues_len, origin = parse_status_payload(body)
        if status != 0:
            raise SystemExit(f'status nonzero: {status}')
        if origin not in (1, 2):
            raise SystemExit(f'bad origin: {origin}')
    print('[proxy-smoke] OK (3 requests, status=0)')

if __name__ == '__main__':
    main()
