#!/usr/bin/env python3
import socket
import struct
import sys
import time

HOST = '127.0.0.1'
PORT = 9123


def be32(x: int) -> bytes:
    return struct.pack('>I', x)


def be64(x: int) -> bytes:
    return struct.pack('>Q', x)


def recv_exact(sock: socket.socket, length: int) -> bytes:
    data = bytearray()
    while len(data) < length:
        chunk = sock.recv(length - len(data))
        if not chunk:
            raise RuntimeError('short read')
        data.extend(chunk)
    return bytes(data)


def request(sock: socket.socket, payload: bytes, typ: int = 1, req_id: int = 1) -> bytes:
    hdr = be32(typ) + be64(req_id) + be32(len(payload))
    sock.sendall(hdr + payload)

    rhdr = recv_exact(sock, 16)
    r_type, r_req, r_len = struct.unpack('>I Q I', rhdr)
    if r_type != 2 or r_req != req_id:
        raise RuntimeError(f'unexpected response header type={r_type} req={r_req}')
    return recv_exact(sock, r_len)

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
        body = request(s, b" ", typ=1, req_id=i + 1)
        status, n_tokens, issues_len, origin = parse_status_payload(body)
        if status != 0:
            print(f"[proxy-smoke] request {i+1} returned status={status}, tokens={n_tokens}, issues_len={issues_len}, origin={origin}", file=sys.stderr)
            raise SystemExit(f'status nonzero: {status}')
        if origin not in (1, 2):
            raise SystemExit(f'bad origin: {origin}')
    print('[proxy-smoke] OK (3 requests, status=0)')

if __name__ == '__main__':
    main()
