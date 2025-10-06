#!/usr/bin/env python3
import socket
import struct
import sys
HOST = '127.0.0.1'
PORT = 9123


def recv_exact(sock: socket.socket, length: int) -> bytes:
    data = bytearray()
    while len(data) < length:
        chunk = sock.recv(length - len(data))
        if not chunk:
            raise RuntimeError('short read')
        data.extend(chunk)
    return bytes(data)


def request(sock: socket.socket, payload: bytes) -> tuple[int, int, int, int, int]:
    sock.sendall(struct.pack('>I', len(payload)))
    sock.sendall(payload)

    resp_len_bytes = recv_exact(sock, 4)
    (resp_len,) = struct.unpack('>I', resp_len_bytes)
    body = recv_exact(sock, resp_len)
    if resp_len != 20:
        raise RuntimeError(f'unexpected response length: {resp_len}')
    return struct.unpack('>IIIII', body)

def main():
    doc = b" " + b"test"
    payload = struct.pack('>I', len(doc)) + doc
    try:
        with socket.create_connection((HOST, PORT), timeout=10.0) as s:
            s.settimeout(10.0)
            for i in range(3):
                status, tokens, issues, alloc, majors = request(s, payload)
                if status != 0:
                    print(
                        f"[proxy-smoke] ERROR request={i+1} status={status} tokens={tokens} issues={issues} alloc_x10={alloc} majors={majors}",
                        file=sys.stderr,
                    )
                    raise SystemExit(status or 1)
                print(f"[proxy-smoke] request {i+1} status={status} tokens={tokens} issues={issues}")
    except OSError as exc:
        print(f"[proxy-smoke] socket error: {exc}", file=sys.stderr)
        raise SystemExit(1)

    print('[proxy-smoke] OK (3 requests, status=0)')

if __name__ == '__main__':
    main()
