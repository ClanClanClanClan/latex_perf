# Rust/Tokio Façade for L0 Lexer Service

This directory contains the Rust/Tokio façade implementation to provide v25_R1 spec compliance.

## Components

- **l0_lexer_client**: Tokio-based client library for Unix Domain Socket communication
- **elderd_rust_proxy**: TCP proxy server that bridges TCP (127.0.0.1:9123) to UDS (/tmp/l0_lex_svc.sock)

## Installation

1. Install Rust (if not already installed):
```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

2. Build the proxy:
```bash
cargo build --release
```

## Usage

1. Start the OCaml service (creates Unix socket at /tmp/l0_lex_svc.sock):
```bash
make service-run
```

2. Start the Tokio proxy (listens on TCP 127.0.0.1:9123):
```bash
./target/release/elderd_rust_proxy
```

3. Run verification:
```bash
make verify_r1
```

## Protocol

The proxy implements a 16-byte big-endian header protocol:
- Request: type(4) | req_id(8) | len(4) + payload
- Response: type(4) | req_id(8) | len(4) + 13-byte status payload

Status payload (13 bytes):
- status (u32 BE), n_tokens (u32 BE), issues_len (u32 BE), origin (u8)
- origin: 1=primary, 2=hedge, else unknown

This provides the Tokio/Rust interface expected by v25_R1 specifications while maintaining the proven OCaml worker implementation.
