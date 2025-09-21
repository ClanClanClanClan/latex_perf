use tokio::{net::{TcpListener, TcpStream}, io::{AsyncReadExt, AsyncWriteExt}, time::Instant};
use l0_lexer_client::Client;

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    let uds = Client::new_uds("/tmp/l0_lex_svc.sock");
    let l = TcpListener::bind("127.0.0.1:9123").await?;
    eprintln!("[proxy] listening on 127.0.0.1:9123; UDS=/tmp/l0_lex_svc.sock");

    loop {
        let (mut sock, _) = l.accept().await?;
        let uds = uds.clone();
        tokio::spawn(async move {
            if let Err(e) = handle(&uds, &mut sock).await {
                eprintln!("[proxy] error: {e}");
            }
        });
    }
}

async fn handle(uds: &Client, s: &mut TcpStream) -> anyhow::Result<()> {
    // Protocol here is illustrative: read 4-byte len + payload, write 4 + 20 bytes back.
    let mut len_buf = [0u8; 4];
    s.read_exact(&mut len_buf).await?;
    let n = u32::from_be_bytes(len_buf) as usize;
    let mut buf = vec![0u8; n];
    s.read_exact(&mut buf).await?;

    let t0 = Instant::now();
    let resp = uds.tokenize(rand::random::<u64>(), &buf).await?;

    let mut out = Vec::with_capacity(24);
    out.extend_from_slice(&u32::to_be_bytes(20));
    out.extend_from_slice(&u32::to_be_bytes(resp.status));
    out.extend_from_slice(&u32::to_be_bytes(resp.tokens));
    out.extend_from_slice(&u32::to_be_bytes(resp.issues));
    out.extend_from_slice(&u32::to_be_bytes(resp.alloc_mb_x10));
    out.extend_from_slice(&u32::to_be_bytes(resp.majors));
    s.write_all(&out).await?;
    s.flush().await?;

    eprintln!("[proxy] {n}B in {:.3} ms", t0.elapsed().as_secs_f64() * 1e3);
    Ok(())
}