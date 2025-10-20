use l0_lexer_client::Client;
use rand::random;
use std::{io::ErrorKind, time::Instant};
use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::{TcpListener, TcpStream},
};

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
    loop {
        let mut len_buf = [0u8; 4];
        match s.read_exact(&mut len_buf).await {
            Ok(_) => {}
            Err(e) if matches!(e.kind(), ErrorKind::UnexpectedEof | ErrorKind::ConnectionReset) => {
                break;
            }
            Err(e) => return Err(e.into()),
        }

        let n = u32::from_be_bytes(len_buf) as usize;
        if n == 0 || n > 2 * 1024 * 1024 {
            let mut out = Vec::with_capacity(24);
            out.extend_from_slice(&u32::to_be_bytes(20));
            out.extend_from_slice(&u32::to_be_bytes(1));
            out.extend_from_slice(&u32::to_be_bytes(0));
            out.extend_from_slice(&u32::to_be_bytes(0));
            out.extend_from_slice(&u32::to_be_bytes(0));
            out.extend_from_slice(&u32::to_be_bytes(0));
            s.write_all(&out).await?;
            s.flush().await?;
            eprintln!("[proxy] reject size n={n}");
            continue;
        }

        let mut buf = vec![0u8; n];
        s.read_exact(&mut buf).await?;

        let request_id = random::<u64>();
        let t0 = Instant::now();
        let resp = uds.tokenize(request_id, &buf).await;

        match resp {
            Ok(resp) => {
                let mut out = Vec::with_capacity(24);
                out.extend_from_slice(&u32::to_be_bytes(20));
                out.extend_from_slice(&u32::to_be_bytes(resp.status));
                out.extend_from_slice(&u32::to_be_bytes(resp.tokens));
                out.extend_from_slice(&u32::to_be_bytes(resp.issues));
                out.extend_from_slice(&u32::to_be_bytes(resp.alloc_mb_x10));
                out.extend_from_slice(&u32::to_be_bytes(resp.majors));
                s.write_all(&out).await?;
                s.flush().await?;
                eprintln!(
                    "[proxy] ok {}B in {:.3} ms status={} tokens={}",
                    n,
                    t0.elapsed().as_secs_f64() * 1e3,
                    resp.status,
                    resp.tokens
                );
            }
            Err(e) => {
                let mut out = Vec::with_capacity(24);
                out.extend_from_slice(&u32::to_be_bytes(20));
                out.extend_from_slice(&u32::to_be_bytes(1));
                out.extend_from_slice(&u32::to_be_bytes(0));
                out.extend_from_slice(&u32::to_be_bytes(0));
                out.extend_from_slice(&u32::to_be_bytes(0));
                out.extend_from_slice(&u32::to_be_bytes(0));
                s.write_all(&out).await?;
                s.flush().await?;
                eprintln!("[proxy] uds error for {}B: {}", n, e);
            }
        }
    }

    Ok(())
}
