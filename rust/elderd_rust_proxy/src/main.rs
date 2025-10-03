use byteorder::{BigEndian, ByteOrder};
use l0_lexer_client::Client;
use std::io::ErrorKind;
use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::{TcpListener, TcpStream},
    time::Instant,
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
        let mut hdr = [0u8; 16];
        match s.read_exact(&mut hdr).await {
            Ok(_) => {}
            Err(e) if e.kind() == ErrorKind::UnexpectedEof => return Ok(()),
            Err(e) => return Err(e.into()),
        }

        let msg_type = BigEndian::read_u32(&hdr[..4]);
        if msg_type != 1 {
            anyhow::bail!("unexpected message type {msg_type}");
        }
        let req_id = BigEndian::read_u64(&hdr[4..12]);
        let n = BigEndian::read_u32(&hdr[12..16]) as usize;

        let mut buf = vec![0u8; n];
        if n > 0 {
            s.read_exact(&mut buf).await?;
        }

        let t0 = Instant::now();
        let resp = match uds.tokenize(req_id, &buf).await {
            Ok(resp) => resp,
            Err(e) => {
                eprintln!("[proxy] tokenize error: {e}");
                let mut header = [0u8; 16];
                BigEndian::write_u32(&mut header[0..4], 2);
                BigEndian::write_u64(&mut header[4..12], req_id);
                BigEndian::write_u32(&mut header[12..16], 13);
                let mut body = [0u8; 13];
                BigEndian::write_u32(&mut body[0..4], 1);
                BigEndian::write_u32(&mut body[4..8], 0);
                BigEndian::write_u32(&mut body[8..12], 0);
                body[12] = 0;
                s.write_all(&header).await?;
                s.write_all(&body).await?;
                s.flush().await?;
                continue;
            }
        };

        let mut header = [0u8; 16];
        BigEndian::write_u32(&mut header[0..4], 2);
        BigEndian::write_u64(&mut header[4..12], req_id);
        BigEndian::write_u32(&mut header[12..16], 13);

        let mut body = [0u8; 13];
        BigEndian::write_u32(&mut body[0..4], resp.status);
        BigEndian::write_u32(&mut body[4..8], resp.tokens);
        BigEndian::write_u32(&mut body[8..12], resp.issues);
        body[12] = if resp.origin == 0 { 1 } else { resp.origin };

        s.write_all(&header).await?;
        s.write_all(&body).await?;
        s.flush().await?;

        eprintln!("[proxy] {n}B in {:.3} ms", t0.elapsed().as_secs_f64() * 1e3);
    }
}
