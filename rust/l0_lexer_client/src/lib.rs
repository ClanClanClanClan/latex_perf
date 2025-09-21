use tokio::{io::{AsyncReadExt, AsyncWriteExt}, net::UnixStream, time::{timeout, Duration}};
use byteorder::{BigEndian, ByteOrder};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum L0Error {
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
    #[error("timeout")]
    Timeout,
    #[error("protocol: {0}")]
    Protocol(&'static str),
}

#[derive(Clone, Debug)]
pub struct L0Response {
    pub status: u32,
    pub tokens: u32,
    pub issues: u32,
    pub alloc_mb_x10: u32,
    pub majors: u32,
    pub origin: u8, // optional: 0=primary,1=hedge-winner
}

#[derive(Clone)]
pub struct Client {
    path: String,
}

impl Client {
    pub fn new_uds(path: impl Into<String>) -> Self {
        Self { path: path.into() }
    }

    pub async fn tokenize(&self, req_id: u64, bytes: &[u8]) -> Result<L0Response, L0Error> {
        let mut s = UnixStream::connect(&self.path).await?;

        // --- write header (type=1 request)
        let mut hdr = [0u8; 16];
        BigEndian::write_u32(&mut hdr[0..4], 1);
        BigEndian::write_u64(&mut hdr[4..12], req_id);
        BigEndian::write_u32(&mut hdr[12..16], bytes.len() as u32);
        s.write_all(&hdr).await?;
        s.write_all(bytes).await?;
        s.flush().await?;

        // --- read response header
        let mut rhdr = [0u8; 16];
        timeout(Duration::from_secs(5), s.read_exact(&mut rhdr))
            .await
            .map_err(|_| L0Error::Timeout)??;

        let rty = BigEndian::read_u32(&rhdr[0..4]);
        if rty != 2 {
            return Err(L0Error::Protocol("unexpected message type"));
        }
        let _rid = BigEndian::read_u64(&rhdr[4..12]); // optional check against req_id
        let rlen = BigEndian::read_u32(&rhdr[12..16]);
        if rlen != 20 && rlen != 21 {
            return Err(L0Error::Protocol("bad resp len"));
        }

        let mut body = vec![0u8; rlen as usize];
        s.read_exact(&mut body).await?;

        let status = BigEndian::read_u32(&body[0..4]);
        let tokens = BigEndian::read_u32(&body[4..8]);
        let issues = BigEndian::read_u32(&body[8..12]);
        let alloc_mb_x10 = BigEndian::read_u32(&body[12..16]);
        let majors = BigEndian::read_u32(&body[16..20]);
        let origin = if rlen == 21 { body[20] } else { 0 };

        Ok(L0Response { status, tokens, issues, alloc_mb_x10, majors, origin })
    }
}