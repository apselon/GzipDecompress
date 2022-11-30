#![forbid(unsafe_code)]

use anyhow::Result;
use crc::{Crc, Digest};
use std::io::{self, Write};

////////////////////////////////////////////////////////////////////////////////

const HISTORY_SIZE: usize = 32 * (1 << 10);
static CRC_CODER: Crc<u32> = Crc::<u32>::new(&crc::CRC_32_ISO_HDLC);

pub struct TrackingWriter<T> {
    inner: T,
    hist_buff: Vec<u8>,
    crc_digest: Digest<'static, u32>,
    num_bytes: usize,
}

impl<T: Write> Write for TrackingWriter<T> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let num_written = self.inner.write(buf)?;

        self.crc_digest.update(&buf[..num_written]);
        self.hist_buff.extend(&buf[..num_written]);

        if self.hist_buff.len() > HISTORY_SIZE {
            self.hist_buff
                .drain(0..(self.hist_buff.len() - HISTORY_SIZE));
        }

        self.num_bytes += num_written;
        Ok(num_written)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

impl<T: Write> TrackingWriter<T> {
    pub fn new(inner: T) -> Self {
        Self {
            inner,
            hist_buff: Vec::<u8>::with_capacity(HISTORY_SIZE),
            crc_digest: CRC_CODER.digest(),
            num_bytes: 0,
        }
    }

    // Write a sequence of `len` bytes written `dist` bytes ago.
    pub fn write_previous(&mut self, dist: usize, mut len: usize) -> Result<()> {
        let s = self.hist_buff.len().checked_sub(dist);

        if s.is_none() {
            anyhow::bail!("dist is bigger than hist_len\n");
        }

        let l = s.unwrap();

        while len > 0 {
            let r = std::cmp::min(l + len, self.hist_buff.len());
            let prev_buff = self.hist_buff[l..r].to_vec();
            let num_written = self.write(&prev_buff[..])?;
            if num_written != prev_buff.len() {
                anyhow::bail!("Bad write");
            }

            len -= num_written;
        }

        Ok(())
    }

    pub fn byte_count(&self) -> usize {
        self.num_bytes
    }

    pub fn crc32(self) -> u32 {
        self.crc_digest.finalize()
    }
}

////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;
    use byteorder::WriteBytesExt;

    #[test]
    fn write() -> Result<()> {
        let mut buf: &mut [u8] = &mut [0u8; 10];
        let mut writer = TrackingWriter::new(&mut buf);

        assert_eq!(writer.write(&[1, 2, 3, 4])?, 4);
        assert_eq!(writer.byte_count(), 4);

        assert_eq!(writer.write(&[4, 8, 15, 16, 23])?, 5);
        assert_eq!(writer.byte_count(), 9);

        assert_eq!(writer.write(&[0, 0, 123])?, 1);
        assert_eq!(writer.byte_count(), 10);

        assert_eq!(writer.write(&[42, 124, 234, 27])?, 0);
        assert_eq!(writer.byte_count(), 10);
        assert_eq!(writer.crc32(), 2992191065);

        Ok(())
    }

    #[test]
    fn write_previous() -> Result<()> {
        let mut buf: &mut [u8] = &mut [0u8; 512];
        let mut writer = TrackingWriter::new(&mut buf);

        for i in 0..=255 {
            writer.write_u8(i)?;
        }

        writer.write_previous(192, 128)?;
        assert_eq!(writer.byte_count(), 384);

        assert!(writer.write_previous(10000, 20).is_err());
        assert_eq!(writer.byte_count(), 384);

        assert!(writer.write_previous(256, 256).is_err());
        assert_eq!(writer.byte_count(), 512);

        assert!(writer.write_previous(1, 1).is_err());
        assert_eq!(writer.byte_count(), 512);
        assert_eq!(writer.crc32(), 2733545866);

        Ok(())
    }
}
