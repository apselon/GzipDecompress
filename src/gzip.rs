#![forbid(unsafe_code)]

use std::io::{BufRead, Write};

use anyhow::Result;
use crc::Crc;

use crate::{bit_reader::BitReader, deflate::DeflateReader, tracking_writer::TrackingWriter};

////////////////////////////////////////////////////////////////////////////////

const ID1: u8 = 0x1f;
const ID2: u8 = 0x8b;

const CM_DEFLATE: u8 = 8;

const FTEXT_OFFSET: u8 = 0;
const FHCRC_OFFSET: u8 = 1;
const FEXTRA_OFFSET: u8 = 2;
const FNAME_OFFSET: u8 = 3;
const FCOMMENT_OFFSET: u8 = 4;

////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Default)]
pub struct MemberHeader {
    pub compression_method: CompressionMethod,
    pub modification_time: u32,
    pub extra: Option<Vec<u8>>,
    pub name: Option<String>,
    pub comment: Option<String>,
    pub extra_flags: u8,
    pub os: u8,
    pub has_crc: bool,
    pub is_text: bool,
}

impl MemberHeader {
    pub fn crc16(&self) -> u16 {
        let crc = Crc::<u32>::new(&crc::CRC_32_ISO_HDLC);
        let mut digest = crc.digest();

        digest.update(&[ID1, ID2, self.compression_method.into(), self.flags().0]);
        digest.update(&self.modification_time.to_le_bytes());
        digest.update(&[self.extra_flags, self.os]);

        if let Some(extra) = &self.extra {
            digest.update(&(extra.len() as u16).to_le_bytes());
            digest.update(extra);
        }

        if let Some(name) = &self.name {
            digest.update(name.as_bytes());
            digest.update(&[0]);
        }

        if let Some(comment) = &self.comment {
            digest.update(comment.as_bytes());
            digest.update(&[0]);
        }

        (digest.finalize() & 0xffff) as u16
    }

    pub fn flags(&self) -> MemberFlags {
        let mut flags = MemberFlags(0);
        flags.set_is_text(self.is_text);
        flags.set_has_crc(self.has_crc);
        flags.set_has_extra(self.extra.is_some());
        flags.set_has_name(self.name.is_some());
        flags.set_has_comment(self.comment.is_some());
        flags
    }
}

////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy, Debug)]
pub enum CompressionMethod {
    Deflate,
    Unknown(u8),
}

impl Default for CompressionMethod {
    fn default() -> Self {
        CompressionMethod::Unknown(0)
    }
}

impl From<u8> for CompressionMethod {
    fn from(value: u8) -> Self {
        match value {
            CM_DEFLATE => Self::Deflate,
            x => Self::Unknown(x),
        }
    }
}

impl From<CompressionMethod> for u8 {
    fn from(method: CompressionMethod) -> u8 {
        match method {
            CompressionMethod::Deflate => CM_DEFLATE,
            CompressionMethod::Unknown(x) => x,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub struct MemberFlags(u8);

#[allow(unused)]
impl MemberFlags {
    fn bit(&self, n: u8) -> bool {
        (self.0 >> n) & 1 != 0
    }

    fn set_bit(&mut self, n: u8, value: bool) {
        if value {
            self.0 |= 1 << n;
        } else {
            self.0 &= !(1 << n);
        }
    }

    pub fn is_text(&self) -> bool {
        self.bit(FTEXT_OFFSET)
    }

    pub fn set_is_text(&mut self, value: bool) {
        self.set_bit(FTEXT_OFFSET, value)
    }

    pub fn has_crc(&self) -> bool {
        self.bit(FHCRC_OFFSET)
    }

    pub fn set_has_crc(&mut self, value: bool) {
        self.set_bit(FHCRC_OFFSET, value)
    }

    pub fn has_extra(&self) -> bool {
        self.bit(FEXTRA_OFFSET)
    }

    pub fn set_has_extra(&mut self, value: bool) {
        self.set_bit(FEXTRA_OFFSET, value)
    }

    pub fn has_name(&self) -> bool {
        self.bit(FNAME_OFFSET)
    }

    pub fn set_has_name(&mut self, value: bool) {
        self.set_bit(FNAME_OFFSET, value)
    }

    pub fn has_comment(&self) -> bool {
        self.bit(FCOMMENT_OFFSET)
    }

    pub fn set_has_comment(&mut self, value: bool) {
        self.set_bit(FCOMMENT_OFFSET, value)
    }
}

////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub struct MemberFooter {
    pub data_crc32: u32,
    pub data_size: u32,
}

////////////////////////////////////////////////////////////////////////////////

pub struct GzipReader<T, W> {
    reader: BitReader<T>,
    output: W,
}

impl<T: BufRead, W: Write> GzipReader<T, W> {
    pub fn new(stream: T, output: W) -> Self {
        Self {
            reader: BitReader::<T>::new(stream),
            output,
        }
    }

    fn read_header(&mut self) -> Result<(MemberHeader, MemberFlags)> {
        match self.reader.read_bits(8) {
            Ok(id1) => {
                if id1.bits() != ID1.into() {
                    anyhow::bail!("wrong id values!");
                }
            }
            Err(ref e) if e.kind() == std::io::ErrorKind::UnexpectedEof => {
                anyhow::bail!("START_EOF");
            }
            Err(e) => {
                anyhow::bail!(e.to_string());
            }
        }

        if self.reader.read_bits(8)?.bits() as u8 != ID2 {
            anyhow::bail!("wrong id values!");
        }

        let mut header = MemberHeader::default();

        let cm_bits = self.reader.read_bits(8)?.bits() as u8;
        header.compression_method = CompressionMethod::from(cm_bits);

        let flg_bits = self.reader.read_bits(8)?.bits() as u8;

        let mtime_bits = self.reader.read_bits(32)?.bits() as u32;
        header.modification_time = mtime_bits;

        let xfl_bits = self.reader.read_bits(8)?.bits() as u8;
        header.extra_flags = xfl_bits;

        let os_bits = self.reader.read_bits(8)?.bits() as u8;
        header.os = os_bits;

        let memeber_flgs = MemberFlags(flg_bits);

        if memeber_flgs.is_text() {
            header.is_text = true;
        }

        if memeber_flgs.has_extra() {
            let xlen = self.reader.read_bits(16)?.bits() as u16;
            let mut extra_flags = vec![0_u8; xlen as usize];

            for cur_item in extra_flags.iter_mut().take(xlen.into()) {
                *cur_item = self.reader.read_bits(8)?.bits() as u8;
            }

            header.extra = Some(extra_flags);
        }

        if memeber_flgs.has_name() {
            let mut name = String::new();

            loop {
                let cur_bits = self.reader.read_bits(8)?.bits() as u8;
                if cur_bits == 0 {
                    break;
                }

                name.push(cur_bits as char);
            }

            header.name = Some(name);
        }

        if memeber_flgs.has_comment() {
            let mut comment = String::new();

            loop {
                let cur_bits = self.reader.read_bits(8)?.bits() as u8;
                if cur_bits == 0 {
                    break;
                }

                comment.push(cur_bits as char);
            }

            header.comment = Some(comment);
        }

        if memeber_flgs.has_crc() {
            header.has_crc = true;
            let crc = self.reader.read_bits(16)?.bits() as u16;

            if crc != header.crc16() {
                anyhow::bail!("header crc16 check failed");
            }
        }

        Ok((header, memeber_flgs))
    }

    fn read_deflate_bitstream(&mut self) -> Result<(u32, u32)> {
        let mut writer = TrackingWriter::new(&mut self.output);

        let block_start = self.reader.borrow_reader_from_boundary(); //Нужно ли тут borrow from boundary?
        let mut deflate_reader = DeflateReader::new(block_start);

        loop {
            if deflate_reader.decode_block(&mut writer)? {
                break;
            }
        }

        Ok((writer.byte_count() as u32, writer.crc32()))
    }

    fn read_footer(&mut self) -> Result<MemberFooter> {
        let data_crc32 = self.reader.read_bits(32)?.bits() as u32;
        let data_size = self.reader.read_bits(32)?.bits() as u32;

        Ok(MemberFooter {
            data_crc32,
            data_size,
        })
    }

    pub fn read_member(&mut self) -> Result<bool> {
        let header = match self.read_header() {
            Ok((h, _)) => h,
            Err(ref e) if e.to_string().contains("START_EOF") => return Ok(true),
            Err(e) => return Err(e),
        };

        match header.compression_method {
            CompressionMethod::Deflate => {}
            _ => anyhow::bail!("unsupported compression method"),
        }

        let (written_byte_count, written_crc32) = self.read_deflate_bitstream()?;

        let footer = self.read_footer()?;

        if footer.data_size != written_byte_count {
            anyhow::bail!("length check failed");
        }

        if footer.data_crc32 != written_crc32 {
            anyhow::bail!("crc32 check failed");
        }

        Ok(false)
    }
}

////////////////////////////////////////////////////////////////////////////////
