#![forbid(unsafe_code)]

use std::io::{BufRead, Write};

use anyhow::Result;
use byteorder::WriteBytesExt;

use crate::bit_reader::BitReader;
use crate::huffman_coding::{decode_litlen_distance_trees, DistanceToken, LitLenToken};
use crate::tracking_writer::TrackingWriter;

////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub struct BlockHeader {
    pub is_final: bool,
    pub compression_type: CompressionType,
}

#[derive(Debug)]
pub enum CompressionType {
    Uncompressed = 0,
    FixedTree = 1,
    DynamicTree = 2,
    Reserved = 3,
}

////////////////////////////////////////////////////////////////////////////////

pub struct DeflateReader<T> {
    bit_reader: BitReader<T>,
}

impl<T: BufRead> DeflateReader<T> {
    pub fn new(stream: T) -> Self {
        Self {
            bit_reader: BitReader::<T>::new(stream),
        }
    }

    fn read_header(&mut self) -> Result<BlockHeader> {
        let is_final = self.bit_reader.read_bits(1)?.bits() != 0;
        let compression_bits = self.bit_reader.read_bits(2)?.bits();
        let header = BlockHeader {
            is_final,
            compression_type: match compression_bits {
                0 => CompressionType::Uncompressed,
                1 => CompressionType::FixedTree,
                2 => CompressionType::DynamicTree,
                3 => CompressionType::Reserved,
                _ => panic!("Bad compression type"),
            },
        };

        Ok(header)
    }

    pub fn decode_block<W: Write>(&mut self, output: &mut TrackingWriter<W>) -> Result<bool> {
        /* 1. Read block header */
        /* 2. If uncompressed, just write bitstream */
        /* 3. Else write decompressed data */
        let block_header = self.read_header()?;

        match block_header.compression_type {
            CompressionType::Uncompressed => {
                self.bit_reader.borrow_reader_from_boundary();
                let len = self.bit_reader.read_bits(16)?.bits() as u16;
                let nlen = self.bit_reader.read_bits(16)?.bits() as u16;

                if nlen != !len {
                    anyhow::bail!(
                        "nlen check failed got len = {}, nlen = {}, !nlen = {}",
                        len,
                        nlen,
                        !nlen
                    );
                }

                let mut data = vec![0_u8; len.into()];
                for cur_item in data.iter_mut().take(len.into()) {
                    *cur_item = self.bit_reader.read_bits(8)?.bits() as u8;
                }

                output.write_all(&data[..])?;
            }

            CompressionType::DynamicTree => {
                let (litlen_code, dist_code) = decode_litlen_distance_trees(&mut self.bit_reader)?;

                loop {
                    let cur_symb = litlen_code.read_symbol(&mut self.bit_reader)?;
                    match cur_symb {
                        LitLenToken::EndOfBlock => break,
                        LitLenToken::Literal(c) => {
                            output.write_u8(c)?;
                            continue;
                        }
                        LitLenToken::Length { base, extra_bits } => {
                            let mut extra = self.bit_reader.read_bits(extra_bits)?.bits() as u16;
                            let len = base + extra;

                            let DistanceToken { base, extra_bits } =
                                dist_code.read_symbol(&mut self.bit_reader)?;

                            extra = self.bit_reader.read_bits(extra_bits)?.bits() as u16;
                            let dist = base + extra;

                            output.write_previous(dist.into(), len.into())?;
                            continue;
                        }
                    }
                }
            }

            _ => anyhow::bail!("unsupported block type"),
        };

        Ok(block_header.is_final)
    }
}
