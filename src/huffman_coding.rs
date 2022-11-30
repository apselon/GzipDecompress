#![forbid(unsafe_code)]

use std::{collections::HashMap, convert::TryFrom, io::BufRead};

use anyhow::Result;

use crate::bit_reader::{BitReader, BitSequence};

////////////////////////////////////////////////////////////////////////////////

pub fn decode_litlen_distance_trees<T: BufRead>(
    bit_reader: &mut BitReader<T>,
) -> Result<(HuffmanCoding<LitLenToken>, HuffmanCoding<DistanceToken>)> {
    // See RFC 1951, section 3.2.7.
    let hlit = bit_reader.read_bits(5)?.bits() + 257_u64;
    let hdist = bit_reader.read_bits(5)?.bits() + 1_u64;
    let hclen = bit_reader.read_bits(4)?.bits() + 4_u64;

    let mut tct_code_lengths = vec![0_u8; 19];
    let pos_order: [usize; 19] = [
        16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
    ];

    for i in 0..hclen as usize {
        let cur_bits = bit_reader.read_bits(3)?.bits() as u8;
        tct_code_lengths[pos_order[i]] = cur_bits;
    }

    let tct_decoder = HuffmanCoding::<TreeCodeToken>::from_lengths(&tct_code_lengths[..])?;

    /* 2. Get LitLen-code-lengths vector. */
    let mut litlen_code_lengths = vec![0_u8; 286];

    let mut i = 0_usize;
    while i < hlit as usize {
        let cur_symb = tct_decoder.read_symbol(bit_reader)?;

        match cur_symb {
            TreeCodeToken::Length(l) => {
                litlen_code_lengths[i] = l;
                i += 1;
            }

            TreeCodeToken::CopyPrev => {
                let extra = bit_reader.read_bits(2)?.bits() as usize;
                let prev_len = litlen_code_lengths[i - 1];

                for _ in 0..(3 + extra) {
                    litlen_code_lengths[i] = prev_len;
                    i += 1;
                }
            }

            TreeCodeToken::RepeatZero { base, extra_bits } => {
                let extra = bit_reader.read_bits(extra_bits)?.bits() as u16;
                i += (base + extra) as usize;
            }
        };
    }

    /* 3. Build Huffman-decoder for LitLen-codes from their lengths. */
    let litlen_decoder = HuffmanCoding::<LitLenToken>::from_lengths(&litlen_code_lengths[..])?;

    /* 5. Get Dist-code-lengths vector */
    let mut dist_code_lengths = vec![0_u8; 30];

    i = 0_usize;
    while i < hdist as usize {
        let cur_symb = tct_decoder.read_symbol(bit_reader)?;

        match cur_symb {
            TreeCodeToken::Length(l) => {
                dist_code_lengths[i] = l;
                i += 1;
            }

            TreeCodeToken::CopyPrev => {
                let extra = bit_reader.read_bits(2)?.bits() as usize;
                let prev_len = dist_code_lengths[i - 1];

                for _ in 0..(3 + extra) {
                    dist_code_lengths[i] = prev_len;
                    i += 1;
                }
            }

            TreeCodeToken::RepeatZero { base, extra_bits } => {
                let extra = bit_reader.read_bits(extra_bits)?.bits() as u16;
                i += (base + extra) as usize;
            }
        }
    }
    /* 6. Build Huffman-decoder for Dist-codes from their lengths. */

    let dist_decoder = HuffmanCoding::<DistanceToken>::from_lengths(&dist_code_lengths[..])?;

    Ok((litlen_decoder, dist_decoder))
}

////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy, Debug)]
pub enum TreeCodeToken {
    Length(u8),
    CopyPrev,
    RepeatZero { base: u16, extra_bits: u8 },
}

impl TryFrom<HuffmanCodeWord> for TreeCodeToken {
    type Error = anyhow::Error;

    fn try_from(value: HuffmanCodeWord) -> Result<Self> {
        // See RFC 1951, section 3.2.7.
        let v = value.0;

        if v > 18 {
            anyhow::bail!("Too big len");
        }

        return Ok(match v {
            0..=15 => Self::Length(v as u8),
            16 => Self::CopyPrev,
            17 => Self::RepeatZero {
                base: 3,
                extra_bits: 3,
            },
            18 => Self::RepeatZero {
                base: 11,
                extra_bits: 7,
            },
            _ => panic!("Bad TreeCodeToken"),
        });
    }
}

////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy, Debug)]
pub enum LitLenToken {
    Literal(u8),
    EndOfBlock,
    Length { base: u16, extra_bits: u8 },
}

impl TryFrom<HuffmanCodeWord> for LitLenToken {
    type Error = anyhow::Error;

    fn try_from(value: HuffmanCodeWord) -> Result<Self> {
        // See RFC 1951, section 3.2.5.
        let v = value.0;

        if v > 285 {
            anyhow::bail!("Too big len");
        }

        return Ok(match v {
            0..=255 => Self::Literal(v as u8),
            256 => Self::EndOfBlock,
            257..=264 => Self::Length {
                base: 3 + (v - 257_u16),
                extra_bits: 0,
            },
            265..=268 => Self::Length {
                base: 11 + 2 * (v - 265_u16),
                extra_bits: 1,
            },
            269..=272 => Self::Length {
                base: 19 + 4 * (v - 269_u16),
                extra_bits: 2,
            },
            273..=276 => Self::Length {
                base: 35 + 8 * (v - 273_u16),
                extra_bits: 3,
            },
            277..=280 => Self::Length {
                base: 67 + 16 * (v - 277_u16),
                extra_bits: 4,
            },
            281..=284 => Self::Length {
                base: 131 + 32 * (v - 281_u16),
                extra_bits: 5,
            },
            285 => Self::Length {
                base: 258,
                extra_bits: 0,
            },
            _ => panic!("Bad code"),
        });
    }
}

////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy, Debug)]
pub struct DistanceToken {
    pub base: u16,
    pub extra_bits: u8,
}

impl TryFrom<HuffmanCodeWord> for DistanceToken {
    type Error = anyhow::Error;

    fn try_from(value: HuffmanCodeWord) -> Result<Self> {
        // See RFC 1951, section 3.2.5.
        let v = value.0;

        if v > 29 {
            anyhow::bail!("Too big DistanceToken");
        }

        return Ok(match v {
            0..=3 => DistanceToken {
                base: 1 + v,
                extra_bits: 0,
            },
            4..=5 => DistanceToken {
                base: 5 + 2 * (v - 4),
                extra_bits: 1,
            },

            6..=7 => DistanceToken {
                base: 9 + 4 * (v - 6),
                extra_bits: 2,
            },

            8..=9 => DistanceToken {
                base: 17 + 8 * (v - 8),
                extra_bits: 3,
            },
            10..=11 => DistanceToken {
                base: 33 + 16 * (v - 10),
                extra_bits: 4,
            },
            12..=13 => DistanceToken {
                base: 65 + 32 * (v - 12),
                extra_bits: 5,
            },
            14..=15 => DistanceToken {
                base: 129 + 64 * (v - 14),
                extra_bits: 6,
            },
            16..=17 => DistanceToken {
                base: 257 + 128 * (v - 16),
                extra_bits: 7,
            },
            18..=19 => DistanceToken {
                base: 513 + 256 * (v - 18),
                extra_bits: 8,
            },
            20..=21 => DistanceToken {
                base: 1025 + 512 * (v - 20),
                extra_bits: 9,
            },
            22..=23 => DistanceToken {
                base: 2049 + 1024 * (v - 22),
                extra_bits: 10,
            },
            24..=25 => DistanceToken {
                base: 4097 + 2048 * (v - 24),
                extra_bits: 11,
            },
            26..=27 => DistanceToken {
                base: 8193 + 4096 * (v - 26),
                extra_bits: 12,
            },
            28..=29 => DistanceToken {
                base: 16385 + 8192 * (v - 28),
                extra_bits: 13,
            },
            _ => panic!("Too big distance token"),
        });
    }
}

////////////////////////////////////////////////////////////////////////////////

const MAX_BITS: usize = 15;

pub struct HuffmanCodeWord(pub u16);

pub struct HuffmanCoding<T> {
    map: HashMap<BitSequence, T>,
}

impl<T> HuffmanCoding<T>
where
    T: Copy + TryFrom<HuffmanCodeWord, Error = anyhow::Error>,
{
    pub fn new(map: HashMap<BitSequence, T>) -> Self {
        Self { map }
    }

    #[allow(unused)]
    pub fn decode_symbol(&self, seq: BitSequence) -> Option<T> {
        self.map.get(&seq).copied()
    }

    pub fn read_symbol<U: BufRead>(&self, bit_reader: &mut BitReader<U>) -> Result<T> {
        let mut cur_bits = BitSequence::new(0, 0);
        loop {
            cur_bits = cur_bits.concat(bit_reader.pop_bit()?);
            if let Some(symbol) = self.decode_symbol(cur_bits) {
                return Ok(symbol);
            }

            if cur_bits.len() as usize > MAX_BITS {
                break;
            }
        }

        anyhow::bail!("Could not decode symbol: cur_bits = {:b}", cur_bits.bits());
    }

    pub fn from_lengths(code_lengths: &[u8]) -> Result<Self> {
        /* 1. Count codes of each len. */

        let mut len_count = HashMap::<u8, u64>::new();
        let mut max_len = 0_u8;

        for &len in code_lengths {
            max_len = std::cmp::max(max_len, len);
            *len_count.entry(len).or_insert(0) += 1;
        }

        len_count.insert(0, 0);

        /* 2. Generate minimal huffan code for each length. */

        let mut cur_code = 0_u64;
        let mut min_code_of_len = vec![0_u64; max_len as usize + 1];

        for len in 1..=max_len {
            cur_code = (cur_code + len_count.get(&(len - 1)).map_or(0, |v| *v)) << 1;
            min_code_of_len[len as usize] = cur_code;
        }

        /* 3. Generate huffman codes for symbols 0, 1, 2 ... */

        let mut map = HashMap::<BitSequence, T>::new();

        for cur_symb in 0..code_lengths.len() as u16 {
            let cur_symb_code_len = code_lengths[cur_symb as usize];
            let cur_symb_huff_code = min_code_of_len[cur_symb_code_len as usize];

            min_code_of_len[cur_symb_code_len as usize] += 1;

            let cur_symb_word = HuffmanCodeWord(cur_symb);
            let cur_symb_code_seq = BitSequence::new(cur_symb_huff_code, cur_symb_code_len);

            map.insert(cur_symb_code_seq, T::try_from(cur_symb_word)?);
        }

        Ok(Self::new(map))
    }
}

////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq)]
    struct Value(u16);

    impl TryFrom<HuffmanCodeWord> for Value {
        type Error = anyhow::Error;

        fn try_from(x: HuffmanCodeWord) -> Result<Self> {
            Ok(Self(x.0))
        }
    }

    #[test]
    fn from_lengths() -> Result<()> {
        let code = HuffmanCoding::<Value>::from_lengths(&[2, 3, 4, 3, 3, 4, 2])?;

        assert_eq!(
            code.decode_symbol(BitSequence::new(0b00, 2)),
            Some(Value(0)),
        );
        assert_eq!(
            code.decode_symbol(BitSequence::new(0b100, 3)),
            Some(Value(1)),
        );
        assert_eq!(
            code.decode_symbol(BitSequence::new(0b1110, 4)),
            Some(Value(2)),
        );
        assert_eq!(
            code.decode_symbol(BitSequence::new(0b101, 3)),
            Some(Value(3)),
        );
        assert_eq!(
            code.decode_symbol(BitSequence::new(0b110, 3)),
            Some(Value(4)),
        );
        assert_eq!(
            code.decode_symbol(BitSequence::new(0b1111, 4)),
            Some(Value(5)),
        );
        assert_eq!(
            code.decode_symbol(BitSequence::new(0b01, 2)),
            Some(Value(6)),
        );

        assert_eq!(code.decode_symbol(BitSequence::new(0b0, 1)), None);
        assert_eq!(code.decode_symbol(BitSequence::new(0b10, 2)), None);
        assert_eq!(code.decode_symbol(BitSequence::new(0b111, 3)), None,);

        Ok(())
    }

    #[test]
    fn read_symbol() -> Result<()> {
        let code = HuffmanCoding::<Value>::from_lengths(&[2, 3, 4, 3, 3, 4, 2])?;
        let mut data: &[u8] = &[0b10111001, 0b11001010, 0b11101101];
        let mut reader = BitReader::new(&mut data);

        assert_eq!(code.read_symbol(&mut reader)?, Value(1));
        assert_eq!(code.read_symbol(&mut reader)?, Value(2));
        assert_eq!(code.read_symbol(&mut reader)?, Value(3));
        assert_eq!(code.read_symbol(&mut reader)?, Value(6));
        assert_eq!(code.read_symbol(&mut reader)?, Value(0));
        assert_eq!(code.read_symbol(&mut reader)?, Value(2));
        assert_eq!(code.read_symbol(&mut reader)?, Value(4));
        assert!(code.read_symbol(&mut reader).is_err());

        Ok(())
    }

    #[test]
    fn from_lengths_with_zeros() -> Result<()> {
        let lengths = [3, 4, 5, 5, 0, 0, 6, 6, 4, 0, 6, 0, 7];
        let code = HuffmanCoding::<Value>::from_lengths(&lengths)?;
        let mut data: &[u8] = &[
            0b00100000, 0b00100001, 0b00010101, 0b10010101, 0b00110101, 0b00011101,
        ];
        let mut reader = BitReader::new(&mut data);

        assert_eq!(code.read_symbol(&mut reader)?, Value(0));
        assert_eq!(code.read_symbol(&mut reader)?, Value(1));
        assert_eq!(code.read_symbol(&mut reader)?, Value(2));
        assert_eq!(code.read_symbol(&mut reader)?, Value(3));
        assert_eq!(code.read_symbol(&mut reader)?, Value(6));
        assert_eq!(code.read_symbol(&mut reader)?, Value(7));
        assert_eq!(code.read_symbol(&mut reader)?, Value(8));
        assert_eq!(code.read_symbol(&mut reader)?, Value(10));
        assert_eq!(code.read_symbol(&mut reader)?, Value(12));
        assert!(code.read_symbol(&mut reader).is_err());

        Ok(())
    }

    #[test]
    fn from_lengths_additional() -> Result<()> {
        let lengths = [
            9, 10, 10, 8, 8, 8, 5, 6, 4, 5, 4, 5, 4, 5, 4, 4, 5, 4, 4, 5, 4, 5, 4, 5, 5, 5, 4, 6, 6,
        ];
        let code = HuffmanCoding::<Value>::from_lengths(&lengths)?;
        let mut data: &[u8] = &[
            0b11111000, 0b10111100, 0b01010001, 0b11111111, 0b00110101, 0b11111001, 0b11011111,
            0b11100001, 0b01110111, 0b10011111, 0b10111111, 0b00110100, 0b10111010, 0b11111111,
            0b11111101, 0b10010100, 0b11001110, 0b01000011, 0b11100111, 0b00000010,
        ];
        let mut reader = BitReader::new(&mut data);

        assert_eq!(code.read_symbol(&mut reader)?, Value(10));
        assert_eq!(code.read_symbol(&mut reader)?, Value(7));
        assert_eq!(code.read_symbol(&mut reader)?, Value(27));
        assert_eq!(code.read_symbol(&mut reader)?, Value(22));
        assert_eq!(code.read_symbol(&mut reader)?, Value(9));
        assert_eq!(code.read_symbol(&mut reader)?, Value(0));
        assert_eq!(code.read_symbol(&mut reader)?, Value(11));
        assert_eq!(code.read_symbol(&mut reader)?, Value(15));
        assert_eq!(code.read_symbol(&mut reader)?, Value(2));
        assert_eq!(code.read_symbol(&mut reader)?, Value(20));
        assert_eq!(code.read_symbol(&mut reader)?, Value(8));
        assert_eq!(code.read_symbol(&mut reader)?, Value(4));
        assert_eq!(code.read_symbol(&mut reader)?, Value(23));
        assert_eq!(code.read_symbol(&mut reader)?, Value(24));
        assert_eq!(code.read_symbol(&mut reader)?, Value(5));
        assert_eq!(code.read_symbol(&mut reader)?, Value(26));
        assert_eq!(code.read_symbol(&mut reader)?, Value(18));
        assert_eq!(code.read_symbol(&mut reader)?, Value(12));
        assert_eq!(code.read_symbol(&mut reader)?, Value(25));
        assert_eq!(code.read_symbol(&mut reader)?, Value(1));
        assert_eq!(code.read_symbol(&mut reader)?, Value(3));
        assert_eq!(code.read_symbol(&mut reader)?, Value(6));
        assert_eq!(code.read_symbol(&mut reader)?, Value(13));
        assert_eq!(code.read_symbol(&mut reader)?, Value(14));
        assert_eq!(code.read_symbol(&mut reader)?, Value(16));
        assert_eq!(code.read_symbol(&mut reader)?, Value(17));
        assert_eq!(code.read_symbol(&mut reader)?, Value(19));
        assert_eq!(code.read_symbol(&mut reader)?, Value(21));

        Ok(())
    }
}
