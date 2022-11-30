#![forbid(unsafe_code)]

use std::io::{self, BufRead};

////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BitSequence {
    len: u8,
    bits: u64,
}

impl BitSequence {
    pub fn new(bits: u64, len: u8) -> Self {
        assert!(len <= 64);

        let mask = !(!0 << len);
        let z_bits = bits & mask;

        Self { bits: z_bits, len }
    }

    pub fn bits(&self) -> u64 {
        self.bits
    }

    pub fn len(&self) -> u8 {
        self.len
    }

    pub fn concat(self, other: Self) -> Self {
        assert!(self.len + other.len <= 64);

        let bits = self.bits << other.len;

        Self {
            bits: bits | other.bits,
            len: self.len + other.len,
        }
    }

    /*
    pub fn append(&mut self, other: &Self) {
        assert!(self.len + other.len <= 64);
        let other_bits = self.bits >> self.len;
        self.bits |= other_bits;
        self.len += other.len;
    }
    */
}

////////////////////////////////////////////////////////////////////////////////

pub struct BitReader<T> {
    stream: T,
    bit_index: usize, //index of the bit which new data in the first byte of stream starts from
    cur_byte: [u8; 1],
}

impl<T: BufRead> BitReader<T> {
    pub fn new(stream: T) -> Self {
        Self {
            stream,
            bit_index: 0,
            cur_byte: [13; 1],
        }
    }

    pub fn pop_bit(&mut self) -> io::Result<BitSequence> {
        if self.bit_index % 8 == 0 {
            self.bit_index = 0;
            self.stream.read_exact(&mut self.cur_byte)?;
        }

        let bit = (self.cur_byte[0] >> self.bit_index) & 1;
        self.bit_index += 1;

        Ok(BitSequence::new(bit as u64, 1))
    }

    pub fn read_bits(&mut self, len: u8) -> io::Result<BitSequence> {
        let mut cur_bits = BitSequence::new(0, 0);

        for _ in 0..len {
            cur_bits = self.pop_bit()?.concat(cur_bits);
        }

        Ok(cur_bits)
    }

    // Discard all the unread bits in the current byte and return a mutable reference
    // to the underlying reader.
    pub fn borrow_reader_from_boundary(&mut self) -> &mut T {
        self.bit_index = 0;
        &mut self.stream
    }
}

////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;
    use byteorder::ReadBytesExt;

    #[test]
    fn read_bits() -> io::Result<()> {
        let data: &[u8] = &[0b01100011, 0b11011011, 0b10101111];
        let mut reader = BitReader::new(data);
        assert_eq!(reader.read_bits(1)?, BitSequence::new(0b1, 1));
        assert_eq!(reader.read_bits(2)?, BitSequence::new(0b01, 2));
        assert_eq!(reader.read_bits(3)?, BitSequence::new(0b100, 3));
        assert_eq!(reader.read_bits(4)?, BitSequence::new(0b1101, 4));
        assert_eq!(reader.read_bits(5)?, BitSequence::new(0b10110, 5));
        assert_eq!(reader.read_bits(8)?, BitSequence::new(0b01011111, 8));
        assert_eq!(
            reader.read_bits(2).unwrap_err().kind(),
            io::ErrorKind::UnexpectedEof
        );
        Ok(())
    }

    #[test]
    fn borrow_reader_from_boundary() -> io::Result<()> {
        let data: &[u8] = &[0b01100011, 0b11011011, 0b10101111];
        let mut reader = BitReader::new(data);
        assert_eq!(reader.read_bits(3)?, BitSequence::new(0b011, 3));
        assert_eq!(reader.borrow_reader_from_boundary().read_u8()?, 0b11011011);
        assert_eq!(reader.read_bits(8)?, BitSequence::new(0b10101111, 8));
        Ok(())
    }
}
