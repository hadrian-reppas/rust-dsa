#![allow(dead_code)]

#[derive(Clone)]
pub struct BitQueue {
    bytes: Vec<u8>,
    front: usize,
    back: usize,
}

impl BitQueue {
    pub fn new() -> Self {
        BitQueue {
            bytes: Vec::new(),
            front: 0,
            back: 0,
        }
    }

    pub fn from_bytes(bytes: &Vec<u8>) -> Self {
        BitQueue {
            bytes: bytes.clone(),
            front: 0,
            back: 8 * bytes.len(),
        }
    }

    pub fn from_bits(bits: &Vec<bool>) -> Self {
        let mut q = BitQueue::new();
        for b in bits {
            q.push(*b);
        }
        q
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        let mut clone = self.clone();
        if clone.front_is_aligned() {
            clone.shrink();
            return clone.bytes;
        }
        let mut bytes = Vec::new();
        while let Some(byte) = clone.next_byte() {
            bytes.push(byte);
        }
        if clone.len() != 0 {
            let mut byte = 0;
            let mut i = 0;
            while let Some(bit) = clone.next() {
                byte |= (bit as u8) << i;
                i += 1;
            }
            bytes.push(byte);
        }
        bytes
    }

    pub fn as_bits(&self) -> Vec<bool> {
        let mut clone = self.clone();
        let mut bits = Vec::new();
        while let Some(b) = clone.next() {
            bits.push(b);
        }
        bits
    }

    pub fn len(&self) -> usize {
        self.back - self.front
    }

    pub fn push(&mut self, bit: bool) {
        if self.back % 8 == 0 {
            self.bytes.push(bit as u8);
        } else {
            let mask = (bit as u8) << self.back % 8;
            self.bytes[self.back / 8] |= mask;
        }
        self.back += 1;
    }

    pub fn push_byte(&mut self, byte: u8) {
        if self.back % 8 == 0 {
            self.bytes.push(byte);
        } else {
            self.bytes[self.back / 8] |= byte.wrapping_shl(self.back as u32 % 8);
            self.bytes.push(byte >> (8 - self.back % 8));
        }
        self.back += 8;
    }

    pub fn next(&mut self) -> Option<bool> {
        if self.front == self.back {
            None
        } else {
            let mask = 1 << self.front % 8;
            let bit = self.bytes[self.front / 8] & mask > 0;
            self.front += 1;
            Some(bit)
        }
    }

    pub fn next_byte(&mut self) -> Option<u8> {
        if self.len() < 8 {
            None
        } else if self.front % 8 == 0 {
            self.front += 8;
            Some(self.bytes[self.front / 8 - 1])
        } else {
            let mask = self.bytes[self.front / 8] >> self.front % 8;
            self.front += 8;
            Some(mask | self.bytes[self.front / 8] >> (8 - self.front % 8))
        }
    }

    pub fn next_u16(&mut self) -> Option<u16> {
        if self.len() < 16 {
            None
        } else {
            Some(self.next_byte()? as u16 | (self.next_byte()? as u16) << 8)
        }
    }

    pub fn next_u32(&mut self) -> Option<u32> {
        if self.len() < 32 {
            None
        } else {
            Some(
                self.next_byte()? as u32
                    | (self.next_byte()? as u32) << 8
                    | (self.next_byte()? as u32) << 16
                    | (self.next_byte()? as u32) << 24,
            )
        }
    }

    pub fn next_u64(&mut self) -> Option<u64> {
        if self.len() < 64 {
            None
        } else {
            Some(
                self.next_byte()? as u64
                    | (self.next_byte()? as u64) << 8
                    | (self.next_byte()? as u64) << 16
                    | (self.next_byte()? as u64) << 24
                    | (self.next_byte()? as u64) << 32
                    | (self.next_byte()? as u64) << 40
                    | (self.next_byte()? as u64) << 48
                    | (self.next_byte()? as u64) << 56,
            )
        }
    }

    pub fn align_front(&mut self) -> Option<()> {
        if self.front_is_aligned() {
            Some(())
        } else if self.len() < 8 - self.front % 8 {
            None
        } else {
            self.front += 8 - self.front % 8;
            Some(())
        }
    }

    pub fn front_is_aligned(&self) -> bool {
        self.front % 8 == 0
    }

    pub fn shrink(&mut self) {
        let i = self.front / 8;
        self.bytes.drain(0..i);
        self.front -= 8 * i;
        self.back -= 8 * i;
    }
}

#[cfg(test)]
mod test {
    use super::BitQueue;

    #[test]
    fn push_next() {
        let mut q = BitQueue::new();
        q.push(true);
        q.push(false);
        q.push(true);
        q.push(false);
        assert_eq!(q.len(), 4);
        assert_eq!(q.next(), Some(true));
        assert_eq!(q.next(), Some(false));
        assert_eq!(q.next(), Some(true));
        assert_eq!(q.next(), Some(false));
        assert_eq!(q.next(), None);
    }

    #[test]
    fn from_bytes() {
        let mut q = BitQueue::from_bytes(&"abc".as_bytes().to_vec());
        assert_eq!(q.next_byte(), Some('a' as u8));
        assert_eq!(q.next_byte(), Some('b' as u8));
        assert_eq!(q.next_byte(), Some('c' as u8));
        assert_eq!(q.next_byte(), None);
    }

    #[test]
    fn bytes() {
        let mut q = BitQueue::from_bits(&vec![true, false, false, true]);
        q.push_byte(0b01110100);
        q.push(false);
        q.push(true);
        q.push_byte(0b11011000);
        q.push(true);
        assert_eq!(q.len(), 23);
        assert_eq!(q.next_byte(), Some(0b01001001));
        assert_eq!(q.next_byte(), Some(0b00100111));
        q.push(true);
        q.push(false);
        assert_eq!(q.next_byte(), Some(0b11110110));
        assert_eq!(q.next_byte(), None);
        assert_eq!(q.next(), Some(false));
        assert_eq!(q.next(), None);
    }

    #[test]
    fn back_and_forth() {
        let bytes = vec![
            33, 232, 183, 12, 212, 179, 243, 191, 119, 174, 140, 64, 255, 56, 116,
        ];
        let q = BitQueue::from_bytes(&bytes);
        assert_eq!(bytes, q.as_bytes());
    }

    #[test]
    fn push_bytes() {
        let bytes = vec![
            33, 232, 183, 12, 212, 179, 243, 191, 119, 174, 140, 64, 255, 56, 116,
        ];
        let mut q = BitQueue::new();
        for byte in &bytes {
            q.push_byte(*byte);
        }
        assert_eq!(bytes, q.as_bytes());
    }

    #[test]
    fn align_front() {
        let bits = vec![
            true, true, true, false, false, true, false, true, false, false, true, true,
        ];
        let mut q = BitQueue::from_bits(&bits);
        q.next();
        q.next();
        q.align_front().unwrap();
        assert_eq!(q.as_bits(), vec![false, false, true, true]);
    }
}
