use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasher, Hash, Hasher};

const FNV1A_PRIME: u128 = 0x0000000001000000000000000000013B;
const FNV1A_OFFSET_BASIS: u128 = 0x6c62272e07bb014262b821756295c58d;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Digest(pub(crate) u128);

impl Default for Digest {
    fn default() -> Self {
        Self(FNV1A_OFFSET_BASIS)
    }
}

impl Digest {
    fn byte(&mut self, byte: u8) {
        self.0 ^= byte as u128;
        self.0 = self.0.wrapping_mul(FNV1A_PRIME);
    }

    pub(crate) fn zero(&mut self) {
        self.byte(0);
    }

    pub(crate) fn update(&mut self, value: isize) {
        for byte in value.to_ne_bytes() {
            self.byte(byte);
        }
    }
}

pub(crate) struct DigestHasher(u64);

impl Hasher for DigestHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, _data: &[u8]) {
        unreachable!("should only be used with Digest")
    }

    fn write_u128(&mut self, data: u128) {
        self.0 = data as u64;
    }
}

#[derive(Default)]
pub(crate) struct DigestHasherBuilder;

impl BuildHasher for DigestHasherBuilder {
    type Hasher = DigestHasher;

    fn build_hasher(&self) -> Self::Hasher {
        DigestHasher(0)
    }
}

pub(crate) type DigestMap<T> = HashMap<Digest, T, DigestHasherBuilder>;
pub(crate) type DigestSet = HashSet<Digest, DigestHasherBuilder>;
