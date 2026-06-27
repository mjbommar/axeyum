//! 256-bit EVM word helpers built on `axeyum_ir::wide::WideUint`.
//!
//! The concrete interpreter runs over [`Word`] (a 256-bit `WideUint`) so witness
//! re-execution uses *exactly* the EVM-256 arithmetic the symbolic lowering
//! encodes — the DISAGREE=0 floor compares like with like.

use axeyum_ir::WideUint;

/// The EVM word width in bits.
pub const WIDTH: u32 = 256;

/// A concrete 256-bit EVM word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Word(pub WideUint);

impl Word {
    /// Zero.
    #[must_use]
    pub fn zero() -> Self {
        Word(WideUint::zero(WIDTH))
    }

    /// A word from a `u128` (zero-extended to 256 bits).
    #[must_use]
    pub fn from_u128(value: u128) -> Self {
        Word(WideUint::from_u128(value, WIDTH))
    }

    /// A word from up-to-32 big-endian bytes (right-aligned, zero-padded on the
    /// left — EVM `PUSH`/word semantics).
    #[must_use]
    pub fn from_be_bytes(bytes: &[u8]) -> Self {
        let mut full = [0u8; 32];
        let n = bytes.len().min(32);
        full[32 - n..].copy_from_slice(&bytes[bytes.len() - n..]);
        // Build LSB-first bits from the 32 big-endian bytes.
        let mut bits = vec![false; 256];
        for (byte_idx, &b) in full.iter().enumerate() {
            // full[0] is the most-significant byte (bits 248..256).
            let base = (31 - byte_idx) * 8;
            for bit in 0..8 {
                if (b >> bit) & 1 == 1 {
                    bits[base + bit] = true;
                }
            }
        }
        Word(WideUint::from_lsb_bits(&bits))
    }

    /// The 32-byte big-endian representation.
    #[must_use]
    pub fn to_be_bytes(&self) -> [u8; 32] {
        let bits = self.0.to_lsb_bits();
        let mut out = [0u8; 32];
        for (i, chunk) in out.iter_mut().enumerate() {
            // out[i] is the byte for bits [ (31-i)*8 .. +8 ).
            let base = (31 - i) * 8;
            let mut byte = 0u8;
            for bit in 0..8 {
                if base + bit < bits.len() && bits[base + bit] {
                    byte |= 1 << bit;
                }
            }
            *chunk = byte;
        }
        out
    }

    /// The low 64 bits as a `usize` clamped to `u64::MAX` semantics — used for
    /// concrete memory offsets and jump targets. Returns `None` if any bit at or
    /// above 64 is set (offset too large to be a usable index).
    #[must_use]
    pub fn to_usize(&self) -> Option<usize> {
        let bits = self.0.to_lsb_bits();
        if bits.iter().skip(64).any(|&b| b) {
            return None;
        }
        let mut v: u64 = 0;
        for (i, &b) in bits.iter().take(64).enumerate() {
            if b {
                v |= 1u64 << i;
            }
        }
        usize::try_from(v).ok()
    }

    /// Is this word zero?
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}
