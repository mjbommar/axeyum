//! A tiny deterministic PRNG for reproducible scenario generation.
//!
//! Determinism is a public API promise for Axeyum: the same seed must yield
//! the same scenario on every machine. `SplitMix64` is used purely to make
//! scenario parameters reproducible, never for any security purpose.

/// A `SplitMix64` generator: small, fast, fully deterministic from its seed.
#[derive(Debug, Clone)]
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    /// Creates a generator seeded with `seed`.
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    /// Returns the next 64-bit output and advances the state.
    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Returns the next 128-bit output from two 64-bit draws.
    pub fn next_u128(&mut self) -> u128 {
        let hi = u128::from(self.next_u64());
        let lo = u128::from(self.next_u64());
        (hi << 64) | lo
    }

    /// Returns a value uniformly in `0..bound` (`bound` must be non-zero).
    ///
    /// Uses simple modulo reduction; the slight bias is irrelevant for picking
    /// scenario parameters.
    pub fn below(&mut self, bound: u64) -> u64 {
        self.next_u64() % bound
    }
}
