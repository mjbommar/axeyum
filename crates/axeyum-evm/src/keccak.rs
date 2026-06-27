//! A pure-Rust Keccak-256 (the EVM `SHA3` hash) — used by the **concrete
//! soundness oracle** only.
//!
//! The symbolic side models `KECCAK256` with a *fresh symbolic word* per hash
//! plus pairwise injectivity constraints (`a == b ⇔ keccak(a) == keccak(b)`, the
//! halmos/hevm precision trick): it assumes collision-freedom but is free to pick
//! any concrete hash *value* for a given argument. That is a sound
//! over-approximation of real keccak (which is collision-resistant, so injective
//! in practice), but it means a lifted witness must be re-checked under the
//! *real* hash before any bug is reported. This module is that real hash:
//! [`keccak256`] computes the actual EVM digest so the concrete interpreter can
//! confirm a keccak-dependent witness genuinely reproduces (DISAGREE = 0). A
//! witness whose bug depends on a specific hash *value* the solver invented (not
//! on key (dis)equality) simply will not reproduce here, and is therefore not
//! reported — never a false positive.
//!
//! Pure Rust, no `unsafe`, no C dependency (Hard Rule: the default build is
//! C-free). `Keccak-f[1600]` with the legacy (pre-NIST) `0x01` pad — i.e. the
//! Ethereum `keccak256`, *not* SHA3-256.

/// The 24 Keccak-f round constants.
const RC: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// Per-lane rotation offsets for the ρ step (row-major, lane `x + 5*y`).
const RHO: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// One `Keccak-f[1600]` permutation over the 5×5 lane state.
fn keccak_f(state: &mut [u64; 25]) {
    for &rc in &RC {
        // θ
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
        }
        let mut d = [0u64; 5];
        for x in 0..5 {
            d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        }
        for x in 0..5 {
            for y in 0..5 {
                state[x + 5 * y] ^= d[x];
            }
        }

        // ρ and π
        let mut b = [0u64; 25];
        for x in 0..5 {
            for y in 0..5 {
                let idx = x + 5 * y;
                let new = y + 5 * ((2 * x + 3 * y) % 5);
                b[new] = state[idx].rotate_left(RHO[idx]);
            }
        }

        // χ
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] =
                    b[x + 5 * y] ^ ((!b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y]);
            }
        }

        // ι
        state[0] ^= rc;
    }
}

/// The EVM `keccak256` digest (32 bytes) of `input`.
#[must_use]
pub fn keccak256(input: &[u8]) -> [u8; 32] {
    const RATE: usize = 136; // 1088-bit rate for keccak-256.
    let mut state = [0u64; 25];

    // Absorb full rate-sized blocks.
    let mut blocks = input.chunks_exact(RATE);
    for block in &mut blocks {
        absorb(&mut state, block);
        keccak_f(&mut state);
    }

    // Pad the final (partial) block: 0x01 ... 0x80 (keccak/legacy pad).
    let rem = blocks.remainder();
    let mut last = [0u8; RATE];
    last[..rem.len()].copy_from_slice(rem);
    last[rem.len()] ^= 0x01;
    last[RATE - 1] ^= 0x80;
    absorb(&mut state, &last);
    keccak_f(&mut state);

    // Squeeze 32 bytes (within the first rate block).
    let mut out = [0u8; 32];
    for (i, chunk) in out.chunks_mut(8).enumerate() {
        chunk.copy_from_slice(&state[i].to_le_bytes());
    }
    out
}

/// XORs `block` (≤ RATE bytes, little-endian lanes) into the state.
fn absorb(state: &mut [u64; 25], block: &[u8]) {
    for (i, lane) in block.chunks(8).enumerate() {
        let mut buf = [0u8; 8];
        buf[..lane.len()].copy_from_slice(lane);
        state[i] ^= u64::from_le_bytes(buf);
    }
}

#[cfg(test)]
mod tests {
    use super::keccak256;

    /// keccak256("") — the canonical empty-input EVM digest.
    #[test]
    fn empty_digest() {
        let h = keccak256(&[]);
        let expected = hex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");
        assert_eq!(h, expected);
    }

    /// keccak256("abc").
    #[test]
    fn abc_digest() {
        let h = keccak256(b"abc");
        let expected = hex("4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45");
        assert_eq!(h, expected);
    }

    /// keccak256 of a single zero byte.
    #[test]
    fn zero_byte_digest() {
        let h = keccak256(&[0u8]);
        let expected = hex("bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a");
        assert_eq!(h, expected);
    }

    fn hex(s: &str) -> [u8; 32] {
        let bytes = s.as_bytes();
        let mut out = [0u8; 32];
        for (i, b) in out.iter_mut().enumerate() {
            let hi = u8::try_from((bytes[2 * i] as char).to_digit(16).unwrap()).unwrap();
            let lo = u8::try_from((bytes[2 * i + 1] as char).to_digit(16).unwrap()).unwrap();
            *b = (hi << 4) | lo;
        }
        out
    }
}
