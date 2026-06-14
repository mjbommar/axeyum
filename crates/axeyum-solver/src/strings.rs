//! Bounded-length string theory by bit-vector lowering (no new IR sort), in the
//! style of the finite enum/record and FP helpers.
//!
//! A string of at most `max_len` bytes is a pair: a length `len` (a small
//! bit-vector) and a `content` bit-vector of `max_len · 8` bits, byte `i` in bits
//! `[8i, 8i+7]`. Only the first `len` bytes are significant; the rest are
//! padding (ignored by every operation, so a string has many bit-level
//! representations but one denotation). Operations build bit-vector/Boolean
//! formulas, so solving and model replay reuse the sound bit-vector path; queries
//! whose strings fit the bound are decided, and the bound caps `content` at the
//! 128-bit width (`max_len ≤ 16`).
//!
//! This is the bounded-model-checking fragment of the SMT string theory (the
//! shape CBMC/Kani use): `str.len`, `str.=`, `str.at`, and literals. Unbounded
//! strings and the shift-heavy operations (`str.++`/`substr`/`contains`/regex)
//! are future work.

use axeyum_ir::{IrError, Sort, TermArena, TermId};

/// A bounded string sort: byte strings of length `0..=max_len` (`max_len ≤ 16`,
/// so `content` stays within the 128-bit bit-vector cap).
#[derive(Clone, Copy, Debug)]
pub struct BoundedString {
    max_len: u32,
}

/// A bounded-string term: its length and its content bit-vector.
#[derive(Clone, Copy, Debug)]
pub struct StrTerm {
    /// Length, a `BitVec(len_width)` value in `0..=max_len`.
    pub len: TermId,
    /// Content, a `BitVec(max_len · 8)`; byte `i` is bits `[8i, 8i+7]`.
    pub content: TermId,
}

impl BoundedString {
    /// Creates a bounded-string sort for lengths `0..=max_len`.
    ///
    /// # Panics
    ///
    /// Panics if `max_len` is 0 or exceeds 16 (the `content` width would exceed
    /// the 128-bit bit-vector cap).
    #[must_use]
    pub fn new(max_len: u32) -> Self {
        assert!((1..=16).contains(&max_len), "bounded string max_len must be 1..=16");
        Self { max_len }
    }

    fn content_width(self) -> u32 {
        self.max_len * 8
    }

    fn len_width(self) -> u32 {
        // bits to hold 0..=max_len
        32 - (self.max_len).leading_zeros()
    }

    /// Declares a fresh string variable `(name_len, name_content)`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the IR builders (e.g. a name conflict).
    pub fn declare(&self, arena: &mut TermArena, name: &str) -> Result<StrTerm, IrError> {
        let len_sym = arena.declare(&format!("{name}!len"), Sort::BitVec(self.len_width()))?;
        let content_sym =
            arena.declare(&format!("{name}!content"), Sort::BitVec(self.content_width()))?;
        Ok(StrTerm {
            len: arena.var(len_sym),
            content: arena.var(content_sym),
        })
    }

    /// The well-formedness constraint `len ≤ max_len` to assert for a declared
    /// variable.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn well_formed(&self, arena: &mut TermArena, x: &StrTerm) -> Result<TermId, IrError> {
        let bound = arena.bv_const(self.len_width(), u128::from(self.max_len))?;
        arena.bv_ule(x.len, bound)
    }

    /// A string literal. The bytes must fit `max_len`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::InvalidWidth`] if the literal is longer than `max_len`,
    /// or [`IrError`] from the builders.
    pub fn literal(&self, arena: &mut TermArena, s: &str) -> Result<StrTerm, IrError> {
        let bytes = s.as_bytes();
        let n = u32::try_from(bytes.len()).unwrap_or(u32::MAX);
        if n > self.max_len {
            return Err(IrError::InvalidWidth(n));
        }
        let mut content: u128 = 0;
        for (i, &b) in bytes.iter().enumerate() {
            content |= u128::from(b) << (i * 8);
        }
        Ok(StrTerm {
            len: arena.bv_const(self.len_width(), u128::from(n))?,
            content: arena.bv_const(self.content_width(), content)?,
        })
    }

    /// `str.len` — the length term (a `BitVec(len_width)`).
    #[must_use]
    pub fn length(self, x: &StrTerm) -> TermId {
        x.len
    }

    /// `str.=` — string equality: equal lengths and equal bytes at every position
    /// below the length (padding ignored).
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn equal(&self, arena: &mut TermArena, x: &StrTerm, y: &StrTerm) -> Result<TermId, IrError> {
        let mut acc = arena.eq(x.len, y.len)?;
        for i in 0..self.max_len {
            // (i < len_x) → byte_x[i] == byte_y[i]
            let idx = arena.bv_const(self.len_width(), u128::from(i))?;
            let active = arena.bv_ult(idx, x.len)?;
            let bx = arena.extract(i * 8 + 7, i * 8, x.content)?;
            let by = arena.extract(i * 8 + 7, i * 8, y.content)?;
            let beq = arena.eq(bx, by)?;
            let nactive = arena.not(active)?;
            let implied = arena.or(nactive, beq)?;
            acc = arena.and(acc, implied)?;
        }
        Ok(acc)
    }

    /// `str.at` at a **constant** index: the byte at position `i` (an 8-bit
    /// `BitVec`), or `0` if `i` is at or beyond the length.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn char_at(&self, arena: &mut TermArena, x: &StrTerm, i: u32) -> Result<TermId, IrError> {
        if i >= self.max_len {
            return arena.bv_const(8, 0);
        }
        let idx = arena.bv_const(self.len_width(), u128::from(i))?;
        let active = arena.bv_ult(idx, x.len)?;
        let byte = arena.extract(i * 8 + 7, i * 8, x.content)?;
        let zero = arena.bv_const(8, 0)?;
        arena.ite(active, byte, zero)
    }
}
