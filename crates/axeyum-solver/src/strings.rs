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

    /// `str.++` — concatenation. Produces a result in a bounded-string sort of
    /// size `self.max_len + other.max_len` (so there is no overflow), placing
    /// `y`'s `other.max_len` bytes after `x`'s symbolic length. `x`'s padding is
    /// masked off first so it cannot corrupt the joined content.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::InvalidWidth`] if the combined length exceeds 16 (the
    /// 128-bit content cap), or [`IrError`] from the builders.
    #[allow(clippy::similar_names)] // len_x_r/len_y_r/len_x_c mirror the layout
    pub fn concat(
        &self,
        arena: &mut TermArena,
        x: &StrTerm,
        other: BoundedString,
        y: &StrTerm,
    ) -> Result<(BoundedString, StrTerm), IrError> {
        let rmax = self.max_len + other.max_len;
        if rmax > 16 {
            return Err(IrError::InvalidWidth(rmax * 8));
        }
        let result = BoundedString::new(rmax);
        let rcw = result.content_width();
        let rlw = result.len_width();

        // result length = len_x + len_y (widened to the result's len width).
        let len_x_r = arena.zero_ext(rlw - self.len_width(), x.len)?;
        let len_y_r = arena.zero_ext(rlw - other.len_width(), y.len)?;
        let rlen = arena.bv_add(len_x_r, len_y_r)?;

        // shift (in bits) for y = len_x * 8, in the result content width.
        let len_x_c = arena.zero_ext(rcw - self.len_width(), x.len)?;
        let three = arena.bv_const(rcw, 3)?; // *8
        let shift = arena.bv_shl(len_x_c, three)?;

        // mask x's content to its low len_x*8 bits (drop padding), widened.
        let one = arena.bv_const(rcw, 1)?;
        let pow = arena.bv_shl(one, shift)?; // 2^(len_x*8)
        let mask = arena.bv_sub(pow, one)?; // low len_x*8 ones
        let x_wide = arena.zero_ext(rcw - self.content_width(), x.content)?;
        let x_masked = arena.bv_and(x_wide, mask)?;

        // place y after x.
        let y_wide = arena.zero_ext(rcw - other.content_width(), y.content)?;
        let y_shifted = arena.bv_shl(y_wide, shift)?;
        let rcontent = arena.bv_or(x_masked, y_shifted)?;

        Ok((result, StrTerm { len: rlen, content: rcontent }))
    }

    /// `str.prefixof` — is `needle` a prefix of `hay`? (`needle`, `hay` in this
    /// sort.) `len(needle) ≤ len(hay)` and the first `len(needle)` bytes agree.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn prefix_of(
        &self,
        arena: &mut TermArena,
        needle: &StrTerm,
        hay: &StrTerm,
    ) -> Result<TermId, IrError> {
        let mut acc = arena.bv_ule(needle.len, hay.len)?;
        for i in 0..self.max_len {
            let idx = arena.bv_const(self.len_width(), u128::from(i))?;
            let active = arena.bv_ult(idx, needle.len)?;
            let nb = arena.extract(i * 8 + 7, i * 8, needle.content)?;
            let hb = arena.extract(i * 8 + 7, i * 8, hay.content)?;
            let beq = arena.eq(nb, hb)?;
            let nactive = arena.not(active)?;
            let implied = arena.or(nactive, beq)?;
            acc = arena.and(acc, implied)?;
        }
        Ok(acc)
    }

    /// `str.contains` — does `hay` contain `needle` as a (contiguous) substring?
    /// A bounded scan: `needle` matches at *some* offset whose window fits within
    /// `len(hay)`. (Both strings in this sort.)
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn contains(
        &self,
        arena: &mut TermArena,
        hay: &StrTerm,
        needle: &StrTerm,
    ) -> Result<TermId, IrError> {
        self.scan_match(arena, hay, needle, false)
    }

    /// `str.suffixof` — is `needle` a suffix of `hay`? Like [`Self::contains`] but
    /// the match window must end exactly at `len(hay)`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn suffix_of(
        &self,
        arena: &mut TermArena,
        needle: &StrTerm,
        hay: &StrTerm,
    ) -> Result<TermId, IrError> {
        self.scan_match(arena, hay, needle, true)
    }

    /// Shared bounded substring scan: `needle` matches at some offset whose
    /// window either ends at or fits within `len(hay)` (`exact_end` selects
    /// suffix vs substring).
    #[allow(clippy::trivially_copy_pass_by_ref)] // mirror the public API shape
    fn scan_match(
        &self,
        arena: &mut TermArena,
        hay: &StrTerm,
        needle: &StrTerm,
        exact_end: bool,
    ) -> Result<TermId, IrError> {
        let mut any = arena.bool_const(false);
        for off in 0..self.max_len {
            let matched = self.match_at(arena, hay, needle, off, exact_end)?;
            any = arena.or(any, matched)?;
        }
        Ok(any)
    }

    /// Whether `needle` matches `hay` at the constant offset `off`: the window
    /// fits (or ends exactly at `len(hay)`) and the bytes agree position-by-
    /// position. The single-offset building block of the scan and of `indexof`.
    #[allow(clippy::similar_names, clippy::trivially_copy_pass_by_ref)]
    fn match_at(
        &self,
        arena: &mut TermArena,
        hay: &StrTerm,
        needle: &StrTerm,
        off: u32,
        exact_end: bool,
    ) -> Result<TermId, IrError> {
        let wide = self.len_width() + 1; // room for off + len(needle)
        let len_h = arena.zero_ext(1, hay.len)?;
        let len_n = arena.zero_ext(1, needle.len)?;
        let off_c = arena.bv_const(wide, u128::from(off))?;
        let end = arena.bv_add(off_c, len_n)?;
        let mut matched = if exact_end {
            arena.eq(end, len_h)?
        } else {
            arena.bv_ule(end, len_h)?
        };
        for j in 0..self.max_len {
            let jc = arena.bv_const(self.len_width(), u128::from(j))?;
            let j_active = arena.bv_ult(jc, needle.len)?;
            let nj_active = arena.not(j_active)?;
            if off + j >= self.max_len {
                matched = arena.and(matched, nj_active)?;
            } else {
                let hb = arena.extract((off + j) * 8 + 7, (off + j) * 8, hay.content)?;
                let nb = arena.extract(j * 8 + 7, j * 8, needle.content)?;
                let beq = arena.eq(hb, nb)?;
                let implied = arena.or(nj_active, beq)?;
                matched = arena.and(matched, implied)?;
            }
        }
        Ok(matched)
    }

    /// `str.indexof` from a **constant** start: returns `(found, index)` where
    /// `found` is whether `needle` occurs at some offset `≥ from`, and `index` is
    /// the smallest such offset (a `BitVec(len_width)`, meaningful when `found`).
    /// Avoids the SMT `-1` sentinel by reporting `found` separately.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub fn index_of(
        &self,
        arena: &mut TermArena,
        hay: &StrTerm,
        needle: &StrTerm,
        from: u32,
    ) -> Result<(TermId, TermId), IrError> {
        let mut found = arena.bool_const(false);
        let mut index = arena.bv_const(self.len_width(), 0)?;
        // Process offsets high → low so the *smallest* matching offset wins.
        for off in (from..self.max_len).rev() {
            let m = self.match_at(arena, hay, needle, off, false)?;
            found = arena.or(found, m)?;
            let off_c = arena.bv_const(self.len_width(), u128::from(off))?;
            index = arena.ite(m, off_c, index)?;
        }
        Ok((found, index))
    }

    /// `str.substr` with a **constant** start and length `n`: the substring of
    /// `x` at `[start, start+n)`, in a bounded-string sort of size `n`. The
    /// content is the `n` source bytes (padding beyond the actual length is
    /// don't-care); the result length is `min(n, len(x) − start)` clamped to 0
    /// when `start ≥ len(x)`, matching SMT-LIB `str.substr`. Requires
    /// `start + n ≤ max_len` and `n ≥ 1`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::InvalidWidth`] if the window is out of range or `n = 0`,
    /// or [`IrError`] from the builders.
    pub fn substr(
        &self,
        arena: &mut TermArena,
        x: &StrTerm,
        start: u32,
        n: u32,
    ) -> Result<(BoundedString, StrTerm), IrError> {
        if n == 0 || start + n > self.max_len {
            return Err(IrError::InvalidWidth(n));
        }
        let result = BoundedString::new(n);
        // content = source bytes [start, start+n).
        let content = arena.extract((start + n) * 8 - 1, start * 8, x.content)?;
        // actual length = start >= len(x) ? 0 : min(n, len(x) - start).
        let lw = self.len_width();
        let start_c = arena.bv_const(lw, u128::from(start))?;
        let n_c = arena.bv_const(lw, u128::from(n))?;
        let zero = arena.bv_const(lw, 0)?;
        let start_ge = arena.bv_uge(start_c, x.len)?;
        let avail = arena.bv_sub(x.len, start_c)?; // valid when start < len(x)
        let avail_lt_n = arena.bv_ult(avail, n_c)?;
        let min_an = arena.ite(avail_lt_n, avail, n_c)?;
        let actual = arena.ite(start_ge, zero, min_an)?;
        let rlen = arena.extract(result.len_width() - 1, 0, actual)?;
        Ok((result, StrTerm { len: rlen, content }))
    }

    /// `str.substr` with a **symbolic** start and constant length `n`: the
    /// substring of `x` at `[start, start+n)`, in a bounded-string sort of size
    /// `n`. Content is `x` right-shifted by `start·8` bytes (variable shift),
    /// truncated to `n` bytes; length is `min(n, len(x) − start)` clamped to 0
    /// when `start ≥ len(x)`. Requires `n ≤ self.max_len` and `n ≥ 1`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::InvalidWidth`] if `n` is out of range, or [`IrError`]
    /// from the builders.
    pub fn substr_at(
        &self,
        arena: &mut TermArena,
        x: &StrTerm,
        start: TermId,
        n: u32,
    ) -> Result<(BoundedString, StrTerm), IrError> {
        if n == 0 || n > self.max_len {
            return Err(IrError::InvalidWidth(n));
        }
        let result = BoundedString::new(n);
        let cw = self.content_width();
        let lw = self.len_width();
        // shift x right by start*8 bits, then take the low n bytes.
        let start_c = arena.zero_ext(cw - lw, start)?;
        let three = arena.bv_const(cw, 3)?; // *8
        let shift = arena.bv_shl(start_c, three)?;
        let shifted = arena.bv_lshr(x.content, shift)?;
        let content = arena.extract(n * 8 - 1, 0, shifted)?;
        // actual length = start >= len(x) ? 0 : min(n, len(x) - start).
        let n_c = arena.bv_const(lw, u128::from(n))?;
        let zero = arena.bv_const(lw, 0)?;
        let start_ge = arena.bv_uge(start, x.len)?;
        let avail = arena.bv_sub(x.len, start)?;
        let avail_lt_n = arena.bv_ult(avail, n_c)?;
        let min_an = arena.ite(avail_lt_n, avail, n_c)?;
        let actual = arena.ite(start_ge, zero, min_an)?;
        let rlen = arena.extract(result.len_width() - 1, 0, actual)?;
        Ok((result, StrTerm { len: rlen, content }))
    }

    /// `str.<` — strict lexicographic order: `x < y` iff at the first differing
    /// position `x`'s byte is smaller, or `x` is a proper prefix of `y`. A
    /// bounded left-to-right scan tracking "equal so far".
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    #[allow(clippy::similar_names)]
    pub fn less(&self, arena: &mut TermArena, x: &StrTerm, y: &StrTerm) -> Result<TermId, IrError> {
        let mut prefix_eq = arena.bool_const(true); // positions < i present in both and equal
        let mut lt = arena.bool_const(false);
        for i in 0..self.max_len {
            let idx = arena.bv_const(self.len_width(), u128::from(i))?;
            let i_lt_lx = arena.bv_ult(idx, x.len)?;
            let i_lt_ly = arena.bv_ult(idx, y.len)?;
            let bx = arena.extract(i * 8 + 7, i * 8, x.content)?;
            let by = arena.extract(i * 8 + 7, i * 8, y.content)?;
            // case A: x ends exactly at i and y has more → x is a proper prefix.
            let lx_eq_i = arena.eq(x.len, idx)?;
            let case_a = arena.and(lx_eq_i, i_lt_ly)?;
            // case B: both have byte i and x[i] < y[i].
            let both = arena.and(i_lt_lx, i_lt_ly)?;
            let bx_lt = arena.bv_ult(bx, by)?;
            let case_b = arena.and(both, bx_lt)?;
            let here = arena.or(case_a, case_b)?;
            let decided = arena.and(prefix_eq, here)?;
            lt = arena.or(lt, decided)?;
            // advance the common-prefix flag.
            let beq = arena.eq(bx, by)?;
            let still = arena.and(both, beq)?;
            prefix_eq = arena.and(prefix_eq, still)?;
        }
        Ok(lt)
    }

    /// `str.<=` — `x < y ∨ x = y`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn less_equal(
        &self,
        arena: &mut TermArena,
        x: &StrTerm,
        y: &StrTerm,
    ) -> Result<TermId, IrError> {
        let lt = self.less(arena, x, y)?;
        let eq = self.equal(arena, x, y)?;
        arena.or(lt, eq)
    }

    /// `take` — the prefix of the first `k` bytes (`k` symbolic): content masked
    /// to its low `k·8` bits, length `min(k, len(x))`. Same sort as `x`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn take(&self, arena: &mut TermArena, x: &StrTerm, k: TermId) -> Result<StrTerm, IrError> {
        let cw = self.content_width();
        let lw = self.len_width();
        let k_c = arena.zero_ext(cw - lw, k)?;
        let three = arena.bv_const(cw, 3)?;
        let shift = arena.bv_shl(k_c, three)?; // k*8
        let one = arena.bv_const(cw, 1)?;
        let pow = arena.bv_shl(one, shift)?; // 2^(k*8) (0 if k*8 >= cw → take all)
        let mask = arena.bv_sub(pow, one)?;
        let content = arena.bv_and(x.content, mask)?;
        let k_lt_len = arena.bv_ult(k, x.len)?;
        let len = arena.ite(k_lt_len, k, x.len)?;
        Ok(StrTerm { len, content })
    }

    /// `drop` — the suffix after the first `k` bytes (`k` symbolic): content
    /// right-shifted by `k·8` bits, length `max(0, len(x) − k)`. Same sort as `x`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn drop(&self, arena: &mut TermArena, x: &StrTerm, k: TermId) -> Result<StrTerm, IrError> {
        let cw = self.content_width();
        let lw = self.len_width();
        let k_c = arena.zero_ext(cw - lw, k)?;
        let three = arena.bv_const(cw, 3)?;
        let shift = arena.bv_shl(k_c, three)?;
        let content = arena.bv_lshr(x.content, shift)?;
        let zero = arena.bv_const(lw, 0)?;
        let k_ge_len = arena.bv_uge(k, x.len)?;
        let avail = arena.bv_sub(x.len, k)?;
        let len = arena.ite(k_ge_len, zero, avail)?;
        Ok(StrTerm { len, content })
    }

    /// `str.replace` for the **equal-length** case: replaces the first occurrence
    /// of `old` in `x` with `new`, assuming `len(old) = len(new)` (so the result
    /// length is unchanged — fixed-width/char replacement). If `old` does not
    /// occur, `x` is returned unchanged. The caller must ensure `len(old) =
    /// len(new)` (assert it, or use equal-length literals); otherwise the result
    /// is only correct on the common bytes.
    ///
    /// Built per position (no sort growth): result byte `p` is `new[p − idx]` when
    /// `p` is in the matched window `[idx, idx + len(old))`, else `x[p]`, where
    /// `idx` is the first match offset.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    #[allow(clippy::similar_names)]
    pub fn replace_same_len(
        &self,
        arena: &mut TermArena,
        x: &StrTerm,
        old: &StrTerm,
        new: &StrTerm,
    ) -> Result<StrTerm, IrError> {
        let (found, idx) = self.index_of(arena, x, old, 0)?;
        let lw = self.len_width();
        let cw = self.content_width();
        let mut content = arena.bv_const(cw, 0)?;
        for p in 0..self.max_len {
            let p_c = arena.bv_const(lw, u128::from(p))?;
            let off = arena.bv_sub(p_c, idx)?; // p - idx (wraps if idx > p)
            let in_window = arena.bv_ult(off, old.len)?;
            let in_region = arena.and(found, in_window)?;
            // new[off]: select new's byte at the (symbolic) offset.
            let mut nb = arena.bv_const(8, 0)?;
            for k in 0..self.max_len {
                let k_c = arena.bv_const(lw, u128::from(k))?;
                let sel = arena.eq(off, k_c)?;
                let newk = arena.extract(k * 8 + 7, k * 8, new.content)?;
                nb = arena.ite(sel, newk, nb)?;
            }
            let sb = arena.extract(p * 8 + 7, p * 8, x.content)?;
            let rbyte = arena.ite(in_region, nb, sb)?;
            // place rbyte at position p.
            let rbyte_w = arena.zero_ext(cw - 8, rbyte)?;
            let shift = arena.bv_const(cw, u128::from(p) * 8)?;
            let placed = arena.bv_shl(rbyte_w, shift)?;
            content = arena.bv_or(content, placed)?;
        }
        Ok(StrTerm { len: x.len, content })
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
