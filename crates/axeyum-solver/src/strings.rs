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
//! shape CBMC/Kani use): `len`, `=`, `at`, literals, `++`, `prefixof`, `contains`,
//! `suffixof`, `substr` (constant and symbolic start), `indexof`, lexicographic
//! `<`/`<=`, `take`/`drop`, equal-length `replace`, regex membership (`in_re`,
//! via a Thompson NFA simulated over the bounded positions), decimal
//! `to_int`/`from_int`, general-length `replace` (first occurrence, result in a
//! `2·max_len` sort), and `replace_all` (non-overlapping, left to right, result
//! in a `max_len²` sort). Unbounded strings (a first-class sequence sort and a
//! native solver) are the remaining frontier.

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

    /// `str.replace` — general length. Replaces the **first** occurrence of `old`
    /// in `x` with `new` (all in this sort), returning the result in a sort of
    /// size `2·max_len` (large enough for any splice: the kept bytes total
    /// `len(x) − len(old) ≤ max_len` plus up to `max_len` inserted bytes). If
    /// `old` does not occur, `x` is returned unchanged; if `old` is empty, `new`
    /// is prepended (SMT-LIB semantics — the empty string occurs first at 0).
    /// Requires `max_len ≤ 8`.
    ///
    /// Splice by masks and shifts (no per-byte ite-chain): with `idx` the first
    /// match offset, the result content is the low `idx` bytes of `x`, `or` `new`
    /// shifted to byte `idx`, `or` the tail `x[idx+len(old)..]` shifted to byte
    /// `idx+len(new)`; the length is `len(x) − len(old) + len(new)`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::InvalidWidth`] if `2·max_len > 16`, or [`IrError`] from
    /// the builders.
    #[allow(clippy::similar_names)]
    pub fn replace(
        &self,
        arena: &mut TermArena,
        x: &StrTerm,
        old: &StrTerm,
        new: &StrTerm,
    ) -> Result<(BoundedString, StrTerm), IrError> {
        let rmax = self.max_len * 2;
        if rmax > 16 {
            return Err(IrError::InvalidWidth(rmax * 8));
        }
        let result = BoundedString::new(rmax);
        let rcw = result.content_width();
        let rlw = result.len_width();
        let lw = self.len_width();
        let cw = self.content_width();

        let (found, idx) = self.index_of(arena, x, old, 0)?;

        // Byte-position shift amounts (·8), all widened to the result content width.
        let three = arena.bv_const(rcw, 3)?;
        let idx_c = arena.zero_ext(rcw - lw, idx)?;
        let idx_sh = arena.bv_shl(idx_c, three)?; // idx*8
        let oldlen_c = arena.zero_ext(rcw - lw, old.len)?;
        let oldend = arena.bv_add(idx_c, oldlen_c)?;
        let oldend_sh = arena.bv_shl(oldend, three)?; // (idx+len(old))*8
        let newlen_c = arena.zero_ext(rcw - lw, new.len)?;
        let newend = arena.bv_add(idx_c, newlen_c)?;
        let newend_sh = arena.bv_shl(newend, three)?; // (idx+len(new))*8

        let x_wide = arena.zero_ext(rcw - cw, x.content)?;
        let new_wide = arena.zero_ext(rcw - cw, new.content)?;
        let one = arena.bv_const(rcw, 1)?;

        // part1 = low idx bytes of x = x & (2^(idx*8) - 1)
        let powidx = arena.bv_shl(one, idx_sh)?;
        let maskidx = arena.bv_sub(powidx, one)?;
        let part1 = arena.bv_and(x_wide, maskidx)?;

        // part2 = new (masked to its len) shifted to byte idx
        let newlen_sh = arena.bv_shl(newlen_c, three)?;
        let pownew = arena.bv_shl(one, newlen_sh)?;
        let masknew = arena.bv_sub(pownew, one)?;
        let new_masked = arena.bv_and(new_wide, masknew)?;
        let part2 = arena.bv_shl(new_masked, idx_sh)?;

        // part3 = tail x[idx+len(old)..] shifted to byte idx+len(new)
        let after = arena.bv_lshr(x_wide, oldend_sh)?;
        let part3 = arena.bv_shl(after, newend_sh)?;

        let c12 = arena.bv_or(part1, part2)?;
        let spliced = arena.bv_or(c12, part3)?;
        let content = arena.ite(found, spliced, x_wide)?;

        // result length = found ? len(x) - len(old) + len(new) : len(x)
        let lenx_r = arena.zero_ext(rlw - lw, x.len)?;
        let oldlen_r = arena.zero_ext(rlw - lw, old.len)?;
        let newlen_r = arena.zero_ext(rlw - lw, new.len)?;
        let sub = arena.bv_sub(lenx_r, oldlen_r)?;
        let rep_len = arena.bv_add(sub, newlen_r)?;
        let len = arena.ite(found, rep_len, lenx_r)?;

        Ok((result, StrTerm { len, content }))
    }

    /// `str.replace_all` — replaces **all** non-overlapping occurrences of `old`
    /// in `x` with `new`, scanning left to right (greedy leftmost, matches do not
    /// overlap), in a sort of size `max_len²` (worst case: every byte starts a
    /// match of a length-1 `old` replaced by a length-`max_len` `new`). An empty
    /// `old` leaves `x` unchanged (SMT-LIB). Requires `max_len ≤ 4` (so
    /// `max_len² ≤ 16`).
    ///
    /// A single left-to-right pass carries a `skip` counter (bytes remaining in
    /// the current match, so inner offsets cannot re-match) and a symbolic output
    /// cursor `out_off`. At position `i`: if `old` matches and `skip = 0`, emit
    /// `new` and set `skip = len(old) − 1`; else if not skipping and `i < len(x)`,
    /// emit `x[i]`; the emitted chunk is shifted to `out_off·8` and `or`-ed in.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::InvalidWidth`] if `max_len² > 16`, or [`IrError`] from
    /// the builders.
    #[allow(clippy::similar_names, clippy::too_many_lines)]
    pub fn replace_all(
        &self,
        arena: &mut TermArena,
        x: &StrTerm,
        old: &StrTerm,
        new: &StrTerm,
    ) -> Result<(BoundedString, StrTerm), IrError> {
        let rmax = self.max_len * self.max_len;
        if rmax > 16 {
            return Err(IrError::InvalidWidth(rmax * 8));
        }
        let result = BoundedString::new(rmax);
        let rcw = result.content_width();
        let rlw = result.len_width();
        let lw = self.len_width();
        let cw = self.content_width();
        let sw = lw + 1; // skip counter width (holds 0..=max_len)
        let three = arena.bv_const(rcw, 3)?; // ·8

        // new masked to its low len(new)·8 bits, widened to the result width.
        let new_wide = arena.zero_ext(rcw - cw, new.content)?;
        let newlen_c = arena.zero_ext(rcw - lw, new.len)?;
        let newlen_sh = arena.bv_shl(newlen_c, three)?;
        let one_c = arena.bv_const(rcw, 1)?;
        let pownew = arena.bv_shl(one_c, newlen_sh)?;
        let masknew = arena.bv_sub(pownew, one_c)?;
        let new_masked = arena.bv_and(new_wide, masknew)?;
        let newlen_r = arena.zero_ext(rlw - lw, new.len)?;

        let zero_r = arena.bv_const(rlw, 0)?;
        let one_r = arena.bv_const(rlw, 1)?;
        let zero_rcw = arena.bv_const(rcw, 0)?;
        let zero_s = arena.bv_const(sw, 0)?;
        let one_s = arena.bv_const(sw, 1)?;

        let mut skip = zero_s;
        let mut out_off = zero_r;
        let mut content = zero_rcw;

        for i in 0..self.max_len {
            let match_i = self.match_at(arena, x, old, i, false)?;
            let skip_zero = arena.eq(skip, zero_s)?;
            let matched_here = arena.and(match_i, skip_zero)?;
            // emit a kept byte when not skipping, no match here, and i < len(x).
            let i_c = arena.bv_const(lw, u128::from(i))?;
            let i_lt_len = arena.bv_ult(i_c, x.len)?;
            let not_match = arena.not(match_i)?;
            let nb = arena.and(skip_zero, not_match)?;
            let emit_byte = arena.and(nb, i_lt_len)?;

            // chunk_len = matched_here ? len(new) : emit_byte ? 1 : 0
            let cl_eb = arena.ite(emit_byte, one_r, zero_r)?;
            let chunk_len = arena.ite(matched_here, newlen_r, cl_eb)?;

            // chunk content (right-aligned): new, or x[i], or nothing.
            let xbyte = arena.extract(i * 8 + 7, i * 8, x.content)?;
            let xbyte_w = arena.zero_ext(rcw - 8, xbyte)?;
            let chunk_eb = arena.ite(emit_byte, xbyte_w, zero_rcw)?;
            let chunk = arena.ite(matched_here, new_masked, chunk_eb)?;

            // place chunk at byte out_off.
            let out_off_c = arena.zero_ext(rcw - rlw, out_off)?;
            let out_sh = arena.bv_shl(out_off_c, three)?;
            let placed = arena.bv_shl(chunk, out_sh)?;
            content = arena.bv_or(content, placed)?;
            out_off = arena.bv_add(out_off, chunk_len)?;

            // advance skip: matched_here ? len(old)-1 : max(skip-1, 0)
            let oldlen_s = arena.zero_ext(sw - lw, old.len)?;
            let oldlen_m1 = arena.bv_sub(oldlen_s, one_s)?;
            let skip_pos = arena.bv_ugt(skip, zero_s)?;
            let skip_dec = arena.bv_sub(skip, one_s)?;
            let skip_else = arena.ite(skip_pos, skip_dec, zero_s)?;
            skip = arena.ite(matched_here, oldlen_m1, skip_else)?;
        }

        // empty old -> x unchanged (SMT-LIB).
        let zero_lw = arena.bv_const(lw, 0)?;
        let old_empty = arena.eq(old.len, zero_lw)?;
        let x_wide = arena.zero_ext(rcw - cw, x.content)?;
        let x_len_r = arena.zero_ext(rlw - lw, x.len)?;
        let final_content = arena.ite(old_empty, x_wide, content)?;
        let final_len = arena.ite(old_empty, x_len_r, out_off)?;

        Ok((result, StrTerm { len: final_len, content: final_content }))
    }

    /// `str.in_re` — does the bounded string `x` match the regular expression
    /// `re`? Compiles `re` to a Thompson NFA and simulates it symbolically over
    /// the `≤ max_len` positions (a per-position state set, char transitions
    /// gated by `pos < len`), accepting iff the accept state is active after
    /// exactly `len` consumed characters. Pure bit-vector/Boolean formula.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn in_re(&self, arena: &mut TermArena, x: &StrTerm, re: &Regex) -> Result<TermId, IrError> {
        let mut nfa = Nfa::default();
        let (start, accept) = nfa.build(re);
        let n = nfa.count;
        let reach = nfa.epsilon_closure();

        // active[s] = is NFA state s reachable after the chars consumed so far?
        // Initially: epsilon-closure of {start} (static).
        let mut active: Vec<TermId> = (0..n)
            .map(|s| arena.bool_const(reach[start][s]))
            .collect();

        // accepted iff at some point exactly `len` chars are consumed and the
        // accept state is active. Check after 0 chars, then after each position.
        let zero = arena.bv_const(self.len_width(), 0)?;
        let len_is_0 = arena.eq(x.len, zero)?;
        let mut accepted = arena.and(len_is_0, active[accept])?;

        for pos in 0..self.max_len {
            let ch = arena.extract(pos * 8 + 7, pos * 8, x.content)?;
            let pos_c = arena.bv_const(self.len_width(), u128::from(pos))?;
            let consume = arena.bv_ult(pos_c, x.len)?; // char at pos is within the string

            // char step: after[t] = OR over edges s--pred-->t of active[s] ∧ consume ∧ pred(ch)
            let mut after = vec![arena.bool_const(false); n];
            for &(s, t, ref pred) in &nfa.chars {
                let pmatch = pred.eval(arena, ch)?;
                let gated = arena.and(active[s], consume)?;
                let step = arena.and(gated, pmatch)?;
                after[t] = arena.or(after[t], step)?;
            }
            // epsilon closure: next[s'] = OR over t of after[t] ∧ reach[t][s']
            let mut next = vec![arena.bool_const(false); n];
            for (t, &a_t) in after.iter().enumerate() {
                for (sp, slot) in next.iter_mut().enumerate() {
                    if reach[t][sp] {
                        *slot = arena.or(*slot, a_t)?;
                    }
                }
            }
            active = next;

            // accept after pos+1 chars: len == pos+1 ∧ active[accept].
            let lenp = arena.bv_const(self.len_width(), u128::from(pos) + 1)?;
            let len_eq = arena.eq(x.len, lenp)?;
            let acc = arena.and(len_eq, active[accept])?;
            accepted = arena.or(accepted, acc)?;
        }
        Ok(accepted)
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

    /// `str.to_int` — decimal parse. Returns `(valid, value)`: `value` is a
    /// `BitVec(64)` holding the decimal number the string denotes, and `valid` is
    /// the Boolean "the string is a non-empty run of ASCII digits `'0'..='9'`".
    /// SMT-LIB `str.to_int` yields `-1` for a non-numeral; a caller wanting that
    /// convention can take `ite(valid, value, -1)`. 64 bits hold any value with
    /// `≤ 16` digits (`< 10^16 < 2^54`), so no overflow within the bound.
    ///
    /// Horner left-to-right (`value := value·10 + digit`) over the significant
    /// positions makes the result length-independent: padding bytes (`i ≥ len`)
    /// leave `value` unchanged.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn to_int(&self, arena: &mut TermArena, x: &StrTerm) -> Result<(TermId, TermId), IrError> {
        const W: u32 = 64;
        let ten = arena.bv_const(W, 10)?;
        let lo = arena.bv_const(8, u128::from(b'0'))?;
        let hi = arena.bv_const(8, u128::from(b'9'))?;
        let mut value = arena.bv_const(W, 0)?;
        let mut valid = arena.bool_const(true);
        for i in 0..self.max_len {
            let idx = arena.bv_const(self.len_width(), u128::from(i))?;
            let active = arena.bv_ult(idx, x.len)?;
            let byte = arena.extract(i * 8 + 7, i * 8, x.content)?;
            // is_digit: '0' <= byte <= '9'
            let ge = arena.bv_uge(byte, lo)?;
            let le = arena.bv_ule(byte, hi)?;
            let is_digit = arena.and(ge, le)?;
            // digit value = zero_extend(byte) - '0'
            let zpad = arena.bv_const(W - 8, 0)?;
            let byte_w = arena.concat(zpad, byte)?;
            let off = arena.bv_const(W, u128::from(b'0'))?;
            let digit = arena.bv_sub(byte_w, off)?;
            // stepped = value * 10 + digit
            let scaled = arena.bv_mul(value, ten)?;
            let stepped = arena.bv_add(scaled, digit)?;
            value = arena.ite(active, stepped, value)?;
            // valid &= (active -> is_digit)
            let imp = arena.implies(active, is_digit)?;
            valid = arena.and(valid, imp)?;
        }
        // a numeral is non-empty
        let zero_len = arena.bv_const(self.len_width(), 0)?;
        let is_empty = arena.eq(x.len, zero_len)?;
        let nonempty = arena.not(is_empty)?;
        valid = arena.and(valid, nonempty)?;
        Ok((valid, value))
    }

    /// `str.from_int` — decimal format. Given a bit-vector `n` (read as a
    /// non-negative integer), returns `(fits, s)` where `s` is the decimal string
    /// (no leading zeros, `"0"` for zero) and `fits` is the Boolean "the value
    /// needs at most `max_len` digits". When `fits` is false `s` is not the true
    /// rendering (the value is out of range), so callers should assert `fits`.
    ///
    /// Digits are peeled least-significant first by repeated `÷10`/`mod 10`; the
    /// significant length `k` is one past the highest nonzero digit (at least 1),
    /// and string byte `p` holds decimal place `k-1-p`, so the content is the
    /// digit sequence reversed into print order.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn from_int(&self, arena: &mut TermArena, n: TermId) -> Result<(TermId, StrTerm), IrError> {
        let n_sort = arena.sort_of(n);
        let w = n_sort.bv_width().ok_or(IrError::SortMismatch {
            expected: "BitVec",
            found: n_sort,
        })?;
        let ten = arena.bv_const(w, 10)?;
        let zero_w = arena.bv_const(w, 0)?;
        // Peel digits LSB-first: digit[j] in 0..=9 (8-bit), rem after j+1 divisions.
        let mut digits: Vec<TermId> = Vec::with_capacity(self.max_len as usize);
        let mut rem = n;
        for _ in 0..self.max_len {
            let d = arena.bv_urem(rem, ten)?;
            let d8 = arena.extract(7, 0, d)?;
            digits.push(d8);
            rem = arena.bv_udiv(rem, ten)?;
        }
        // fits iff the value is fully consumed within max_len digits.
        let fits = arena.eq(rem, zero_w)?;
        // Significant length k = 1 + highest j (>=1) with digit[j] != 0, else 1.
        let mut k = arena.bv_const(self.len_width(), 1)?;
        let zero8 = arena.bv_const(8, 0)?;
        for j in 1..self.max_len {
            let nonzero = {
                let is_zero = arena.eq(digits[j as usize], zero8)?;
                arena.not(is_zero)?
            };
            let jp1 = arena.bv_const(self.len_width(), u128::from(j + 1))?;
            k = arena.ite(nonzero, jp1, k)?;
        }
        // content byte p holds decimal place (k-1-p): select digit[k-1-p] when p<k.
        let off = arena.bv_const(8, u128::from(b'0'))?;
        let mut content = arena.bv_const(self.content_width(), 0)?;
        for p in 0..self.max_len {
            let pc = arena.bv_const(self.len_width(), u128::from(p))?;
            let active = arena.bv_ult(pc, k)?;
            // didx = k - 1 - p (only meaningful when active)
            let one = arena.bv_const(self.len_width(), 1)?;
            let km1 = arena.bv_sub(k, one)?;
            let didx = arena.bv_sub(km1, pc)?;
            // select digit[didx] by ite-chain over j
            let mut sel = zero8;
            for j in 0..self.max_len {
                let jc = arena.bv_const(self.len_width(), u128::from(j))?;
                let is_j = arena.eq(didx, jc)?;
                sel = arena.ite(is_j, digits[j as usize], sel)?;
            }
            let byte = arena.bv_add(sel, off)?;
            let placed = arena.ite(active, byte, zero8)?;
            // OR the byte into position p of content
            let widened = if self.content_width() > 8 {
                let zpad = arena.bv_const(self.content_width() - 8, 0)?;
                arena.concat(zpad, placed)?
            } else {
                placed
            };
            let shifted = {
                let amt = arena.bv_const(self.content_width(), u128::from(p) * 8)?;
                arena.bv_shl(widened, amt)?
            };
            content = arena.bv_or(content, shifted)?;
        }
        Ok((fits, StrTerm { len: k, content }))
    }
}

/// A regular expression over bytes for [`BoundedString::in_re`].
#[derive(Clone, Debug)]
pub enum Regex {
    /// Matches only the empty string.
    Empty,
    /// Matches a single specific byte.
    Char(u8),
    /// Matches any byte in `[lo, hi]` (inclusive).
    Range(u8, u8),
    /// Concatenation: `a` then `b`.
    Concat(Box<Regex>, Box<Regex>),
    /// Alternation: `a` or `b`.
    Union(Box<Regex>, Box<Regex>),
    /// Kleene star: zero or more repetitions of `a`.
    Star(Box<Regex>),
    /// Kleene plus: one or more repetitions of `a` (`re.+`).
    Plus(Box<Regex>),
    /// Option: zero or one `a` (`re.opt`).
    Opt(Box<Regex>),
    /// Any single byte (`re.allchar`, the regex `.`).
    AnyChar,
    /// Bounded repetition `a{n, m}` (`re.loop`): between `n` and `m` (inclusive)
    /// repetitions of `a`. If `n > m` the language is empty (matches nothing).
    Loop(Box<Regex>, u32, u32),
}

impl Regex {
    /// A literal multi-byte string regex (`Concat` of `Char`s; empty → `Empty`).
    #[must_use]
    pub fn literal(s: &str) -> Regex {
        let mut it = s.bytes().rev();
        match it.next() {
            None => Regex::Empty,
            Some(last) => {
                let mut acc = Regex::Char(last);
                for b in it {
                    acc = Regex::Concat(Box::new(Regex::Char(b)), Box::new(acc));
                }
                acc
            }
        }
    }
}

/// A byte predicate on an NFA character transition.
enum Pred {
    Eq(u8),
    Range(u8, u8),
}

impl Pred {
    fn eval(&self, arena: &mut TermArena, ch: TermId) -> Result<TermId, IrError> {
        match *self {
            Pred::Eq(c) => {
                let cc = arena.bv_const(8, u128::from(c))?;
                arena.eq(ch, cc)
            }
            Pred::Range(lo, hi) => {
                let lo_c = arena.bv_const(8, u128::from(lo))?;
                let hi_c = arena.bv_const(8, u128::from(hi))?;
                let ge = arena.bv_uge(ch, lo_c)?;
                let le = arena.bv_ule(ch, hi_c)?;
                arena.and(ge, le)
            }
        }
    }
}

/// A Thompson NFA: epsilon edges, predicate-labeled char edges, state count.
#[derive(Default)]
struct Nfa {
    eps: Vec<(usize, usize)>,
    chars: Vec<(usize, usize, Pred)>,
    count: usize,
}

impl Nfa {
    fn state(&mut self) -> usize {
        let s = self.count;
        self.count += 1;
        s
    }

    /// Builds the NFA fragment for `re`, returning its `(start, accept)` states.
    fn build(&mut self, re: &Regex) -> (usize, usize) {
        match re {
            Regex::Empty => {
                let s = self.state();
                let a = self.state();
                self.eps.push((s, a));
                (s, a)
            }
            Regex::Char(c) => {
                let s = self.state();
                let a = self.state();
                self.chars.push((s, a, Pred::Eq(*c)));
                (s, a)
            }
            Regex::Range(lo, hi) => {
                let s = self.state();
                let a = self.state();
                self.chars.push((s, a, Pred::Range(*lo, *hi)));
                (s, a)
            }
            Regex::Concat(x, y) => {
                let (xs, xa) = self.build(x);
                let (ys, ya) = self.build(y);
                self.eps.push((xa, ys));
                (xs, ya)
            }
            Regex::Union(x, y) => {
                let s = self.state();
                let a = self.state();
                let (xs, xa) = self.build(x);
                let (ys, ya) = self.build(y);
                self.eps.push((s, xs));
                self.eps.push((s, ys));
                self.eps.push((xa, a));
                self.eps.push((ya, a));
                (s, a)
            }
            Regex::Star(x) => {
                let s = self.state();
                let a = self.state();
                let (xs, xa) = self.build(x);
                self.eps.push((s, xs));
                self.eps.push((s, a));
                self.eps.push((xa, xs));
                self.eps.push((xa, a));
                (s, a)
            }
            Regex::Plus(x) => {
                // a+ = a a* : build a, then allow looping back through it.
                let (xs, xa) = self.build(x);
                self.eps.push((xa, xs));
                (xs, xa)
            }
            Regex::Opt(x) => {
                // a? = a | ε
                let s = self.state();
                let a = self.state();
                let (xs, xa) = self.build(x);
                self.eps.push((s, xs));
                self.eps.push((s, a));
                self.eps.push((xa, a));
                (s, a)
            }
            Regex::AnyChar => {
                let s = self.state();
                let a = self.state();
                self.chars.push((s, a, Pred::Range(0, 255)));
                (s, a)
            }
            Regex::Loop(x, n, m) => {
                if n > m {
                    // empty language: two disconnected states, accept unreachable.
                    let start = self.state();
                    let accept = self.state();
                    (start, accept)
                } else {
                    // a{n,m} = a^n (a?)^(m-n) : n mandatory then m-n optional copies.
                    let mut parts: Vec<Regex> = Vec::with_capacity(*m as usize);
                    for _ in 0..*n {
                        parts.push((**x).clone());
                    }
                    for _ in *n..*m {
                        parts.push(Regex::Opt(Box::new((**x).clone())));
                    }
                    let folded = parts.into_iter().rev().fold(None, |acc, p| match acc {
                        None => Some(p),
                        Some(rest) => Some(Regex::Concat(Box::new(p), Box::new(rest))),
                    });
                    self.build(&folded.unwrap_or(Regex::Empty))
                }
            }
        }
    }

    /// `reach[i][j]` = state `j` is reachable from `i` by epsilon edges (with
    /// `reach[i][i]` true). Transitive closure over the epsilon edges.
    fn epsilon_closure(&self) -> Vec<Vec<bool>> {
        let n = self.count;
        let mut reach = vec![vec![false; n]; n];
        for (i, row) in reach.iter_mut().enumerate() {
            row[i] = true;
        }
        for &(u, v) in &self.eps {
            reach[u][v] = true;
        }
        // Floyd–Warshall transitive closure.
        for k in 0..n {
            let row_k = reach[k].clone();
            for row in &mut reach {
                if row[k] {
                    for (dst, &src) in row.iter_mut().zip(row_k.iter()) {
                        *dst |= src;
                    }
                }
            }
        }
        reach
    }
}
