//! Bounded bit-blasting of linear integer arithmetic (`QF_LIA`) to `QF_BV`
//! (ADR-0014).
//!
//! Each integer variable becomes a fresh width-`B` bit-vector (two's
//! complement), integer constants become width-`B` bit-vector constants, and
//! the linear integer operators map to their signed bit-vector counterparts:
//!
//! | integer op | bit-vector op |
//! |---|---|
//! | `int_add`/`int_sub`/`int_neg`/`int_mul` | `bvadd`/`bvsub`/`bvneg`/`bvmul` |
//! | `int_lt`/`int_le`/`int_gt`/`int_ge` | `bvslt`/`bvsle`/`bvsgt`/`bvsge` |
//!
//! The result is pure `QF_BV`, decided by the existing pipeline. **The encoding
//! is only sound for `sat` after replay:** bit-vector arithmetic wraps at width
//! `B`, so a bit-vector model can satisfy the wrapped constraints while the true
//! integers (read back from the model) overflow. The caller must interpret the
//! bit-vector model as signed integers and re-check the *original* integer
//! assertions with the exact evaluator — [`IntBlasting::integer_model`] builds
//! that integer assignment. A bit-vector `unsat` means only "no model in the
//! bounded range", which is `unknown` for the integer problem, never `unsat`.

use std::collections::HashMap;

use axeyum_ir::{Assignment, IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value};

use crate::canonical::build_app;

/// The largest bit-width the bounded blaster accepts, so signed values stay
/// within the `i128` reference range used for model read-back.
pub const MAX_INT_BLAST_WIDTH: u32 = 64;

/// Error from integer bit-blasting.
#[derive(Debug, Clone)]
pub enum IntBlastError {
    /// An integer constant does not fit in signed width-`B` (the chosen bound is
    /// too small); the caller should treat this as `unknown`.
    ConstantOutOfRange {
        /// The offending constant.
        value: i128,
        /// The chosen bit-width.
        width: u32,
    },
    /// The requested width is zero or exceeds [`MAX_INT_BLAST_WIDTH`].
    InvalidWidth(u32),
    /// An IR builder error while constructing replacement terms.
    Ir(IrError),
}

impl core::fmt::Display for IntBlastError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            IntBlastError::ConstantOutOfRange { value, width } => {
                write!(
                    f,
                    "integer constant {value} does not fit in signed {width} bits"
                )
            }
            IntBlastError::InvalidWidth(width) => {
                write!(f, "invalid integer bit-blast width {width}")
            }
            IntBlastError::Ir(error) => write!(f, "integer bit-blast IR error: {error}"),
        }
    }
}

impl core::error::Error for IntBlastError {}

impl From<IrError> for IntBlastError {
    fn from(error: IrError) -> Self {
        IntBlastError::Ir(error)
    }
}

/// Result of bit-blasting integers from a set of assertions.
#[derive(Debug, Clone)]
pub struct IntBlasting {
    assertions: Vec<TermId>,
    width: u32,
    /// `(original integer symbol, fresh bit-vector symbol)` pairs.
    vars: Vec<(SymbolId, SymbolId)>,
    had_integers: bool,
    /// Number of no-overflow (faithful-product) side-constraints conjoined onto
    /// the assertions — one per integer product bit-blasted at this width. These
    /// are *restricting* guards: they prune wrapping models so the bounded search
    /// finds the genuine witness for `sat`, but they also strengthen the formula,
    /// so a refutation of the guarded query does NOT refute the original. Any
    /// proof-/`unsat`-emitting consumer must treat a non-zero count as a reason to
    /// stay inconclusive (see `restricting_constraints`).
    restricting_constraints: usize,
}

impl IntBlasting {
    /// The pure-`QF_BV` assertions.
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// Whether the input actually contained any integer constructs.
    pub fn had_integers(&self) -> bool {
        self.had_integers
    }

    /// The bit-width used for the bounded encoding.
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Number of no-overflow side-constraints conjoined onto the blasted
    /// assertions (one per integer product). A non-zero count means the blasted
    /// query is a **strict restriction** of the original: it is sound to read a
    /// model back for `sat` (replay re-checks the originals), but a bit-vector
    /// `unsat` of the guarded query does NOT establish `unsat` of the original —
    /// so any proof export / `unsat`-emitting path must decline (stay
    /// `Inconclusive`/`Unknown`) when this is non-zero.
    pub fn restricting_constraints(&self) -> usize {
        self.restricting_constraints
    }

    /// Reads a bit-vector model back into an integer assignment over the
    /// *original* integer symbols, interpreting each fresh bit-vector value as a
    /// signed (two's complement) integer. Non-integer bindings in `model` are
    /// preserved.
    ///
    /// # Panics
    ///
    /// Panics if a fresh bit-vector symbol is unassigned or non-bit-vector,
    /// which cannot happen for a model returned by a backend that solved the
    /// blasted assertions.
    pub fn integer_model(&self, model: &Assignment) -> Assignment {
        let mut out = model.clone();
        for &(int_sym, bv_sym) in &self.vars {
            let (width, raw) = model
                .get(bv_sym)
                .expect("fresh bit-vector symbol is assigned")
                .as_bv()
                .expect("fresh symbol is bit-vector sorted");
            out.set(int_sym, Value::Int(to_signed(width, raw)));
        }
        out
    }
}

/// Bit-blasts all integer constructs in `assertions` to `QF_BV` at width
/// `width`, returning equisatisfiable-in-range pure-`QF_BV` assertions plus the
/// variable map needed to read a model back as integers.
///
/// If no assertion contains integers, the assertions are returned unchanged.
///
/// # Errors
///
/// Returns [`IntBlastError::InvalidWidth`] for a bad width,
/// [`IntBlastError::ConstantOutOfRange`] if a constant does not fit the bound,
/// or an internal IR builder error.
pub fn blast_integers(
    arena: &mut TermArena,
    assertions: &[TermId],
    width: u32,
) -> Result<IntBlasting, IntBlastError> {
    if width == 0 || width > MAX_INT_BLAST_WIDTH {
        return Err(IntBlastError::InvalidWidth(width));
    }
    let had_integers = assertions.iter().any(|&term| contains_integer(arena, term));
    if !had_integers {
        return Ok(IntBlasting {
            assertions: assertions.to_vec(),
            width,
            vars: Vec::new(),
            had_integers: false,
            restricting_constraints: 0,
        });
    }

    let mut ctx = Blaster {
        width,
        ..Blaster::default()
    };
    let mut rewritten = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        rewritten.push(ctx.rewrite(arena, assertion)?);
    }

    // No-overflow side-constraints for every integer product bit-blasted at width
    // `B`. Each is a *restriction* that forces the SAT search onto a NON-WRAPPING
    // (faithful) model of `a * b`, so the bounded blast finds the genuine small
    // witness instead of a spurious mod-2^B wrapping one (which replay rejects).
    // Conjoining them with the rewritten assertions keeps the result a pure
    // conjunction; see `mul_no_overflow_constraint` for the encoding and the
    // soundness note (replay remains the anchor; UNSAT-with-constraint only widens
    // via the ladder, never an `unsat`).
    let restricting_constraints = ctx.mul_constraints.len();
    rewritten.extend(ctx.mul_constraints);

    Ok(IntBlasting {
        assertions: rewritten,
        width,
        vars: ctx.vars,
        had_integers: true,
        restricting_constraints,
    })
}

#[derive(Default)]
struct Blaster {
    width: u32,
    term_memo: HashMap<TermId, TermId>,
    symbol_memo: HashMap<SymbolId, SymbolId>,
    vars: Vec<(SymbolId, SymbolId)>,
    fresh_counter: usize,
    /// No-overflow side-constraints accumulated for each integer product (one
    /// `bool` term per `int_mul`); conjoined with the rewritten assertions.
    mul_constraints: Vec<TermId>,
}

impl Blaster {
    fn rewrite(&mut self, arena: &mut TermArena, term: TermId) -> Result<TermId, IntBlastError> {
        if let Some(&cached) = self.term_memo.get(&term) {
            return Ok(cached);
        }
        let node = arena.node(term).clone();
        let result = match node {
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::RealConst(_) => term,
            TermNode::IntConst(value) => self.encode_constant(arena, value)?,
            TermNode::Symbol(symbol) => {
                if arena.sort_of(term) == Sort::Int {
                    let bv_sym = self.blast_symbol(arena, symbol)?;
                    arena.var(bv_sym)
                } else {
                    term
                }
            }
            // Coercions bridge the BV and (width-`B`) integer encodings; they
            // need the blast width, so they are handled here, not in the static
            // `build_int_app`.
            TermNode::App {
                op: Op::Bv2Nat,
                args,
            } => {
                let bv = self.rewrite(arena, args[0])?; // BV passthrough (width w)
                let Sort::BitVec(w) = arena.sort_of(bv) else {
                    return Err(IntBlastError::Ir(IrError::SortMismatch {
                        expected: "BitVec",
                        found: arena.sort_of(bv),
                    }));
                };
                // Reinterpret the unsigned BV value in the signed width-`B`
                // encoding: zero-extend when `B > w` (stays non-negative); when
                // `B <= w` the high bits are dropped (bounded — replay-checked).
                match w.cmp(&self.width) {
                    core::cmp::Ordering::Less => arena.zero_ext(self.width - w, bv)?,
                    core::cmp::Ordering::Equal => bv,
                    core::cmp::Ordering::Greater => arena.extract(self.width - 1, 0, bv)?,
                }
            }
            TermNode::App {
                op: Op::Int2Bv { width },
                args,
            } => {
                let x = self.rewrite(arena, args[0])?; // Int → width-`B` BV
                // x mod 2^width = low `width` bits of x's two's complement; when
                // `width > B`, sign-extend (preserves the modular value).
                match width.cmp(&self.width) {
                    core::cmp::Ordering::Less | core::cmp::Ordering::Equal => {
                        arena.extract(width - 1, 0, x)?
                    }
                    core::cmp::Ordering::Greater => arena.sign_ext(width - self.width, x)?,
                }
            }
            TermNode::App {
                op: Op::IntMul,
                args,
            } => {
                // Lower both factors, then form the width-`B` product *and* a
                // no-overflow side-constraint that ties it to the true (non-wrapping)
                // integer product. The constraint is recorded for conjunction; the
                // node value remains the plain width-`B` `bvmul` so the rest of the
                // rewrite (and the existing replay) is unchanged.
                let a = self.rewrite(arena, args[0])?;
                let b = self.rewrite(arena, args[1])?;
                let product = arena.bv_mul(a, b)?;
                let constraint = self.mul_no_overflow_constraint(arena, a, b, product)?;
                self.mul_constraints.push(constraint);
                product
            }
            TermNode::App { op, args } => {
                let mut lowered = Vec::with_capacity(args.len());
                for &arg in &args {
                    lowered.push(self.rewrite(arena, arg)?);
                }
                Self::build_int_app(arena, op, &lowered)?
            }
        };
        self.term_memo.insert(term, result);
        Ok(result)
    }

    /// A zero bit-vector constant of the same width as `t`.
    fn bv_zero_like(arena: &mut TermArena, t: TermId) -> Result<TermId, IntBlastError> {
        let Sort::BitVec(w) = arena.sort_of(t) else {
            return Err(IntBlastError::Ir(IrError::SortMismatch {
                expected: "BitVec",
                found: arena.sort_of(t),
            }));
        };
        Ok(arena.bv_const(w, 0)?)
    }

    /// Builds the **faithful-product (no-overflow) side-constraint** for an
    /// integer product `a * b` whose width-`B` two's-complement value is
    /// `product` (`= bvmul(a, b)`, both width `B`).
    ///
    /// The true signed product of two `B`-bit values fits in `2B` bits, so we
    /// recompute it exactly there — sign-extend each factor to `2B` and multiply
    /// — and demand that it equal the sign-extension of the width-`B` `product`.
    /// That holds iff the integer product `a * b` fits in signed `B` bits, i.e.
    /// the width-`B` `bvmul` did NOT wrap. Adding this as a conjunct forces the
    /// SAT search onto a non-wrapping (faithful) model — exactly the genuine
    /// small witness for tiny-witness `QF_NIA` queries.
    ///
    /// Soundness: this is a *restriction* at width `B`. A model that satisfies it
    /// has `a * b` equal over the integers to its width-`B` encoding, so the
    /// existing exact-integer replay (the soundness anchor in `lia.rs` /
    /// `combined.rs`) still independently re-checks every original assertion — a
    /// mis-encoded constraint could only make the search MISS a model (→ a
    /// wider width via the ladder, or a sound `Unknown`), never accept a wrong
    /// `Sat`. When the width-`B` solve is UNSAT *with* this constraint, the width
    /// ladder simply widens (a genuine large-product witness is found at a larger
    /// `B`); an exhausted ladder stays `Unknown`, never `Unsat`.
    fn mul_no_overflow_constraint(
        &self,
        arena: &mut TermArena,
        a: TermId,
        b: TermId,
        product: TermId,
    ) -> Result<TermId, IntBlastError> {
        let width = self.width;
        // True signed product in `2*width` bits (cannot itself overflow there).
        let a_wide = arena.sign_ext(width, a)?;
        let b_wide = arena.sign_ext(width, b)?;
        let true_product = arena.bv_mul(a_wide, b_wide)?;
        // Sign-extend the width-`B` result to `2*width`; equality with the true
        // product is exactly "the product fits in signed `B` bits".
        let product_wide = arena.sign_ext(width, product)?;
        Ok(arena.eq(product_wide, true_product)?)
    }

    fn build_int_app(
        arena: &mut TermArena,
        op: Op,
        args: &[TermId],
    ) -> Result<TermId, IntBlastError> {
        let term = match op {
            Op::IntNeg => arena.bv_neg(args[0])?,
            Op::IntAdd => arena.bv_add(args[0], args[1])?,
            Op::IntSub => arena.bv_sub(args[0], args[1])?,
            Op::IntMul => arena.bv_mul(args[0], args[1])?,
            // Euclidean div/mod on the two's-complement encoding. From the
            // truncated remainder `rt = bvsrem(a,b)` (sign of `a`), the Euclidean
            // remainder is `rt + |b|` when `rt < 0`, else `rt` (always in
            // `0..|b|`); the quotient is then `(a − r) bvsdiv b`, exact since
            // `a − r` is a multiple of `b`. SMT-LIB BV totality gives the right
            // `b = 0` behaviour for `mod` (`bvsrem a 0 = a` ⇒ `mod = a`); `div`
            // is forced to `0` to match the in-tree `div a 0 = 0` convention.
            Op::IntAbs => {
                let zero = Self::bv_zero_like(arena, args[0])?;
                let neg = arena.bv_neg(args[0])?;
                let is_neg = arena.bv_slt(args[0], zero)?;
                arena.ite(is_neg, neg, args[0])?
            }
            Op::IntDiv | Op::IntMod => {
                let (a, b) = (args[0], args[1]);
                let zero = Self::bv_zero_like(arena, a)?;
                let rt = arena.bv_srem(a, b)?;
                let b_neg = arena.bv_slt(b, zero)?;
                let neg_b = arena.bv_neg(b)?;
                let abs_b = arena.ite(b_neg, neg_b, b)?;
                let rt_neg = arena.bv_slt(rt, zero)?;
                let rt_plus = arena.bv_add(rt, abs_b)?;
                let r_eucl = arena.ite(rt_neg, rt_plus, rt)?;
                if op == Op::IntMod {
                    r_eucl
                } else {
                    let diff = arena.bv_sub(a, r_eucl)?;
                    let q = arena.bv_sdiv(diff, b)?;
                    let b_zero = arena.eq(b, zero)?;
                    arena.ite(b_zero, zero, q)?
                }
            }
            Op::IntLt => arena.bv_slt(args[0], args[1])?,
            Op::IntLe => arena.bv_sle(args[0], args[1])?,
            Op::IntGt => arena.bv_sgt(args[0], args[1])?,
            Op::IntGe => arena.bv_sge(args[0], args[1])?,
            // Eq / Ite / Bool connectives over already-rewritten args, plus any
            // pure bit-vector operators, rebuild unchanged.
            _ => build_app(arena, op, args)?,
        };
        Ok(term)
    }

    fn encode_constant(&self, arena: &mut TermArena, value: i128) -> Result<TermId, IntBlastError> {
        let width = self.width;
        let min = -(1i128 << (width - 1));
        let max = (1i128 << (width - 1)) - 1;
        if value < min || value > max {
            return Err(IntBlastError::ConstantOutOfRange { value, width });
        }
        // Two's complement low `width` bits (reinterpret the bit pattern).
        let encoded = u128::from_le_bytes(value.to_le_bytes()) & mask(width);
        Ok(arena.bv_const(width, encoded)?)
    }

    fn blast_symbol(
        &mut self,
        arena: &mut TermArena,
        symbol: SymbolId,
    ) -> Result<SymbolId, IntBlastError> {
        if let Some(&cached) = self.symbol_memo.get(&symbol) {
            return Ok(cached);
        }
        let name = format!("!int_bv_{}", self.fresh_counter);
        self.fresh_counter += 1;
        let bv_sym = arena.declare(&name, Sort::BitVec(self.width))?;
        self.symbol_memo.insert(symbol, bv_sym);
        self.vars.push((symbol, bv_sym));
        Ok(bv_sym)
    }
}

/// Returns `true` if `term` contains any integer sort or integer constant.
fn contains_integer(arena: &TermArena, term: TermId) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if arena.sort_of(t) == Sort::Int {
            return true;
        }
        match arena.node(t) {
            TermNode::IntConst(_) => return true,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::RealConst(_)
            | TermNode::Symbol(_) => {}
        }
    }
    false
}

/// Interprets a width-`B` two's complement value as a signed `i128`.
fn to_signed(width: u32, value: u128) -> i128 {
    let value = value & mask(width);
    if width < 128 && (value >> (width - 1)) & 1 == 1 {
        #[allow(clippy::cast_possible_wrap)]
        let signed = value as i128;
        signed - (1i128 << width)
    } else {
        #[allow(clippy::cast_possible_wrap)]
        let signed = value as i128;
        signed
    }
}

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

#[cfg(test)]
mod tests {
    use super::{blast_integers, contains_integer};
    use axeyum_ir::{Assignment, Sort, TermArena, Value, eval};

    #[test]
    fn no_integers_passes_through() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let f = arena.eq(x, one).unwrap();
        let blast = blast_integers(&mut arena, &[f], 32).unwrap();
        assert!(!blast.had_integers());
        assert_eq!(blast.assertions(), &[f]);
    }

    #[test]
    fn linear_constraint_blasts_and_model_reads_back() {
        // x + 2 == 5 && x > 0 : the bit-vector model reads back to the integer
        // x = 3, which satisfies the original integer assertions exactly.
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::Int).unwrap();
        let x = arena.var(x_sym);
        let two = arena.int_const(2);
        let five = arena.int_const(5);
        let zero = arena.int_const(0);
        let sum = arena.int_add(x, two).unwrap();
        let eq = arena.eq(sum, five).unwrap();
        let pos = arena.int_gt(x, zero).unwrap();

        let blast = blast_integers(&mut arena, &[eq, pos], 16).unwrap();
        assert!(blast.had_integers());
        for &t in blast.assertions() {
            assert!(!contains_integer(&arena, t), "no integer ops remain");
        }

        // A bit-vector model with x_bv = 3 satisfies the blasted assertions;
        // reading it back yields the integer x = 3 satisfying the originals.
        let bv_sym = arena.find_symbol("!int_bv_0").unwrap();
        let mut bv_model = Assignment::new();
        bv_model.set(
            bv_sym,
            Value::Bv {
                width: 16,
                value: 3,
            },
        );
        let int_model = blast.integer_model(&bv_model);
        assert_eq!(int_model.get(x_sym), Some(Value::Int(3)));
        assert_eq!(eval(&arena, eq, &int_model).unwrap(), Value::Bool(true));
        assert_eq!(eval(&arena, pos, &int_model).unwrap(), Value::Bool(true));
    }

    #[test]
    fn negative_integers_round_trip_through_signed_encoding() {
        // x == -3 : the encoding is two's complement and reads back negative.
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::Int).unwrap();
        let x = arena.var(x_sym);
        let neg3 = arena.int_const(-3);
        let eq = arena.eq(x, neg3).unwrap();

        let blast = blast_integers(&mut arena, &[eq], 8).unwrap();
        let bv_sym = arena.find_symbol("!int_bv_0").unwrap();
        // -3 in two's complement, width 8, is 0xfd.
        let mut bv_model = Assignment::new();
        bv_model.set(
            bv_sym,
            Value::Bv {
                width: 8,
                value: 0xfd,
            },
        );
        let int_model = blast.integer_model(&bv_model);
        assert_eq!(int_model.get(x_sym), Some(Value::Int(-3)));
        assert_eq!(eval(&arena, eq, &int_model).unwrap(), Value::Bool(true));
    }

    #[test]
    fn constant_out_of_range_is_reported() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::Int).unwrap();
        let x = arena.var(x_sym);
        // 1000 does not fit in signed 8 bits (max 127).
        let big = arena.int_const(1000);
        let eq = arena.eq(x, big).unwrap();
        assert!(blast_integers(&mut arena, &[eq], 8).is_err());
    }
}
