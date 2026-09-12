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

/// Whether the blaster also constrains the **additive** operators
/// (`int_add`/`int_sub`/`int_neg`) against wraparound, the way it already
/// constrains `int_mul`. `0` is off; any non-zero value is on, and **`1` is
/// what ships** (ADR-1937).
///
/// # What this was, and what measured it
///
/// [`Blaster::mul_no_overflow_constraint`] pinned every `int_mul` to its
/// non-wrapping value and **nothing else in this file was pinned at all**.
/// ADR-1921 measured that widening the ladder to 64 decides **0 of 110**
/// winnable `QF_NIA` files, and that 14 of the 20 that stayed `unknown` report
/// `overflowed at width 64` — they climbed the whole tail and the replay still
/// failed at the top rung. The hypothesis it left standing, explicitly as a
/// hypothesis, was that the surviving replay failures are **additive**
/// wraparound: a sum or difference that left the signed range, which widening
/// cannot fix because it enlarges the range the search may wander into exactly
/// as fast as it enlarges the range a genuine witness may live in.
///
/// That hypothesis is now measured and it is right. Interleaved per-file A/B
/// over the whole 200-file `QF_NIA` division, one binary, arms alternating:
/// **39 decided → 78**, 40 gains, 0 real losses, 0 verdict flips, wall
/// **−10.2 %** — it is FASTER, because a constrained search stops wandering
/// through wrapping models the replay would reject anyway. Cost on 298
/// already-decided files across nine integer-bearing divisions: 0 real losses,
/// 0 flips, **+1.9 %** wall. 78 verdicts cross-checked against the benchmark's
/// own `:status`, z3 and cvc5: **0 disagreements**.
/// See `bench-results/qf-nia-dispatch-20260912/`.
///
/// # Soundness
///
/// Same argument as the multiplicative one, and it is a *restriction* at width
/// `B`: it can only shrink the bit-vector model set. `Sat` stays anchored by
/// the exact-integer replay in `lia.rs` / `combined.rs`, which re-checks every
/// original assertion regardless; a bit-vector `Unsat` with integers present is
/// already reported as `unknown` ("no model within the bounded integer width"),
/// never as an integer `unsat`. So a mis-encoded constraint can only make the
/// search MISS a model (a wider rung, or a sound `Unknown`), never accept a
/// wrong `Sat`.
///
/// **The one place a bit-vector `Unsat` IS trusted** is
/// `auto::solve_exact_bounded_box`, which re-blasts a box-clamped query and
/// transfers the raw refutation. That is safe here for a reason worth writing
/// down rather than leaving to be inferred: its `BoundedBox::width` is proven
/// to cover **every Int subterm's** interval, not merely every variable's, so
/// at that width no operation wraps and these constraints are *implied* — they
/// cannot remove a model the box route could otherwise have found. The
/// 499-pair A/B produced **0 verdict flips**, which is the empirical half of
/// the same statement. If this is ever revisited, that function is where to
/// look.
///
/// Turning it back off for an A/B is `AXEYUM_INT_BLAST_ADDITIVE_NO_OVERFLOW=0`.
const ADDITIVE_NO_OVERFLOW: usize = 1;

axeyum_ir::cap_lever! {
    /// The effective value of [`ADDITIVE_NO_OVERFLOW`]: the compiled default, or
    /// `AXEYUM_INT_BLAST_ADDITIVE_NO_OVERFLOW` when that variable is set.
    ///
    /// A measurement lever, not a tuning knob. With the variable unset this is
    /// exactly `ADDITIVE_NO_OVERFLOW` (`1`, on since ADR-1937); set it to `0` to
    /// re-run the A/B against the pre-ADR-1937 encoding. A malformed value is
    /// refused rather than silently defaulted. See [`axeyum_ir::config_lever`].
    fn additive_no_overflow() -> usize = "AXEYUM_INT_BLAST_ADDITIVE_NO_OVERFLOW" or ADDITIVE_NO_OVERFLOW;
}

/// Whether the additive no-overflow side-constraints are armed for this process.
#[must_use]
pub fn additive_no_overflow_armed() -> bool {
    additive_no_overflow() != 0
}

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
    /// An integer constant outside the `i128` reference range (ADR-1702 slice
    /// 2). It cannot fit any width this route accepts, so it is a decline, not
    /// a narrowing; the caller should treat it as `unknown`.
    WideConstantOutOfRange {
        /// Bit length of the offending constant's magnitude.
        bits: u64,
        /// The chosen bit-width.
        width: u32,
    },
    /// The requested width is zero or exceeds [`MAX_INT_BLAST_WIDTH`].
    InvalidWidth(u32),
    /// An integer operator with no faithful finite bit-vector encoding in this
    /// route (e.g. `int.pow2`, whose value is exponential in its operand). The
    /// caller should treat this as `unknown` and let a specialized decider (the
    /// NIA linearizer) handle the query instead.
    UnsupportedOp(Op),
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
            IntBlastError::WideConstantOutOfRange { bits, width } => {
                write!(
                    f,
                    "integer constant of {bits} bits is outside the i128 range and \
                     does not fit signed {width} bits"
                )
            }
            IntBlastError::InvalidWidth(width) => {
                write!(f, "invalid integer bit-blast width {width}")
            }
            IntBlastError::UnsupportedOp(op) => {
                write!(f, "integer bit-blast does not support operator {op:?}")
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
    blast_integers_with_additive_no_overflow(arena, assertions, width, additive_no_overflow_armed())
}

/// [`blast_integers`] with the additive no-overflow side-constraints selected
/// EXPLICITLY rather than read from the process environment.
///
/// The lever ([`ADDITIVE_NO_OVERFLOW`]) resolves once per process through a
/// `OnceLock`, so a test that sets the variable is a test of whichever test
/// happened to read it first. Taking the flag as an argument is what makes the
/// armed behaviour testable at all, and what lets a measurement harness arm it
/// per call instead of per process.
///
/// # Errors
///
/// As [`blast_integers`].
pub fn blast_integers_with_additive_no_overflow(
    arena: &mut TermArena,
    assertions: &[TermId],
    width: u32,
    additive: bool,
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
        additive,
        ..Blaster::default()
    };
    let mut rewritten = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        rewritten.push(ctx.rewrite(arena, assertion)?);
    }

    // No-overflow side-constraints for every integer product bit-blasted at width
    // `B` -- and, when `AXEYUM_INT_BLAST_ADDITIVE_NO_OVERFLOW` is armed, for every
    // `int_add`/`int_sub`/`int_neg` as well (see `ADDITIVE_NO_OVERFLOW`; off by
    // default, so the shipped assertions are unchanged). Each is a *restriction*
    // that forces the SAT search onto a NON-WRAPPING (faithful) model, so the
    // bounded blast finds the genuine small witness instead of a spurious mod-2^B
    // wrapping one (which replay rejects). Conjoining them with the rewritten
    // assertions keeps the result a pure conjunction; see
    // `mul_no_overflow_constraint` / `additive_no_overflow_constraint` for the
    // encodings and the soundness note (replay remains the anchor;
    // UNSAT-with-constraint only widens via the ladder, never an `unsat`).
    let restricting_constraints = ctx.no_overflow_constraints.len();
    rewritten.extend(ctx.no_overflow_constraints);

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
    /// No-overflow side-constraints accumulated while rewriting: one `bool` term
    /// per `int_mul`, plus one per `int_add`/`int_sub`/`int_neg` when
    /// [`additive_no_overflow_armed`] is true. Conjoined with the rewritten
    /// assertions.
    no_overflow_constraints: Vec<TermId>,
    /// Whether `int_add`/`int_sub`/`int_neg` also get a no-overflow constraint.
    /// Passed in, never read from the environment here: see
    /// [`blast_integers_with_additive_no_overflow`].
    additive: bool,
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
            // A literal outside `i128` cannot fit any width this route
            // accepts (`MAX_INT_BLAST_WIDTH` is 64), so it declines with
            // its own error rather than being narrowed. Every caller of
            // `blast_integers` already maps an `IntBlastError` to
            // `unknown`.
            TermNode::WideIntConst(value) => {
                return Err(IntBlastError::WideConstantOutOfRange {
                    bits: value.bits(),
                    width: self.width,
                });
            }
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
            // `int.pow2` has no faithful finite bit-vector encoding here (its value
            // is exponential in the operand); decline so the query falls through to
            // the NIA linearizer, which abstracts it with theory-valid axioms.
            TermNode::App {
                op: Op::IntPow2, ..
            } => return Err(IntBlastError::UnsupportedOp(Op::IntPow2)),
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
                self.no_overflow_constraints.push(constraint);
                product
            }
            // The ADDITIVE analogue, armed only by
            // `AXEYUM_INT_BLAST_ADDITIVE_NO_OVERFLOW` (see [`ADDITIVE_NO_OVERFLOW`]).
            // With the lever off this arm's guard is false and the operators fall
            // through to the generic `App` arm below — the pre-lever behaviour,
            // unchanged. `IntAbs`, and the `bv_add`/`bv_sub` inside the Euclidean
            // `IntDiv`/`IntMod` construction in `build_int_app`, are NOT covered:
            // they are built there, not here, and saying so is cheaper than
            // letting a reader infer coverage this arm does not have.
            TermNode::App {
                op: op @ (Op::IntAdd | Op::IntSub | Op::IntNeg),
                ref args,
            } if self.additive => {
                let mut lowered = Vec::with_capacity(args.len());
                for &arg in args {
                    lowered.push(self.rewrite(arena, arg)?);
                }
                let result = Self::build_int_app(arena, op, &lowered)?;
                let constraint =
                    Self::additive_no_overflow_constraint(arena, op, &lowered, result)?;
                self.no_overflow_constraints.push(constraint);
                result
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

    /// The **additive** no-overflow side-constraint for `int_add`, `int_sub` and
    /// `int_neg`, whose width-`B` two's-complement value is `result`.
    ///
    /// One extra bit is enough and 2·`B` would be waste: the signed sum,
    /// difference or negation of `B`-bit values always fits in `B+1` bits. So
    /// recompute the operation exactly at `B+1` and demand that it equal the
    /// sign-extension of the width-`B` `result`; that holds iff the width-`B`
    /// operation did NOT wrap. (`int_neg` is included because `-MIN` is exactly
    /// the value that wraps to itself, which no `add`/`sub` constraint catches.)
    ///
    /// Soundness: see [`ADDITIVE_NO_OVERFLOW`]. This is a restriction at width
    /// `B`; `Sat` remains anchored by the exact-integer replay and an in-range
    /// `unsat` is already reported as `unknown`.
    ///
    /// An associated function, not a method: unlike
    /// [`Self::mul_no_overflow_constraint`] it needs no `self.width` — one extra
    /// bit is enough at every width, so the width never enters the encoding.
    fn additive_no_overflow_constraint(
        arena: &mut TermArena,
        op: Op,
        lowered: &[TermId],
        result: TermId,
    ) -> Result<TermId, IntBlastError> {
        let wide: Vec<TermId> = lowered
            .iter()
            .map(|&t| arena.sign_ext(1, t))
            .collect::<Result<_, _>>()?;
        let true_value = Self::build_int_app(arena, op, &wide)?;
        let result_wide = arena.sign_ext(1, result)?;
        Ok(arena.eq(result_wide, true_value)?)
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
        let bv_sym = arena.declare_internal(&name, Sort::BitVec(self.width))?;
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
            TermNode::IntConst(_) | TermNode::WideIntConst(_) => return true,
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
    use super::{blast_integers, blast_integers_with_additive_no_overflow, contains_integer};
    use axeyum_ir::{Assignment, Op, Sort, TermArena, TermId, TermNode, Value, eval};

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
    fn user_declare_cannot_alias_int_blast_fresh_bv() {
        // Soundness firewall: a crafted user symbol named exactly like the fresh
        // bit-blast helper (`!int_bv_0`) must NOT alias the internal helper the
        // reduction mints. The user and internal namespaces are disjoint, so even
        // with the same name string they resolve to two distinct `SymbolId`s.
        let mut arena = TermArena::new();
        // The attacker declares the user symbol first — exactly what the SMT-LIB
        // parser does for `(declare-fun !int_bv_0 () (_ BitVec 8))`.
        let user = arena.declare("!int_bv_0", Sort::BitVec(8)).unwrap();

        let x_sym = arena.declare("x", Sort::Int).unwrap();
        let x = arena.var(x_sym);
        let five = arena.int_const(5);
        let eq = arena.eq(x, five).unwrap();
        let _blast = blast_integers(&mut arena, &[eq], 8).unwrap();

        let internal = arena
            .find_internal_symbol("!int_bv_0")
            .expect("blast minted its fresh bv symbol on the internal namespace");
        assert_ne!(
            internal, user,
            "user declare aliased the internal bit-blast symbol — firewall breached",
        );
        assert_eq!(arena.find_symbol("!int_bv_0"), Some(user));
        assert_eq!(arena.find_internal_symbol("!int_bv_0"), Some(internal));
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
        let bv_sym = arena.find_internal_symbol("!int_bv_0").unwrap();
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
        let bv_sym = arena.find_internal_symbol("!int_bv_0").unwrap();
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

    // ----------------------------------------------------------------------
    // The ADDITIVE no-overflow side-constraint (`ADDITIVE_NO_OVERFLOW`).
    //
    // Every test below drives `blast_integers_with_additive_no_overflow`
    // EXPLICITLY rather than through the environment lever: the lever resolves
    // once per process through a `OnceLock`, so an env-var test is a test of
    // whichever test read it first -- a gate on one shell, and one that passes
    // or fails by scheduling order.
    // ----------------------------------------------------------------------

    /// Counts the integer operators of each kind reachable from `roots`, so the
    /// expectations below are derived from the TERM, not from a literal a
    /// maintainer typed. A test named "only products are constrained" that
    /// hard-codes `1` measures the maintainer's memory of the fixture.
    fn int_op_counts(arena: &TermArena, roots: &[TermId]) -> (usize, usize) {
        use std::collections::BTreeSet;
        let (mut muls, mut adds) = (0, 0);
        let mut seen: BTreeSet<TermId> = BTreeSet::new();
        let mut stack: Vec<TermId> = roots.to_vec();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let TermNode::App { op, args } = arena.node(t) {
                match op {
                    Op::IntMul => muls += 1,
                    Op::IntAdd | Op::IntSub | Op::IntNeg => adds += 1,
                    _ => {}
                }
                stack.extend(args.iter().copied());
            }
        }
        (muls, adds)
    }

    /// `(+ (* x y) z) = 1` -- one product and one sum, so the two arms are
    /// distinguishable by COUNT and a fixture that accidentally had no sum
    /// could not pass.
    fn one_product_one_sum(arena: &mut TermArena) -> Vec<TermId> {
        let xs = arena.declare("x", Sort::Int).unwrap();
        let ys = arena.declare("y", Sort::Int).unwrap();
        let zs = arena.declare("z", Sort::Int).unwrap();
        let (x, y, z) = (arena.var(xs), arena.var(ys), arena.var(zs));
        let prod = arena.int_mul(x, y).unwrap();
        let sum = arena.int_add(prod, z).unwrap();
        let one = arena.int_const(1);
        vec![arena.eq(sum, one).unwrap()]
    }

    #[test]
    fn the_shipped_blaster_constrains_products_and_nothing_else() {
        let mut arena = TermArena::new();
        let assertions = one_product_one_sum(&mut arena);
        let (muls, adds) = int_op_counts(&arena, &assertions);
        assert!(muls > 0 && adds > 0, "fixture must contain both kinds");

        let off =
            blast_integers_with_additive_no_overflow(&mut arena, &assertions, 8, false).unwrap();
        assert_eq!(
            off.restricting_constraints(),
            muls,
            "with the lever off, exactly one constraint per product and none per sum",
        );
    }

    #[test]
    fn arming_the_lever_adds_one_constraint_per_additive_operator() {
        let mut arena = TermArena::new();
        let assertions = one_product_one_sum(&mut arena);
        let (muls, adds) = int_op_counts(&arena, &assertions);

        let on =
            blast_integers_with_additive_no_overflow(&mut arena, &assertions, 8, true).unwrap();
        assert_eq!(
            on.restricting_constraints(),
            muls + adds,
            "armed: one per product AND one per add/sub/neg",
        );
    }

    #[test]
    fn the_shipped_default_is_on() {
        // The constant, not the resolved lever: `additive_no_overflow_armed()`
        // reads the environment, and asserting on it would make this test pass
        // or fail by ambient variable. What ships is the constant.
        assert_ne!(
            super::ADDITIVE_NO_OVERFLOW,
            0,
            "the additive constraint ships ON (ADR-1937: +40 decided on QF_NIA, 0 real \
             losses over 499 paired solves, 0 disagreements against :status/z3/cvc5). \
             Turning it OFF is an A/B (AXEYUM_INT_BLAST_ADDITIVE_NO_OVERFLOW=0), not a default.",
        );
    }

    /// The encoding test that can actually fail: enumerate EVERY width-4 model
    /// and require the emitted constraint to be true exactly when the integer
    /// result is in signed range.
    ///
    /// This is what distinguishes the shipped encoding from every plausible
    /// wrong one: a zero-extension instead of a sign-extension disagrees on
    /// negative operands, extending by 0 bits makes it a tautology, and
    /// comparing the wrong side makes it unsatisfiable. Each of those is a
    /// distinct wrong answer on some pair in this table.
    #[test]
    fn the_additive_constraint_is_exactly_in_signed_range_at_every_width_4_model() {
        const W: u32 = 4;
        const LO: i32 = -8;
        const HI: i32 = 7;
        let mut checked = 0usize;
        let mut excluded = 0usize;
        for a in LO..=HI {
            for b in LO..=HI {
                let mut arena = TermArena::new();
                let xs = arena.declare("x", Sort::Int).unwrap();
                let ys = arena.declare("y", Sort::Int).unwrap();
                let (x, y) = (arena.var(xs), arena.var(ys));
                let sum = arena.int_add(x, y).unwrap();
                let zero = arena.int_const(0);
                // A trivially true carrier so `sum` is reachable from an assertion.
                let ge = arena.int_ge(sum, zero).unwrap();
                let lt = arena.int_lt(sum, zero).unwrap();
                let root = arena.or(ge, lt).unwrap();

                let blast =
                    blast_integers_with_additive_no_overflow(&mut arena, &[root], W, true).unwrap();
                assert_eq!(blast.restricting_constraints(), 1);
                // The constraint is the LAST assertion (appended after the
                // rewritten roots) -- asserted, not assumed.
                let constraint = *blast.assertions().last().unwrap();

                let bx = arena.find_internal_symbol("!int_bv_0").unwrap();
                let by = arena.find_internal_symbol("!int_bv_1").unwrap();
                let mut m = Assignment::new();
                m.set(bx, encode_signed(a, W));
                m.set(by, encode_signed(b, W));

                let got = eval(&arena, constraint, &m).unwrap();
                let want = (LO..=HI).contains(&(a + b));
                assert_eq!(
                    got,
                    Value::Bool(want),
                    "a={a} b={b}: a+b={} in range? {want}",
                    a + b
                );
                checked += 1;
                if !want {
                    excluded += 1;
                }
            }
        }
        assert_eq!(checked, 256, "every width-4 pair must be exercised");
        // A constraint that excludes NOTHING is a constraint that does nothing;
        // the population must contain both outcomes or this test is vacuous.
        assert!(
            excluded > 0 && excluded < checked,
            "{excluded} of {checked} excluded -- the table must contain both outcomes",
        );
    }

    /// `int_neg` is in the arm for exactly one value: `-MIN` wraps to itself,
    /// and no `add`/`sub` constraint catches it. If the arm ever loses `IntNeg`
    /// this is the test that notices.
    #[test]
    fn the_additive_constraint_catches_negating_the_minimum() {
        const W: u32 = 4;
        let mut arena = TermArena::new();
        let xs = arena.declare("x", Sort::Int).unwrap();
        let x = arena.var(xs);
        let neg = arena.int_neg(x).unwrap();
        let zero = arena.int_const(0);
        let ge = arena.int_ge(neg, zero).unwrap();
        let lt = arena.int_lt(neg, zero).unwrap();
        let root = arena.or(ge, lt).unwrap();

        let blast = blast_integers_with_additive_no_overflow(&mut arena, &[root], W, true).unwrap();
        assert_eq!(blast.restricting_constraints(), 1);
        let constraint = *blast.assertions().last().unwrap();
        let bx = arena.find_internal_symbol("!int_bv_0").unwrap();

        for (v, want) in [(-8_i32, false), (-7, true), (0, true), (7, true)] {
            let mut m = Assignment::new();
            m.set(bx, encode_signed(v, W));
            assert_eq!(
                eval(&arena, constraint, &m).unwrap(),
                Value::Bool(want),
                "neg({v}) in signed range? {want}",
            );
        }
    }

    /// Two's-complement encoding of a signed `i32` into a width-`w` bit-vector
    /// value, for the enumeration tests above.
    fn encode_signed(v: i32, w: u32) -> Value {
        let mask = (1u128 << w) - 1;
        Value::Bv {
            width: w,
            value: i128::from(v).cast_unsigned() & mask,
        }
    }
}
