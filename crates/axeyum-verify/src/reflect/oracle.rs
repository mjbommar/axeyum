//! The differential-fuzz **oracle harness** (Track 5, P5.4 / T5.4.1).
//!
//! Reflection is *untrusted search*; this is the concrete-execution check that
//! sits opposite the symbolic proofs. Given a set of BV input symbols and one or
//! more evaluators — a reflected [`TermId`], or a real Rust closure standing in
//! for the compiled function — `DiffFuzz` samples inputs deterministically
//! (seeded LCG + width corners), evaluates every evaluator, and reports any
//! disagreement with the exact witnessing inputs. `DISAGREE = 0` is the floor
//! the whole project holds; this makes it one call instead of a hand-rolled loop
//! per test.
//!
//! Two shapes, both here:
//! - **reflection ≡ reflection** (`DiffFuzz::check_agree`) — e.g. a function's
//!   MIR reflection vs its LLVM reflection (the cross-IR differential fuzz);
//! - **reflection ≡ real fn** (`DiffFuzz::check_against`) — the reflected term
//!   vs the actual Rust function (the module/`checked_*` oracles).
//!
//! Determinism is a public promise, so the sampling is a fixed LCG with an
//! explicit seed; the same `(inputs, seed, iters)` always draws the same tuples.

use axeyum_ir::{Assignment, SymbolId, TermArena, TermId, Value, eval};

/// The LCG multiplier used throughout axeyum's deterministic samplers.
const LCG_MUL: u64 = 6_364_136_223_846_793_005;
/// Default seed (distinct from the string/BV fuzz seeds so failures are traceable).
const DEFAULT_SEED: u64 = 0x5DEE_CE66_D1CE_5EED;

/// The result of a differential-fuzz run.
#[derive(Debug, Clone)]
pub struct FuzzReport {
    /// How many input tuples were drawn and checked.
    pub samples: usize,
    /// How many of them produced disagreeing outputs.
    pub disagreements: usize,
    /// The first disagreeing `(inputs, left, right)`, if any.
    pub first: Option<(Vec<u128>, u128, u128)>,
}

impl FuzzReport {
    /// Whether every sample agreed (`DISAGREE = 0`).
    pub fn agreed(&self) -> bool {
        self.disagreements == 0
    }

    /// Panic with the witnessing inputs unless every sample agreed — the
    /// one-liner a test asserts on.
    ///
    /// # Panics
    /// Panics if any sample disagreed, printing the first witnessing tuple.
    pub fn assert_agreed(&self, what: &str) {
        assert!(
            self.agreed(),
            "{what}: {} / {} samples disagreed; first at inputs {:?}: {:?} vs {:?}",
            self.disagreements,
            self.samples,
            self.first.as_ref().map(|w| &w.0),
            self.first.as_ref().map(|w| w.1),
            self.first.as_ref().map(|w| w.2),
        );
    }
}

/// A deterministic differential-fuzz driver over a fixed set of BV input symbols.
///
/// The `inputs` are `(symbol, width)` in the order a [`check_against`] oracle
/// receives them; width `1` binds a `Bool`, any other width a `BitVec`.
///
/// [`check_against`]: DiffFuzz::check_against
pub struct DiffFuzz {
    inputs: Vec<(SymbolId, u32)>,
    iters: usize,
    seed: u64,
}

impl DiffFuzz {
    /// A driver over `inputs`, with the default seed and `iters` samples.
    pub fn new(inputs: Vec<(SymbolId, u32)>, iters: usize) -> Self {
        Self {
            inputs,
            iters,
            seed: DEFAULT_SEED,
        }
    }

    /// As [`DiffFuzz::new`] but with an explicit seed (for independent runs).
    #[must_use]
    pub fn with_seed(mut self, seed: u64) -> Self {
        self.seed = seed;
        self
    }

    /// The width mask for a `width`-bit value (`width` in `1..=128`).
    fn mask(width: u32) -> u128 {
        if width >= 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        }
    }

    /// The always-tested corner values for a `width`-bit input.
    fn corners(width: u32) -> [u128; 5] {
        let m = Self::mask(width);
        let sign = if width >= 1 { 1u128 << (width - 1) } else { 0 };
        [0, 1, m, m - 1, sign & m]
    }

    /// Draw the `iter`-th input tuple: the first few are corner tuples (every
    /// input at its k-th corner), the rest LCG-random. Deterministic in
    /// `(seed, iter)`.
    fn sample(&self, iter: usize) -> Vec<u128> {
        // Corner phase: one tuple per corner index (all inputs share the index).
        if iter < 5 {
            return self
                .inputs
                .iter()
                .map(|&(_, w)| Self::corners(w)[iter])
                .collect();
        }
        // Random phase: an LCG stream stepped per input, folded to ≤128 bits.
        let mut state = self
            .seed
            .wrapping_add((iter as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let mut next = || {
            state = state.wrapping_mul(LCG_MUL).wrapping_add(1);
            state
        };
        self.inputs
            .iter()
            .map(|&(_, w)| {
                let lo = u128::from(next());
                let hi = u128::from(next());
                ((hi << 64) | lo) & Self::mask(w)
            })
            .collect()
    }

    /// Bind sampled `values` (in input order) into an [`Assignment`].
    fn assignment(&self, values: &[u128]) -> Assignment {
        let mut asg = Assignment::new();
        for (&(sym, width), &value) in self.inputs.iter().zip(values) {
            let v = if width == 1 {
                Value::Bool(value & 1 == 1)
            } else {
                Value::Bv {
                    width,
                    value: value & Self::mask(width),
                }
            };
            asg.set(sym, v);
        }
        asg
    }

    /// Read a BV-valued reflected term under an assignment.
    fn eval_bv(arena: &TermArena, term: TermId, asg: &Assignment) -> u128 {
        match eval(arena, term, asg).expect("reflected term should evaluate") {
            Value::Bv { value, .. } => value,
            other => panic!("expected a BV value from the reflected term, got {other:?}"),
        }
    }

    /// Fuzz `term` against a real-function `oracle` (which receives the sampled
    /// input values in symbol order and returns the expected `width`-agnostic
    /// output). The oracle's return and the term's value are compared as raw
    /// `u128` (mask on your side if the widths differ).
    ///
    /// # Panics
    /// Panics if a reflected term does not evaluate to a bit-vector value.
    pub fn check_against<F: Fn(&[u128]) -> u128>(
        &self,
        arena: &TermArena,
        term: TermId,
        oracle: F,
    ) -> FuzzReport {
        self.run(arena, term, |_arena, asg| oracle_wrap(&oracle, asg, self))
    }

    /// Fuzz two reflected terms (`left`, `right`) for pointwise agreement — the
    /// reflection ≡ reflection shape (e.g. MIR vs LLVM of one function).
    ///
    /// # Panics
    /// Panics if either reflected term does not evaluate to a bit-vector value.
    pub fn check_agree(&self, arena: &TermArena, left: TermId, right: TermId) -> FuzzReport {
        let mut disagreements = 0;
        let mut first = None;
        for iter in 0..self.iters {
            let values = self.sample(iter);
            let asg = self.assignment(&values);
            let l = Self::eval_bv(arena, left, &asg);
            let r = Self::eval_bv(arena, right, &asg);
            if l != r {
                disagreements += 1;
                if first.is_none() {
                    first = Some((values, l, r));
                }
            }
        }
        FuzzReport {
            samples: self.iters,
            disagreements,
            first,
        }
    }

    /// The shared driver for [`check_against`](DiffFuzz::check_against): compare
    /// the term's value to `expected(arena, assignment)` per sample.
    fn run(
        &self,
        arena: &TermArena,
        term: TermId,
        expected: impl Fn(&TermArena, &Assignment) -> u128,
    ) -> FuzzReport {
        let mut disagreements = 0;
        let mut first = None;
        for iter in 0..self.iters {
            let values = self.sample(iter);
            let asg = self.assignment(&values);
            let got = Self::eval_bv(arena, term, &asg);
            let want = expected(arena, &asg);
            if got != want {
                disagreements += 1;
                if first.is_none() {
                    first = Some((values, got, want));
                }
            }
        }
        FuzzReport {
            samples: self.iters,
            disagreements,
            first,
        }
    }
}

/// Recover the sampled values from an assignment (input order) and hand them to
/// the caller's oracle — so `check_against` oracles see `&[u128]`, not the arena.
fn oracle_wrap<F: Fn(&[u128]) -> u128>(oracle: &F, asg: &Assignment, fuzz: &DiffFuzz) -> u128 {
    let values: Vec<u128> = fuzz
        .inputs
        .iter()
        .map(|&(sym, _)| match asg.get(sym) {
            Some(Value::Bv { value, .. }) => value,
            Some(Value::Bool(b)) => u128::from(b),
            other => panic!("oracle input has no scalar value: {other:?}"),
        })
        .collect();
    oracle(&values)
}
