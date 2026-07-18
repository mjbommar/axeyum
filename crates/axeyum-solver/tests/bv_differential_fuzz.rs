//! Adversarial differential soundness fuzzer for the scalar bit-vector
//! (`QF_BV`) sat/unsat decider against the Z3 oracle.
//!
//! `QF_BV` is the **foundation layer** the whole stack bit-blasts down to:
//! arrays (`QF_ABV`) eliminate to it, and every other fragment that lowers to a
//! SAT query passes through the same term-to-AIG-to-CNF path. A wrong `Unsat`
//! (claiming no model when one exists) or a wrong `Sat` (a model that does not
//! satisfy the original atoms, or one Z3 refutes) here would be the worst
//! possible bug, so validating this decider is the capstone of a soundness
//! sweep that already found four real defects in other fragments.
//!
//! This harness — mirroring the proven `abv_differential_fuzz.rs` /
//! `nia_differential_fuzz.rs` templates — deterministically generates thousands
//! of small random `QF_BV` formulas (no `Math::random`/`Date::now`; a fixed-seed
//! LCG drives every choice), decides each with both the default pure-Rust
//! `solve` front door (the `QF_BV` bit-blast path) and a direct Z3 BV query over
//! the same declarations and atoms, and gates on the joint verdict:
//!
//! - axeyum `Sat` ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat` → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Sat` → the returned model is **independently replayed** through the
//!   IR ground evaluator on every original atom; a definite `Bool(false)` replay
//!   panics (wrong sat) regardless of Z3.
//! - axeyum `Unknown` is ALLOWED (incomplete is sound) — counted, never failed.
//! - Z3 `Unknown`/timeout → the instance is skipped (cannot adjudicate).
//! - a solver panic is caught (`catch_unwind`) and counted as CRASHED
//!   (adjudication-neutral — a panic is never a verdict, hence never a
//!   mis-verdict); the first repro is recorded and the sweep continues.
//!
//! The test passes iff disagreements == 0 AND no axeyum `Sat` definitely
//! refutes under replay.
//!
//! A deterministic 1-in-16 sample is also sent to cvc5 when that binary is
//! available, creating a standing three-way verdict gate without making the
//! default pure-Rust build depend on an external executable. Set
//! `AXEYUM_REQUIRE_CVC5=1` in the publication lane to fail rather than skip
//! when cvc5 is unavailable. Every disagreement prints the complete standalone
//! SMT-LIB reproducer. Four named controls preserve the Glaurung bug history:
//! strict rejection of malformed concat/extension contracts, legitimate empty
//! SAT models versus model-less UNSAT, normalized concat/extension semantics,
//! and a full-width 128-bit constant with bit 100 set.
//!
//! Set `AXEYUM_QFBV_PROOF_SAMPLE_STRIDE=N` to select jointly-UNSAT width-at-most-8
//! rows for both CNF DRAT and end-to-end faithfulness-plus-DRAT checking. An
//! optional `AXEYUM_QFBV_PROOF_DEADLINE_MS` gives each route its own bounded
//! proof-search deadline; expiry is counted with the exact seed as inconclusive
//! or not certified, never as a satisfiability verdict.
//!
//! ## Semantic-safety note
//!
//! Every construct generated has *identical* SMT-LIB semantics on both sides.
//! axeyum adopts SMT-LIB totality verbatim
//! (`docs/research/01-foundations/bv-semantics-and-partial-operations.md`) and
//! Z3 ≥ 2.6 is SMT-LIB-compliant, so the totality corners that trip naive
//! differential testing all match by construction:
//! - `bvudiv x 0 = ~0` (all-ones), `bvurem x 0 = x`; the signed `bvsdiv`,
//!   `bvsrem`, `bvsmod` follow their SMT-LIB expansions (`bvsmod` sign tracks the
//!   divisor). Z3's `Z3_mk_bvudiv`/`…` lower to exactly these.
//! - over-shifts (`bvshl`/`bvlshr`/`bvashr` by a shift amount `≥ W`) yield
//!   `0`/`0`/all-sign-bits — both engines agree.
//! - `extract(h,l)` / `zero_ext(i)` / `sign_ext(i)` / `concat` are width-exact and
//!   index-checked at build time; the generator keeps every index in range.
//!
//! The **full scalar `QF_BV` operator set** is exercised: `bvnot, bvneg, bvand,
//! bvor, bvxor, bvadd, bvsub, bvmul, bvudiv, bvurem, bvsdiv, bvsrem, bvsmod,
//! bvshl, bvlshr, bvashr` plus structural `concat, extract, zero_extend,
//! sign_extend`, and the relations `{=, !=, bvult, bvule, bvugt, bvuge, bvslt,
//! bvsle, bvsgt, bvsge}` with occasional Boolean (`and`/`or`/`not`) combinations.
//! Nothing is omitted: every scalar op's totality convention is shared with Z3.
#![cfg(feature = "full")]
#![cfg(feature = "z3")]

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;
use std::sync::mpsc;
use std::time::{Duration, Instant};

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, EndToEndUnsatOutcome, SolverBackend, SolverConfig, UnsatProofOutcome, Z3Backend,
    certify_qf_bv_unsat_end_to_end_within, export_qf_bv_unsat_proof_within, solve,
};
use z3::ast::{BV, Bool};
use z3::{Params, SatResult, Solver};

mod common_cvc5;
use common_cvc5::{DetailedVerdict as Cvc5Verdict, cvc5_bin, cvc5_decide_detailed};
mod common_bitwuzla;
use common_bitwuzla::{DetailedVerdict as BitwuzlaVerdict, bitwuzla_bin, bitwuzla_decide_detailed};

/// Number of instances generated and adjudicated. Each is tiny (≤ 4 vars, ≤ 4
/// atoms, depth ≤ 3, width ≤ 32) so Z3 decides well within its timeout and the
/// bit-blast stays cheap.
const DEFAULT_INSTANCES: u64 = 4000;
const MAX_CONFIGURED_INSTANCES: u64 = 100_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GeneratorProfile {
    /// The generator used by ADR-0224/0225. Seed 0 still names the exact same
    /// formula as it did in those committed campaigns.
    UniformV1,
    /// Preserve the random formula, then add one deterministic, true edge-case
    /// control. The directed controls rotate over semantic corner families.
    EdgeV1,
}

impl GeneratorProfile {
    fn configured() -> Self {
        match std::env::var("AXEYUM_QFBV_GENERATOR_PROFILE").as_deref() {
            Ok("uniform-v1") | Err(_) => Self::UniformV1,
            Ok("edge-v1") => Self::EdgeV1,
            Ok(value) => {
                panic!("AXEYUM_QFBV_GENERATOR_PROFILE must be uniform-v1 or edge-v1, got {value:?}")
            }
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::UniformV1 => "uniform-v1",
            Self::EdgeV1 => "edge-v1",
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct SweepConfig {
    seed_start: u64,
    seed_end: u64,
    instances: u64,
    profile: GeneratorProfile,
}

impl SweepConfig {
    fn configured() -> Self {
        let seed_start = configured_u64("AXEYUM_QFBV_SEED_START", 0);
        let instances = configured_u64("AXEYUM_QFBV_INSTANCES", DEFAULT_INSTANCES);
        assert!(
            (1..=MAX_CONFIGURED_INSTANCES).contains(&instances),
            "AXEYUM_QFBV_INSTANCES must be in 1..={MAX_CONFIGURED_INSTANCES}"
        );
        let seed_end = seed_start.checked_add(instances).unwrap_or_else(|| {
            panic!("AXEYUM_QFBV_SEED_START + AXEYUM_QFBV_INSTANCES overflowed u64")
        });
        Self {
            seed_start,
            seed_end,
            instances,
            profile: GeneratorProfile::configured(),
        }
    }
}

fn configured_u64(name: &str, default: u64) -> u64 {
    match std::env::var(name) {
        Ok(value) => value
            .parse::<u64>()
            .unwrap_or_else(|_| panic!("{name} must be an unsigned integer")),
        Err(_) => default,
    }
}

/// Send this deterministic subset of generated instances to the independent
/// cvc5 parser/solver. The existing Axeyum/Z3 gate still covers every row.
const CVC5_SAMPLE_STRIDE: u64 = 16;
const BITWUZLA_SAMPLE_STRIDE: u64 = 16;

fn cvc5_sample_stride() -> u64 {
    match std::env::var("AXEYUM_CVC5_SAMPLE_STRIDE") {
        Ok(value) => value
            .parse::<u64>()
            .ok()
            .filter(|stride| *stride > 0)
            .unwrap_or_else(|| panic!("AXEYUM_CVC5_SAMPLE_STRIDE must be a positive integer")),
        Err(_) => CVC5_SAMPLE_STRIDE,
    }
}

fn bitwuzla_sample_stride() -> u64 {
    match std::env::var("AXEYUM_BITWUZLA_SAMPLE_STRIDE") {
        Ok(value) => value
            .parse::<u64>()
            .ok()
            .filter(|stride| *stride > 0)
            .unwrap_or_else(|| panic!("AXEYUM_BITWUZLA_SAMPLE_STRIDE must be a positive integer")),
        Err(_) => BITWUZLA_SAMPLE_STRIDE,
    }
}

fn proof_sample_stride() -> Option<u64> {
    let Ok(value) = std::env::var("AXEYUM_QFBV_PROOF_SAMPLE_STRIDE") else {
        return None;
    };
    Some(
        value
            .parse::<u64>()
            .ok()
            .filter(|stride| *stride > 0)
            .unwrap_or_else(|| {
                panic!("AXEYUM_QFBV_PROOF_SAMPLE_STRIDE must be a positive integer")
            }),
    )
}

fn proof_deadline() -> Option<Duration> {
    let value = std::env::var("AXEYUM_QFBV_PROOF_DEADLINE_MS").ok()?;
    let milliseconds = value
        .parse::<u64>()
        .expect("AXEYUM_QFBV_PROOF_DEADLINE_MS must be a positive integer");
    assert!(
        (1..=600_000).contains(&milliseconds),
        "AXEYUM_QFBV_PROOF_DEADLINE_MS must be in 1..=600000"
    );
    Some(Duration::from_millis(milliseconds))
}

fn proof_verbose() -> bool {
    std::env::var("AXEYUM_QFBV_PROOF_VERBOSE").as_deref() == Ok("1")
}

/// Per-instance Z3 wall-clock budget. Small `QF_BV` formulas ⇒ Z3 decides far
/// faster; this only bounds the rare pathological shape so the test never hangs.
const Z3_TIMEOUT: Duration = Duration::from_secs(2);

/// Per-instance hard wall-clock cap on the axeyum `solve`. A slow shape (e.g.
/// nested width-32 `bvmul`/`bvudiv`) is run on a worker thread and joined with
/// this cap; a solve that overruns is recorded as a timeout (adjudication-
/// neutral, exactly like `Unknown`) and the sweep moves on. This is sound — a
/// timeout is never a sat/unsat verdict — and bounds total runtime.
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(5);

/// A deterministic linear-congruential PRNG (the MMIX multiplier/increment).
/// No clock, no OS entropy: the whole sweep is reproducible from the seed.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        // Mix the seed once so consecutive seeds 0,1,2,… don't start correlated.
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }

    /// Advance and return the next 64-bit state.
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    /// A uniform integer in `0..n` (`n > 0`), returned as a `usize`.
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("modulus fits usize")
    }

    /// A uniform integer in `0..n` (`n > 0`), returned as a `u32` (for widths /
    /// extract windows, which are always small). `n` must fit `u32`.
    fn below_u32(&mut self, n: u32) -> u32 {
        u32::try_from(self.next_u64() % u64::from(n)).expect("modulus fits u32")
    }
}

/// The ten relations over bit-vectors. All are total and identical in axeyum and
/// Z3, so every one is a fair differential test.
#[derive(Clone, Copy)]
enum BvCmp {
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

impl BvCmp {
    fn pick(rng: &mut Lcg) -> BvCmp {
        match rng.below(10) {
            0 => BvCmp::Eq,
            1 => BvCmp::Ne,
            2 => BvCmp::Ult,
            3 => BvCmp::Ule,
            4 => BvCmp::Ugt,
            5 => BvCmp::Uge,
            6 => BvCmp::Slt,
            7 => BvCmp::Sle,
            8 => BvCmp::Sgt,
            _ => BvCmp::Sge,
        }
    }

    fn symbol(self) -> &'static str {
        match self {
            BvCmp::Eq => "=",
            BvCmp::Ne => "distinct",
            BvCmp::Ult => "bvult",
            BvCmp::Ule => "bvule",
            BvCmp::Ugt => "bvugt",
            BvCmp::Uge => "bvuge",
            BvCmp::Slt => "bvslt",
            BvCmp::Sle => "bvsle",
            BvCmp::Sgt => "bvsgt",
            BvCmp::Sge => "bvsge",
        }
    }

    /// Build `lhs ⋈ rhs` as an IR Bool over two equal-width bit-vector terms.
    fn build(self, a: &mut TermArena, lhs: TermId, rhs: TermId) -> TermId {
        match self {
            BvCmp::Eq => a.eq(lhs, rhs).unwrap(),
            BvCmp::Ne => {
                let e = a.eq(lhs, rhs).unwrap();
                a.not(e).unwrap()
            }
            BvCmp::Ult => a.bv_ult(lhs, rhs).unwrap(),
            BvCmp::Ule => a.bv_ule(lhs, rhs).unwrap(),
            BvCmp::Ugt => a.bv_ugt(lhs, rhs).unwrap(),
            BvCmp::Uge => a.bv_uge(lhs, rhs).unwrap(),
            BvCmp::Slt => a.bv_slt(lhs, rhs).unwrap(),
            BvCmp::Sle => a.bv_sle(lhs, rhs).unwrap(),
            BvCmp::Sgt => a.bv_sgt(lhs, rhs).unwrap(),
            BvCmp::Sge => a.bv_sge(lhs, rhs).unwrap(),
        }
    }

    /// Build `lhs ⋈ rhs` as a Z3 `Bool` over two bit-vector terms.
    fn build_z3(self, lhs: &BV, rhs: &BV) -> Bool {
        match self {
            BvCmp::Eq => lhs.eq(rhs),
            BvCmp::Ne => lhs.ne(rhs),
            BvCmp::Ult => lhs.bvult(rhs),
            BvCmp::Ule => lhs.bvule(rhs),
            BvCmp::Ugt => lhs.bvugt(rhs),
            BvCmp::Uge => lhs.bvuge(rhs),
            BvCmp::Slt => lhs.bvslt(rhs),
            BvCmp::Sle => lhs.bvsle(rhs),
            BvCmp::Sgt => lhs.bvsgt(rhs),
            BvCmp::Sge => lhs.bvsge(rhs),
        }
    }
}

/// A binary bit-vector operation that preserves width. The full scalar
/// width-preserving set; all are total with verbatim-identical axeyum/Z3
/// semantics (including the SMT-LIB division/remainder/shift totality corners).
#[derive(Clone, Copy, PartialEq, Eq)]
enum BvBin {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Udiv,
    Urem,
    Sdiv,
    Srem,
    Smod,
    Shl,
    Lshr,
    Ashr,
}

impl BvBin {
    fn pick(rng: &mut Lcg) -> BvBin {
        match rng.below(14) {
            0 => BvBin::Add,
            1 => BvBin::Sub,
            2 => BvBin::Mul,
            3 => BvBin::And,
            4 => BvBin::Or,
            5 => BvBin::Xor,
            6 => BvBin::Udiv,
            7 => BvBin::Urem,
            8 => BvBin::Sdiv,
            9 => BvBin::Srem,
            10 => BvBin::Smod,
            11 => BvBin::Shl,
            12 => BvBin::Lshr,
            _ => BvBin::Ashr,
        }
    }

    fn symbol(self) -> &'static str {
        match self {
            BvBin::Add => "bvadd",
            BvBin::Sub => "bvsub",
            BvBin::Mul => "bvmul",
            BvBin::And => "bvand",
            BvBin::Or => "bvor",
            BvBin::Xor => "bvxor",
            BvBin::Udiv => "bvudiv",
            BvBin::Urem => "bvurem",
            BvBin::Sdiv => "bvsdiv",
            BvBin::Srem => "bvsrem",
            BvBin::Smod => "bvsmod",
            BvBin::Shl => "bvshl",
            BvBin::Lshr => "bvlshr",
            BvBin::Ashr => "bvashr",
        }
    }

    fn build(self, a: &mut TermArena, x: TermId, y: TermId) -> TermId {
        match self {
            BvBin::Add => a.bv_add(x, y).unwrap(),
            BvBin::Sub => a.bv_sub(x, y).unwrap(),
            BvBin::Mul => a.bv_mul(x, y).unwrap(),
            BvBin::And => a.bv_and(x, y).unwrap(),
            BvBin::Or => a.bv_or(x, y).unwrap(),
            BvBin::Xor => a.bv_xor(x, y).unwrap(),
            BvBin::Udiv => a.bv_udiv(x, y).unwrap(),
            BvBin::Urem => a.bv_urem(x, y).unwrap(),
            BvBin::Sdiv => a.bv_sdiv(x, y).unwrap(),
            BvBin::Srem => a.bv_srem(x, y).unwrap(),
            BvBin::Smod => a.bv_smod(x, y).unwrap(),
            BvBin::Shl => a.bv_shl(x, y).unwrap(),
            BvBin::Lshr => a.bv_lshr(x, y).unwrap(),
            BvBin::Ashr => a.bv_ashr(x, y).unwrap(),
        }
    }

    fn build_z3(self, x: &BV, y: &BV) -> BV {
        match self {
            BvBin::Add => x.bvadd(y),
            BvBin::Sub => x.bvsub(y),
            BvBin::Mul => x.bvmul(y),
            BvBin::And => x.bvand(y),
            BvBin::Or => x.bvor(y),
            BvBin::Xor => x.bvxor(y),
            BvBin::Udiv => x.bvudiv(y),
            BvBin::Urem => x.bvurem(y),
            BvBin::Sdiv => x.bvsdiv(y),
            BvBin::Srem => x.bvsrem(y),
            BvBin::Smod => x.bvsmod(y),
            BvBin::Shl => x.bvshl(y),
            BvBin::Lshr => x.bvlshr(y),
            BvBin::Ashr => x.bvashr(y),
        }
    }
}

/// A unary width-preserving op.
#[derive(Clone, Copy)]
enum BvUn {
    Not,
    Neg,
}

impl BvUn {
    fn pick(rng: &mut Lcg) -> BvUn {
        if rng.below(2) == 0 {
            BvUn::Not
        } else {
            BvUn::Neg
        }
    }

    fn symbol(self) -> &'static str {
        match self {
            BvUn::Not => "bvnot",
            BvUn::Neg => "bvneg",
        }
    }

    fn build(self, a: &mut TermArena, x: TermId) -> TermId {
        match self {
            BvUn::Not => a.bv_not(x).unwrap(),
            BvUn::Neg => a.bv_neg(x).unwrap(),
        }
    }

    fn build_z3(self, x: &BV) -> BV {
        match self {
            BvUn::Not => x.bvnot(),
            BvUn::Neg => x.bvneg(),
        }
    }
}

/// A width-typed bit-vector term. Every node carries its output width so the
/// width-changing structural ops (`concat`, `extract`, `zero_extend`,
/// `sign_extend`) compose soundly and so atoms compare equal-width operands.
/// Plain data (no IR/Z3 handles), so an [`Instance`] is `Send` + `Clone`; the
/// same tree builds the IR term, the Z3 term, and the pretty-print.
#[derive(Clone)]
enum Term {
    /// A bit-vector variable of the instance width, by index into the vars.
    Var(usize),
    /// A small bit-vector constant of the given width (masked at build time).
    Const { width: u32, value: u128 },
    /// `op(a, b)` for a width-preserving binary op (operands share `a`'s width).
    Bin(BvBin, Box<Term>, Box<Term>),
    /// `op(a)` for a width-preserving unary op.
    Un(BvUn, Box<Term>),
    /// `concat(hi, lo)` — output width is `hi.width + lo.width`.
    Concat(Box<Term>, Box<Term>),
    /// `extract(hi, lo, a)` — output width `hi - lo + 1`, with `hi < a.width`.
    Extract { hi: u32, lo: u32, a: Box<Term> },
    /// `zero_extend(by, a)` — output width `a.width + by`.
    ZeroExt { by: u32, a: Box<Term> },
    /// `sign_extend(by, a)` — output width `a.width + by`.
    SignExt { by: u32, a: Box<Term> },
}

/// Per-instance bit widths. A mix of tiny (sign-bit / carry edges at 1 and 4),
/// byte, and the larger 16/32 that stress carry/overflow/shift chains while the
/// bit-blast stays affordable at depth ≤ 3.
const WIDTHS: [u32; 5] = [1, 4, 8, 16, 32];

const REQUIRED_OPERATORS: &[&str] = &[
    "=",
    "and",
    "bvadd",
    "bvand",
    "bvashr",
    "bvlshr",
    "bvmul",
    "bvneg",
    "bvnot",
    "bvor",
    "bvsdiv",
    "bvsge",
    "bvsgt",
    "bvshl",
    "bvsle",
    "bvslt",
    "bvsmod",
    "bvsrem",
    "bvsub",
    "bvudiv",
    "bvuge",
    "bvugt",
    "bvule",
    "bvult",
    "bvurem",
    "bvxor",
    "concat",
    "const",
    "distinct",
    "extract",
    "not",
    "or",
    "sign_extend",
    "var",
    "zero_extend",
];

const REQUIRED_EDGE_CASES: &[&str] = &[
    "concat_one_bit_high",
    "concat_one_bit_low",
    "constant_all_ones",
    "constant_sign_bit",
    "constant_zero",
    "division_or_remainder_by_zero",
    "extract_full_width",
    "extract_high_boundary",
    "extract_low_boundary",
    "shift_at_width",
    "shift_above_width",
    "signed_division_overflow",
    "sign_extend_by_zero",
    "zero_extend_by_zero",
];

/// Term-tree depth ceiling — shallow so Z3 decides fast and the width-32
/// `bvmul`/`bvudiv` bit-blast stays small.
const MAX_DEPTH: usize = 3;

impl Term {
    fn width(&self, instance_width: u32) -> u32 {
        match self {
            Term::Var(_) => instance_width,
            Term::Const { width, .. } => *width,
            Term::Bin(_, lhs, _) | Term::Un(_, lhs) => lhs.width(instance_width),
            Term::Concat(high, low) => high.width(instance_width) + low.width(instance_width),
            Term::Extract { hi, lo, .. } => hi - lo + 1,
            Term::ZeroExt { by, a } | Term::SignExt { by, a } => a.width(instance_width) + by,
        }
    }

    /// Generate a random term of exactly `width` bits with remaining `depth`.
    ///
    /// Width is threaded top-down: the generator only ever emits a subtree whose
    /// output width equals the requested `width`, so the full tree is well-typed
    /// by construction and atoms always compare equal widths.
    ///
    /// Crucially, the declared variables all have the **instance width**
    /// `inst_width`; a `Var` leaf is therefore only well-typed when the requested
    /// `width == inst_width`. When a width-changing op recurses asking for a
    /// sub-term of a *different* width, only constants and further structural ops
    /// are emitted at that width — never a (mis-typed) `Var`. A leaf at any width
    /// is always a `Const` of that width, so generation always terminates.
    fn generate(rng: &mut Lcg, depth: usize, width: u32, inst_width: u32, num_vars: usize) -> Term {
        // A `Var` (instance width) is only well-typed at the instance width.
        let var_ok = width == inst_width;

        if depth == 0 {
            // Leaf: a variable (only at the instance width) or a small constant.
            return if var_ok && rng.below(3) != 0 {
                Term::Var(rng.below(num_vars as u64))
            } else {
                Term::Const {
                    width,
                    value: u128::from(rng.next_u64()),
                }
            };
        }
        // Pick a constructor. Width-changing ops always recurse at the matching
        // sub-width; the leaf options keep the distribution from blowing up.
        match rng.below(9) {
            0 if var_ok => Term::Var(rng.below(num_vars as u64)),
            // `0` when `!var_ok` (sub-width) falls through here to a constant.
            0 | 1 => Term::Const {
                width,
                value: u128::from(rng.next_u64()),
            },
            2 | 3 => Term::Bin(
                BvBin::pick(rng),
                Box::new(Term::generate(rng, depth - 1, width, inst_width, num_vars)),
                Box::new(Term::generate(rng, depth - 1, width, inst_width, num_vars)),
            ),
            4 => Term::Un(
                BvUn::pick(rng),
                Box::new(Term::generate(rng, depth - 1, width, inst_width, num_vars)),
            ),
            5 => {
                // concat(hi, lo) with hi.width + lo.width == width. Needs width ≥ 2.
                if width < 2 {
                    Term::Const {
                        width,
                        value: u128::from(rng.next_u64()),
                    }
                } else {
                    let lo_w = rng.below_u32(width - 1) + 1; // 1..=width-1
                    let hi_w = width - lo_w;
                    Term::Concat(
                        Box::new(Term::generate(rng, depth - 1, hi_w, inst_width, num_vars)),
                        Box::new(Term::generate(rng, depth - 1, lo_w, inst_width, num_vars)),
                    )
                }
            }
            6 => {
                // extract(hi, lo, a) yielding exactly `width` bits: choose a source
                // width `src ≥ width`, place the window inside it. `hi ≤ src-1`.
                let extra = rng.below_u32(MAX_EXTRACT_PAD + 1);
                let src = width + extra; // src ≥ width, src ≥ 1
                let lo = if src > width {
                    rng.below_u32(src - width + 1)
                } else {
                    0
                };
                let hi = lo + width - 1; // hi - lo + 1 == width, hi ≤ src-1
                Term::Extract {
                    hi,
                    lo,
                    a: Box::new(Term::generate(rng, depth - 1, src, inst_width, num_vars)),
                }
            }
            7 => {
                // zero_extend(by, a): by + src == width, src ≥ 1.
                if width < 2 {
                    Term::Const {
                        width,
                        value: u128::from(rng.next_u64()),
                    }
                } else {
                    let by = rng.below_u32(width - 1); // 0..=width-2
                    let src = width - by;
                    Term::ZeroExt {
                        by,
                        a: Box::new(Term::generate(rng, depth - 1, src, inst_width, num_vars)),
                    }
                }
            }
            _ => {
                // sign_extend(by, a): by + src == width, src ≥ 1.
                if width < 2 {
                    Term::Const {
                        width,
                        value: u128::from(rng.next_u64()),
                    }
                } else {
                    let by = rng.below_u32(width - 1); // 0..=width-2
                    let src = width - by;
                    Term::SignExt {
                        by,
                        a: Box::new(Term::generate(rng, depth - 1, src, inst_width, num_vars)),
                    }
                }
            }
        }
    }

    fn build(&self, a: &mut TermArena, vars: &[TermId]) -> TermId {
        match self {
            Term::Var(i) => vars[*i],
            Term::Const { width, value } => {
                let masked = mask_u128(*value, *width);
                a.bv_const(*width, masked).unwrap()
            }
            Term::Bin(op, x, y) => {
                let xt = x.build(a, vars);
                let yt = y.build(a, vars);
                op.build(a, xt, yt)
            }
            Term::Un(op, x) => {
                let xt = x.build(a, vars);
                op.build(a, xt)
            }
            Term::Concat(hi, lo) => {
                let ht = hi.build(a, vars);
                let lt = lo.build(a, vars);
                a.concat(ht, lt).unwrap()
            }
            Term::Extract { hi, lo, a: inner } => {
                let it = inner.build(a, vars);
                a.extract(*hi, *lo, it).unwrap()
            }
            Term::ZeroExt { by, a: inner } => {
                let it = inner.build(a, vars);
                a.zero_ext(*by, it).unwrap()
            }
            Term::SignExt { by, a: inner } => {
                let it = inner.build(a, vars);
                a.sign_ext(*by, it).unwrap()
            }
        }
    }

    /// Build the Z3 mirror. Z3 `BV` nodes carry their own width, so unlike the
    /// IR side no width has to be threaded — the structural ops read it back off
    /// the operand.
    fn build_z3(&self, vars: &[BV]) -> BV {
        match self {
            Term::Var(i) => vars[*i].clone(),
            Term::Const { width: w, value } => {
                let masked = mask_u128(*value, *w);
                if let Ok(value) = u64::try_from(masked) {
                    BV::from_u64(value, *w)
                } else {
                    BV::from_str(*w, &masked.to_string())
                        .expect("well-typed u128 numeral is accepted by Z3")
                }
            }
            Term::Bin(op, x, y) => {
                let xt = x.build_z3(vars);
                let yt = y.build_z3(vars);
                op.build_z3(&xt, &yt)
            }
            Term::Un(op, x) => {
                let xt = x.build_z3(vars);
                op.build_z3(&xt)
            }
            Term::Concat(hi, lo) => {
                let ht = hi.build_z3(vars);
                let lt = lo.build_z3(vars);
                ht.concat(&lt)
            }
            Term::Extract { hi, lo, a } => {
                let it = a.build_z3(vars);
                it.extract(*hi, *lo)
            }
            Term::ZeroExt { by, a } => {
                let it = a.build_z3(vars);
                it.zero_ext(*by)
            }
            Term::SignExt { by, a } => {
                let it = a.build_z3(vars);
                it.sign_ext(*by)
            }
        }
    }

    fn dump(&self, names: &[&str]) -> String {
        match self {
            Term::Var(i) => names[*i].to_string(),
            Term::Const { width, value } => {
                let masked = mask_u128(*value, *width);
                format!("(_ bv{masked} {width})")
            }
            Term::Bin(op, x, y) => {
                format!("({} {} {})", op.symbol(), x.dump(names), y.dump(names))
            }
            Term::Un(op, x) => format!("({} {})", op.symbol(), x.dump(names)),
            Term::Concat(hi, lo) => format!("(concat {} {})", hi.dump(names), lo.dump(names)),
            Term::Extract { hi, lo, a } => {
                format!("((_ extract {hi} {lo}) {})", a.dump(names))
            }
            Term::ZeroExt { by, a } => format!("((_ zero_extend {by}) {})", a.dump(names)),
            Term::SignExt { by, a } => format!("((_ sign_extend {by}) {})", a.dump(names)),
        }
    }

    fn record_coverage(&self, operators: &mut BTreeSet<&'static str>) {
        match self {
            Term::Var(_) => {
                operators.insert("var");
            }
            Term::Const { .. } => {
                operators.insert("const");
            }
            Term::Bin(op, x, y) => {
                operators.insert(op.symbol());
                x.record_coverage(operators);
                y.record_coverage(operators);
            }
            Term::Un(op, x) => {
                operators.insert(op.symbol());
                x.record_coverage(operators);
            }
            Term::Concat(high, low) => {
                operators.insert("concat");
                high.record_coverage(operators);
                low.record_coverage(operators);
            }
            Term::Extract { a, .. } => {
                operators.insert("extract");
                a.record_coverage(operators);
            }
            Term::ZeroExt { a, .. } => {
                operators.insert("zero_extend");
                a.record_coverage(operators);
            }
            Term::SignExt { a, .. } => {
                operators.insert("sign_extend");
                a.record_coverage(operators);
            }
        }
    }

    fn record_edge_coverage(&self, instance_width: u32, edges: &mut BTreeSet<&'static str>) {
        match self {
            Term::Var(_) => {}
            Term::Const { width, value } => {
                let value = mask_u128(*value, *width);
                if value == 0 {
                    edges.insert("constant_zero");
                }
                if value == mask_u128(u128::MAX, *width) {
                    edges.insert("constant_all_ones");
                }
                if *width > 0 && value == (1_u128 << (*width - 1)) {
                    edges.insert("constant_sign_bit");
                }
            }
            Term::Bin(op, lhs, rhs) => {
                let width = lhs.width(instance_width);
                if matches!(
                    op,
                    BvBin::Udiv | BvBin::Urem | BvBin::Sdiv | BvBin::Srem | BvBin::Smod
                ) && matches!(
                    rhs.as_ref(),
                    Term::Const { width, value } if mask_u128(*value, *width) == 0
                ) {
                    edges.insert("division_or_remainder_by_zero");
                }
                if *op == BvBin::Sdiv
                    && matches!(
                        lhs.as_ref(),
                        Term::Const { width, value }
                            if mask_u128(*value, *width) == (1_u128 << (*width - 1))
                    )
                    && matches!(
                        rhs.as_ref(),
                        Term::Const { width, value }
                            if mask_u128(*value, *width) == mask_u128(u128::MAX, *width)
                    )
                {
                    edges.insert("signed_division_overflow");
                }
                if matches!(op, BvBin::Shl | BvBin::Lshr | BvBin::Ashr)
                    && let Term::Const {
                        width: rhs_width,
                        value,
                    } = rhs.as_ref()
                {
                    let shift = mask_u128(*value, *rhs_width);
                    if shift == u128::from(width) {
                        edges.insert("shift_at_width");
                    } else if shift > u128::from(width) {
                        edges.insert("shift_above_width");
                    }
                }
                lhs.record_edge_coverage(instance_width, edges);
                rhs.record_edge_coverage(instance_width, edges);
            }
            Term::Un(_, inner) => inner.record_edge_coverage(instance_width, edges),
            Term::Concat(high, low) => {
                if high.width(instance_width) == 1 {
                    edges.insert("concat_one_bit_high");
                }
                if low.width(instance_width) == 1 {
                    edges.insert("concat_one_bit_low");
                }
                high.record_edge_coverage(instance_width, edges);
                low.record_edge_coverage(instance_width, edges);
            }
            Term::Extract { hi, lo, a } => {
                let source_width = a.width(instance_width);
                if *lo == 0 {
                    edges.insert("extract_low_boundary");
                }
                if *hi + 1 == source_width {
                    edges.insert("extract_high_boundary");
                }
                if *lo == 0 && *hi + 1 == source_width {
                    edges.insert("extract_full_width");
                }
                a.record_edge_coverage(instance_width, edges);
            }
            Term::ZeroExt { by, a } => {
                if *by == 0 {
                    edges.insert("zero_extend_by_zero");
                }
                a.record_edge_coverage(instance_width, edges);
            }
            Term::SignExt { by, a } => {
                if *by == 0 {
                    edges.insert("sign_extend_by_zero");
                }
                a.record_edge_coverage(instance_width, edges);
            }
        }
    }
}

/// Cap on how much wider than the requested width an `extract` source may be —
/// bounds the extra bit-blast bits and keeps every term shallow.
const MAX_EXTRACT_PAD: u32 = 4;

/// Mask `v` to the low `w` bits.
fn mask_u128(v: u128, w: u32) -> u128 {
    if w >= 128 { v } else { v & ((1u128 << w) - 1) }
}

/// A generated atom: either a single comparison `t1 ⋈ t2` over two equal-width
/// terms, or a small Boolean combination of two comparisons.
#[derive(Clone)]
enum Atom {
    /// `lhs ⋈ rhs`.
    Cmp { lhs: Term, rhs: Term, cmp: BvCmp },
    /// `(c1 ∧ c2)` / `(c1 ∨ c2)` / `¬c1` over comparison atoms.
    BoolCombo(BoolOp, Box<Atom>, Box<Atom>),
}

/// The Boolean connective combining two comparison atoms (`Not` ignores the
/// second operand).
#[derive(Clone, Copy)]
enum BoolOp {
    And,
    Or,
    Not,
}

impl BoolOp {
    fn pick(rng: &mut Lcg) -> BoolOp {
        match rng.below(3) {
            0 => BoolOp::And,
            1 => BoolOp::Or,
            _ => BoolOp::Not,
        }
    }
}

impl Atom {
    /// Generate a single comparison over two equal-width terms.
    ///
    /// The comparison is at the instance width most of the time (so the declared
    /// variables appear), but ~1/4 of the time at a smaller width drawn from
    /// [`WIDTHS`] (operands then built from constants and structural ops) so the
    /// comparators are also exercised on sub-width values.
    fn generate_cmp(rng: &mut Lcg, inst_width: u32, num_vars: usize) -> Atom {
        let cmp_width = if rng.below(4) == 0 {
            // A (possibly) narrower width, capped at the instance width.
            let w = WIDTHS[rng.below(WIDTHS.len() as u64)];
            w.min(inst_width)
        } else {
            inst_width
        };
        Atom::Cmp {
            lhs: Term::generate(rng, MAX_DEPTH, cmp_width, inst_width, num_vars),
            rhs: Term::generate(rng, MAX_DEPTH, cmp_width, inst_width, num_vars),
            cmp: BvCmp::pick(rng),
        }
    }

    /// Generate an atom: ~1/4 of the time a Boolean combination of comparisons.
    fn generate(rng: &mut Lcg, inst_width: u32, num_vars: usize) -> Atom {
        if rng.below(4) == 0 {
            let op = BoolOp::pick(rng);
            let c1 = Box::new(Atom::generate_cmp(rng, inst_width, num_vars));
            let c2 = Box::new(Atom::generate_cmp(rng, inst_width, num_vars));
            Atom::BoolCombo(op, c1, c2)
        } else {
            Atom::generate_cmp(rng, inst_width, num_vars)
        }
    }

    fn build(&self, a: &mut TermArena, vars: &[TermId]) -> TermId {
        match self {
            Atom::Cmp { lhs, rhs, cmp } => {
                let lt = lhs.build(a, vars);
                let rt = rhs.build(a, vars);
                cmp.build(a, lt, rt)
            }
            Atom::BoolCombo(op, c1, c2) => {
                let b1 = c1.build(a, vars);
                match op {
                    BoolOp::And => {
                        let b2 = c2.build(a, vars);
                        a.and(b1, b2).unwrap()
                    }
                    BoolOp::Or => {
                        let b2 = c2.build(a, vars);
                        a.or(b1, b2).unwrap()
                    }
                    BoolOp::Not => a.not(b1).unwrap(),
                }
            }
        }
    }

    fn build_z3(&self, vars: &[BV]) -> Bool {
        match self {
            Atom::Cmp { lhs, rhs, cmp } => {
                let l = lhs.build_z3(vars);
                let r = rhs.build_z3(vars);
                cmp.build_z3(&l, &r)
            }
            Atom::BoolCombo(op, c1, c2) => {
                let b1 = c1.build_z3(vars);
                match op {
                    BoolOp::And => {
                        let b2 = c2.build_z3(vars);
                        Bool::and(&[b1, b2])
                    }
                    BoolOp::Or => {
                        let b2 = c2.build_z3(vars);
                        Bool::or(&[b1, b2])
                    }
                    BoolOp::Not => b1.not(),
                }
            }
        }
    }

    fn dump(&self, names: &[&str]) -> String {
        match self {
            Atom::Cmp { lhs, rhs, cmp } => {
                format!("({} {} {})", cmp.symbol(), lhs.dump(names), rhs.dump(names))
            }
            Atom::BoolCombo(op, c1, c2) => match op {
                BoolOp::And => format!("(and {} {})", c1.dump(names), c2.dump(names)),
                BoolOp::Or => format!("(or {} {})", c1.dump(names), c2.dump(names)),
                BoolOp::Not => format!("(not {})", c1.dump(names)),
            },
        }
    }

    fn record_coverage(&self, operators: &mut BTreeSet<&'static str>) {
        match self {
            Atom::Cmp { lhs, rhs, cmp } => {
                operators.insert(cmp.symbol());
                lhs.record_coverage(operators);
                rhs.record_coverage(operators);
            }
            Atom::BoolCombo(op, first, second) => {
                operators.insert(match op {
                    BoolOp::And => "and",
                    BoolOp::Or => "or",
                    BoolOp::Not => "not",
                });
                first.record_coverage(operators);
                if !matches!(op, BoolOp::Not) {
                    second.record_coverage(operators);
                }
            }
        }
    }

    fn record_edge_coverage(&self, instance_width: u32, edges: &mut BTreeSet<&'static str>) {
        match self {
            Atom::Cmp { lhs, rhs, .. } => {
                lhs.record_edge_coverage(instance_width, edges);
                rhs.record_edge_coverage(instance_width, edges);
            }
            Atom::BoolCombo(op, first, second) => {
                first.record_edge_coverage(instance_width, edges);
                if !matches!(op, BoolOp::Not) {
                    second.record_edge_coverage(instance_width, edges);
                }
            }
        }
    }
}

/// A full generated instance. Owns only plain data (no IR/Z3 handles), so it is
/// `Send` + `Clone` — a clone can be moved onto an axeyum worker thread while the
/// original drives the Z3 query and the repro dump.
#[derive(Clone)]
struct Instance {
    /// The common bit width of all variables (terms may use other widths inside
    /// via structural ops, but the four declared variables share this width).
    width: u32,
    num_vars: usize,
    atoms: Vec<Atom>,
}

/// Variable names (up to 4).
const VAR_NAMES: [&str; 4] = ["x", "y", "z", "w"];

impl Instance {
    /// Deterministically generate an instance from the PRNG.
    ///
    /// Distribution:
    /// - width `W` ∈ {1, 4, 8, 16, 32};
    /// - 2..=4 BV variables of width `W`;
    /// - 1..=4 atoms, each either a comparison `t1 ⋈ t2` (`⋈` uniform over the
    ///   ten relations) over depth-≤3 terms drawn from the full scalar op set, or
    ///   (~1/4) a Boolean `and`/`or`/`not` combination of two comparisons.
    fn generate(rng: &mut Lcg, profile: GeneratorProfile, seed: u64) -> Instance {
        let width = WIDTHS[rng.below(WIDTHS.len() as u64)];
        let num_vars = rng.below(3) + 2; // 2..=4
        let num_atoms = rng.below(4) + 1; // 1..=4

        let mut atoms: Vec<_> = (0..num_atoms)
            .map(|_| Atom::generate(rng, width, num_vars))
            .collect();
        if profile == GeneratorProfile::EdgeV1 {
            atoms.push(edge_control(seed));
        }

        Instance {
            width,
            num_vars,
            atoms,
        }
    }

    /// Materialize the instance as IR assertions over a fresh arena, returning
    /// the arena, the per-variable symbol ids, and the assertion term ids.
    fn build(&self) -> (TermArena, Vec<SymbolId>, Vec<TermId>) {
        let mut a = TermArena::new();
        let syms: Vec<SymbolId> = (0..self.num_vars)
            .map(|i| a.declare(VAR_NAMES[i], Sort::BitVec(self.width)).unwrap())
            .collect();
        let vars: Vec<TermId> = syms.iter().map(|&s| a.var(s)).collect();

        let assertions: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| atom.build(&mut a, &vars))
            .collect();
        (a, syms, assertions)
    }

    /// Build the same instance as a list of Z3 `Bool` atoms over fresh Z3 BV
    /// constants — the exact same `QF_BV` semantics axeyum's bit-blast targets.
    fn to_z3(&self) -> Vec<Bool> {
        let vars: Vec<BV> = (0..self.num_vars)
            .map(|i| BV::new_const(VAR_NAMES[i], self.width))
            .collect();

        self.atoms.iter().map(|atom| atom.build_z3(&vars)).collect()
    }

    /// An SMT-ish dump of the instance for a reproducing panic message.
    fn dump(&self) -> String {
        let names = &VAR_NAMES[..self.num_vars];
        let w = self.width;
        let mut lines = vec![format!("vars: {} : (_ BitVec {w})", names.join(", "))];
        for (i, atom) in self.atoms.iter().enumerate() {
            lines.push(format!("  atom[{i}]: {}", atom.dump(names)));
        }
        lines.join("\n")
    }

    /// Complete standalone SMT-LIB reproducer consumed by cvc5 and printed on
    /// any disagreement. The same typed tree drives Axeyum, direct Z3, and this
    /// rendering, so the three engines share one semantic source of truth.
    fn to_smt2(&self) -> String {
        let mut lines = vec!["(set-logic QF_BV)".to_string()];
        for name in &VAR_NAMES[..self.num_vars] {
            lines.push(format!("(declare-const {name} (_ BitVec {}))", self.width));
        }
        let names = &VAR_NAMES[..self.num_vars];
        for atom in &self.atoms {
            lines.push(format!("(assert {})", atom.dump(names)));
        }
        lines.push("(check-sat)".to_string());
        lines.push("(exit)".to_string());
        lines.join("\n") + "\n"
    }

    fn record_coverage(
        &self,
        widths: &mut BTreeSet<u32>,
        operators: &mut BTreeSet<&'static str>,
        edge_instances: &mut BTreeMap<&'static str, u64>,
    ) {
        widths.insert(self.width);
        let mut edges = BTreeSet::new();
        for atom in &self.atoms {
            atom.record_coverage(operators);
            atom.record_edge_coverage(self.width, &mut edges);
        }
        for edge in edges {
            *edge_instances.entry(edge).or_default() += 1;
        }
    }
}

fn edge_control(seed: u64) -> Atom {
    let c = |value| Term::Const { width: 8, value };
    let bin = |op, lhs, rhs| Term::Bin(op, Box::new(lhs), Box::new(rhs));
    match seed % 16 {
        0 => eq_atom(bin(BvBin::Udiv, c(0xa5), c(0)), c(0xff)),
        1 => eq_atom(bin(BvBin::Urem, c(0xa5), c(0)), c(0xa5)),
        2 => eq_atom(bin(BvBin::Sdiv, c(0x80), c(0xff)), c(0x80)),
        3 => eq_atom(bin(BvBin::Srem, c(0xa5), c(0)), c(0xa5)),
        4 => eq_atom(bin(BvBin::Smod, c(0xa5), c(0)), c(0xa5)),
        5 => eq_atom(bin(BvBin::Shl, c(0xa5), c(8)), c(0)),
        6 => eq_atom(bin(BvBin::Lshr, c(0xa5), c(9)), c(0)),
        7 => eq_atom(bin(BvBin::Ashr, c(0x80), c(8)), c(0xff)),
        8 => eq_atom(
            Term::Extract {
                hi: 3,
                lo: 0,
                a: Box::new(c(0xab)),
            },
            Term::Const {
                width: 4,
                value: 0xb,
            },
        ),
        9 => eq_atom(
            Term::Extract {
                hi: 7,
                lo: 4,
                a: Box::new(c(0xab)),
            },
            Term::Const {
                width: 4,
                value: 0xa,
            },
        ),
        10 => eq_atom(
            Term::Extract {
                hi: 7,
                lo: 0,
                a: Box::new(c(0xab)),
            },
            c(0xab),
        ),
        11 => eq_atom(
            Term::ZeroExt {
                by: 0,
                a: Box::new(c(0xab)),
            },
            c(0xab),
        ),
        12 => eq_atom(
            Term::SignExt {
                by: 0,
                a: Box::new(c(0xab)),
            },
            c(0xab),
        ),
        13 => eq_atom(
            Term::Concat(
                Box::new(Term::Const {
                    width: 7,
                    value: 0x55,
                }),
                Box::new(Term::Const { width: 1, value: 1 }),
            ),
            c(0xab),
        ),
        14 => eq_atom(
            Term::Concat(
                Box::new(Term::Const { width: 1, value: 1 }),
                Box::new(Term::Const {
                    width: 7,
                    value: 0x2b,
                }),
            ),
            c(0xab),
        ),
        _ => eq_atom(c(0x80), c(0x80)),
    }
}

/// A coarse verdict label, abstracting away the model/reason payloads.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn label(r: &CheckResult) -> Verdict {
    match r {
        CheckResult::Sat(_) => Verdict::Sat,
        CheckResult::Unsat => Verdict::Unsat,
        CheckResult::Unknown(_) => Verdict::Unknown,
    }
}

/// The replay outcome of an axeyum `Sat`, computed on the worker thread (which
/// owns the arena). BV ground evaluation is total over this fragment, so a
/// well-formed `Sat` model is expected to replay `AllTrue`. `Indeterminate` is
/// kept defensively (e.g. the evaluator declines an atom) and is adjudication-
/// neutral; only `Violated` is a wrong sat.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Replay {
    /// Not a `Sat` verdict (no model to replay).
    NotSat,
    /// Every original atom evaluated `true` at the model — a verified replay.
    AllTrue,
    /// The evaluator declined ≥ 1 atom (`Err`/non-Bool) and refuted none.
    Indeterminate,
    /// An atom evaluated `false` at the model — a WRONG SAT (carries the atom
    /// index and a model dump for the panic).
    Violated { atom: usize, model: String },
}

/// The full axeyum result for one instance, decided on a worker thread under a
/// hard wall-clock cap.
struct AxeyumOutcome {
    verdict: Verdict,
    replay: Replay,
    /// A model dump for a `Sat` (used only when reporting a disagreement).
    model_dump: Option<String>,
}

/// The bounded axeyum decision for one instance.
enum Bounded {
    /// `solve` finished within the cap and returned a verdict.
    Decided(AxeyumOutcome),
    /// `solve` overran the wall-clock cap — adjudication-neutral, like `Unknown`.
    Timeout,
    /// `solve` (or the replay) **panicked** — a crash bug in the solver, *not* a
    /// sat/unsat verdict. Adjudication-neutral (a panic is never a verdict, so it
    /// can never be a wrong sat/unsat), but counted and the first one reported.
    Crashed,
}

/// Decide an instance with axeyum on a worker thread, joining under
/// [`AXEYUM_TIMEOUT`].
///
/// The arena, the model, and the replay all live on the worker thread; only the
/// `Send` summary crosses back. The whole `solve`+replay runs inside
/// `catch_unwind` so a solver panic does not abort the sweep — it is reported as
/// [`Bounded::Crashed`] (adjudication-neutral), letting the differential gate run
/// across every instance instead of wedging on one crashing shape.
fn solve_axeyum_bounded(inst: Instance) -> Bounded {
    let (tx, rx) = mpsc::channel::<AxeyumOutcome>();
    std::thread::spawn(move || {
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
            let (a, syms, assertions) = inst.build();
            let mut a = a;
            let result = solve(&mut a, &assertions, &SolverConfig::default());
            let outcome = match result {
                // `solve` must not error; treat an error like a crash (channel
                // stays empty → reported as Crashed). `Unknown` is a result.
                Err(_) => return,
                Ok(ax) => {
                    let verdict = label(&ax);
                    let (replay, model_dump) = match &ax {
                        CheckResult::Sat(model) => {
                            let asg = model.to_assignment();
                            let dump = dump_model(&syms, model);
                            let mut replay = Replay::AllTrue;
                            for (i, &assertion) in assertions.iter().enumerate() {
                                match eval(&a, assertion, &asg) {
                                    Ok(Value::Bool(true)) => {}
                                    Ok(Value::Bool(false)) => {
                                        replay = Replay::Violated {
                                            atom: i,
                                            model: dump.clone(),
                                        };
                                        break;
                                    }
                                    // `Err(..)` or a non-Bool result: indeterminate,
                                    // not a refutation. Keep scanning for a true
                                    // violation in a later atom.
                                    _ => {
                                        if replay == Replay::AllTrue {
                                            replay = Replay::Indeterminate;
                                        }
                                    }
                                }
                            }
                            (replay, Some(dump))
                        }
                        _ => (Replay::NotSat, None),
                    };
                    AxeyumOutcome {
                        verdict,
                        replay,
                        model_dump,
                    }
                }
            };
            // The receiver may be gone (we timed out); ignore a send error.
            let _ = tx.send(outcome);
        }));
        // On panic / error, `tx` is dropped here without a send → the receiver
        // observes `Disconnected`, mapped to a crash below.
    });

    match rx.recv_timeout(AXEYUM_TIMEOUT) {
        Ok(outcome) => Bounded::Decided(outcome),
        Err(mpsc::RecvTimeoutError::Timeout) => Bounded::Timeout,
        // The worker dropped its sender without sending: it panicked or `solve`
        // returned an error. Either way it is a crash, not a verdict.
        Err(mpsc::RecvTimeoutError::Disconnected) => Bounded::Crashed,
    }
}

/// Decide an instance with Z3 over the `QF_BV` theory, with a tiny wall-clock
/// timeout. Returns `Unknown` on timeout/incompleteness (the instance is then
/// skipped — Z3 cannot adjudicate it).
fn z3_decide(inst: &Instance) -> Verdict {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32(
        "timeout",
        u32::try_from(Z3_TIMEOUT.as_millis()).unwrap_or(u32::MAX),
    );
    solver.set_params(&params);
    for atom in inst.to_z3() {
        solver.assert(&atom);
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

/// Running counters for the sweep.
#[derive(Default)]
struct Tally {
    total: u64,
    jointly_decided: u64,
    agreements: u64,
    axeyum_unknown: u64,
    axeyum_timeout: u64,
    axeyum_crashed: u64,
    z3_unknown_skipped: u64,
    cvc5_sampled: u64,
    cvc5_decided: u64,
    cvc5_unknown_skipped: u64,
    three_way_agreements: u64,
    bitwuzla_sampled: u64,
    bitwuzla_decided: u64,
    bitwuzla_unknown_skipped: u64,
    bitwuzla_agreements: u64,
    four_way_agreements: u64,
    proof_selected_unsat: u64,
    cnf_drat_proved: u64,
    cnf_drat_inconclusive: u64,
    cnf_drat_inconclusive_seeds: Vec<u64>,
    end_to_end_certified: u64,
    end_to_end_not_certified: u64,
    end_to_end_not_certified_seeds: Vec<u64>,
    sat_replayed: u64,
    sat_replay_indeterminate: u64,
    /// The first crashing instance, kept for the report.
    first_crash: Option<(u64, String)>,
}

#[derive(Default)]
struct Coverage {
    widths: BTreeSet<u32>,
    operators: BTreeSet<&'static str>,
    edge_instances: BTreeMap<&'static str, u64>,
}

impl Coverage {
    fn observe(&mut self, instance: &Instance) {
        instance.record_coverage(
            &mut self.widths,
            &mut self.operators,
            &mut self.edge_instances,
        );
    }
}

struct NeutralOracles {
    cvc5: Option<String>,
    cvc5_stride: u64,
    bitwuzla: Option<String>,
    bitwuzla_stride: u64,
}

impl NeutralOracles {
    fn configured() -> Self {
        let result = Self {
            cvc5: cvc5_bin(),
            cvc5_stride: cvc5_sample_stride(),
            bitwuzla: bitwuzla_bin(),
            bitwuzla_stride: bitwuzla_sample_stride(),
        };
        if std::env::var("AXEYUM_REQUIRE_CVC5").as_deref() == Ok("1") {
            assert!(
                result.cvc5.is_some(),
                "AXEYUM_REQUIRE_CVC5=1 but no working cvc5 binary was found"
            );
        }
        if std::env::var("AXEYUM_REQUIRE_BITWUZLA").as_deref() == Ok("1") {
            assert!(
                result.bitwuzla.is_some(),
                "AXEYUM_REQUIRE_BITWUZLA=1 but no working Bitwuzla binary was found"
            );
        }
        result
    }
}

fn record_unsat_proof_coverage(
    seed: u64,
    inst: &Instance,
    tally: &mut Tally,
    proof_deadline: Option<Duration>,
) {
    tally.proof_selected_unsat += 1;
    let (arena, _symbols, assertions) = inst.build();

    if proof_verbose() {
        eprintln!("[bv-proof] seed={seed} CNF DRAT start");
    }
    let cnf_deadline = proof_deadline.map(|duration| Instant::now() + duration);
    match export_qf_bv_unsat_proof_within(&arena, &assertions, cnf_deadline) {
        Ok(UnsatProofOutcome::Proved(proof)) => {
            assert_eq!(
                proof.recheck(),
                Ok(true),
                "CNF DRAT recheck failed:\n{}",
                inst.to_smt2()
            );
            tally.cnf_drat_proved += 1;
        }
        Ok(UnsatProofOutcome::Inconclusive) => {
            tally.cnf_drat_inconclusive += 1;
            tally.cnf_drat_inconclusive_seeds.push(seed);
        }
        Ok(UnsatProofOutcome::Satisfiable) => panic!(
            "proof route returned satisfiable for a jointly-UNSAT formula:\n{}",
            inst.to_smt2()
        ),
        Err(error) => panic!(
            "CNF proof route failed for a valid jointly-UNSAT formula: {error}\n{}",
            inst.to_smt2()
        ),
    }

    if proof_verbose() {
        eprintln!("[bv-proof] seed={seed} end-to-end start");
    }
    let end_to_end_deadline = proof_deadline.map(|duration| Instant::now() + duration);
    match certify_qf_bv_unsat_end_to_end_within(&arena, &assertions, end_to_end_deadline) {
        Ok(outcome @ EndToEndUnsatOutcome::Certified { .. }) => {
            assert_eq!(
                outcome.recheck(),
                Ok(true),
                "end-to-end certificate recheck failed:\n{}",
                inst.to_smt2()
            );
            tally.end_to_end_certified += 1;
        }
        Ok(EndToEndUnsatOutcome::NotCertified) => {
            tally.end_to_end_not_certified += 1;
            tally.end_to_end_not_certified_seeds.push(seed);
        }
        Ok(EndToEndUnsatOutcome::Satisfiable) => panic!(
            "end-to-end route returned satisfiable for a jointly-UNSAT formula:\n{}",
            inst.to_smt2()
        ),
        Err(error) => panic!(
            "end-to-end route failed for a valid jointly-UNSAT formula: {error}\n{}",
            inst.to_smt2()
        ),
    }
    if proof_verbose() {
        eprintln!("[bv-proof] seed={seed} complete");
    }
}

fn run_cvc5_oracle(
    seed: u64,
    smt2: &str,
    binary: Option<&str>,
    expected: Verdict,
    tally: &mut Tally,
) -> Option<Verdict> {
    let binary = binary?;
    tally.cvc5_sampled += 1;
    let verdict = match cvc5_decide_detailed(binary, smt2, Z3_TIMEOUT) {
        Cvc5Verdict::Sat => Verdict::Sat,
        Cvc5Verdict::Unsat => Verdict::Unsat,
        Cvc5Verdict::Unknown => {
            tally.cvc5_unknown_skipped += 1;
            return None;
        }
        Cvc5Verdict::Failure(detail) => panic!(
            "cvc5 failed on valid generated QF_BV (seed {seed}): {detail}\n\
             Complete reproducer:\n{smt2}"
        ),
    };
    tally.cvc5_decided += 1;
    assert_eq!(
        verdict, expected,
        "cvc5 disagreement (seed {seed}): expected={expected:?}, cvc5={verdict:?}\n\
         Complete reproducer:\n{smt2}"
    );
    tally.three_way_agreements += 1;
    Some(verdict)
}

fn run_bitwuzla_oracle(
    seed: u64,
    smt2: &str,
    binary: Option<&str>,
    expected: Verdict,
    tally: &mut Tally,
) -> Option<Verdict> {
    let binary = binary?;
    tally.bitwuzla_sampled += 1;
    let verdict = match bitwuzla_decide_detailed(binary, smt2, Z3_TIMEOUT) {
        BitwuzlaVerdict::Sat => Verdict::Sat,
        BitwuzlaVerdict::Unsat => Verdict::Unsat,
        BitwuzlaVerdict::Unknown => {
            tally.bitwuzla_unknown_skipped += 1;
            return None;
        }
        BitwuzlaVerdict::Failure(detail) => panic!(
            "Bitwuzla failed on valid generated QF_BV (seed {seed}): {detail}\n\
             Complete reproducer:\n{smt2}"
        ),
    };
    tally.bitwuzla_decided += 1;
    assert_eq!(
        verdict, expected,
        "Bitwuzla disagreement (seed {seed}): expected={expected:?}, Bitwuzla={verdict:?}\n\
         Complete reproducer:\n{smt2}"
    );
    tally.bitwuzla_agreements += 1;
    Some(verdict)
}

/// Decide one instance with both engines and fold the result into `t`. Panics
/// only on a genuine soundness violation (a non-replaying Sat, or a jointly-
/// decided Sat/Unsat disagreement) — the whole point of the gate.
fn run_instance(
    seed: u64,
    inst: &Instance,
    t: &mut Tally,
    cvc5: Option<&str>,
    bitwuzla: Option<&str>,
    sample_proof: bool,
    proof_deadline: Option<Duration>,
) {
    // --- axeyum: the default pure-Rust front door, hard-capped. ----------
    let outcome = match solve_axeyum_bounded(inst.clone()) {
        Bounded::Decided(o) => o,
        Bounded::Timeout => {
            t.axeyum_timeout += 1;
            return;
        }
        Bounded::Crashed => {
            t.axeyum_crashed += 1;
            if t.first_crash.is_none() {
                t.first_crash = Some((seed, inst.dump()));
            }
            return;
        }
    };
    let ax_label = outcome.verdict;

    // A `Sat` whose model VIOLATES an original atom under the independent ground
    // evaluator is a wrong sat — regardless of Z3.
    if let Replay::Violated { atom, model } = &outcome.replay {
        panic!(
            "WRONG SAT (seed {seed}): axeyum returned Sat but its model makes \
             atom[{atom}] FALSE under the independent ground evaluator — a \
             soundness bug.\nmodel: {model}\ninstance:\n{}\n\
             Complete SMT-LIB reproducer:\n{}",
            inst.dump(),
            inst.to_smt2()
        );
    }
    match outcome.replay {
        Replay::AllTrue => t.sat_replayed += 1,
        Replay::Indeterminate => t.sat_replay_indeterminate += 1,
        Replay::NotSat | Replay::Violated { .. } => {}
    }

    if ax_label == Verdict::Unknown {
        t.axeyum_unknown += 1;
    }

    // --- Z3 oracle: a direct QF_BV query, tiny timeout. ------------------
    let z3_label = z3_decide(inst);
    if z3_label == Verdict::Unknown {
        t.z3_unknown_skipped += 1;
        return;
    }
    // Both sides committed to Sat/Unsat (axeyum may still be Unknown).
    if ax_label == Verdict::Unknown {
        return;
    }

    t.jointly_decided += 1;

    // THE SOUNDNESS GATE: a jointly-decided instance must AGREE.
    if ax_label == z3_label {
        t.agreements += 1;
    } else {
        let model_dump = outcome
            .model_dump
            .unwrap_or_else(|| "(no axeyum model)".to_string());
        panic!(
            "DISAGREEMENT (seed {seed}): axeyum = {ax_label:?}, Z3 = {z3_label:?}.\n\
             This is a {} soundness bug.\n\
             axeyum model: {model_dump}\n\
             instance:\n{}\n\
             Complete SMT-LIB reproducer:\n{}",
            match (ax_label, z3_label) {
                (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                _ => "verdict",
            },
            inst.dump(),
            inst.to_smt2()
        );
    }

    if sample_proof && ax_label == Verdict::Unsat {
        record_unsat_proof_coverage(seed, inst, t, proof_deadline);
    }

    let smt2 = inst.to_smt2();
    let cvc5_label = run_cvc5_oracle(seed, &smt2, cvc5, ax_label, t);
    let bitwuzla_label = run_bitwuzla_oracle(seed, &smt2, bitwuzla, ax_label, t);
    if cvc5_label.is_some() && bitwuzla_label.is_some() {
        t.four_way_agreements += 1;
    }
}

fn eq_atom(lhs: Term, rhs: Term) -> Atom {
    Atom::Cmp {
        lhs,
        rhs,
        cmp: BvCmp::Eq,
    }
}

fn glaurung_named_instances() -> Vec<(&'static str, Verdict, Instance)> {
    let concat = Instance {
        width: 64,
        num_vars: 0,
        atoms: vec![eq_atom(
            Term::Concat(
                Box::new(Term::Const {
                    width: 56,
                    value: 0x12,
                }),
                Box::new(Term::ZeroExt {
                    by: 7,
                    a: Box::new(Term::Const { width: 1, value: 1 }),
                }),
            ),
            Term::Const {
                width: 64,
                value: 0x1201,
            },
        )],
    };

    let extension_source = 0xdead_beef_0000_1234_u128;
    let extension = Instance {
        width: 64,
        num_vars: 1,
        atoms: vec![
            eq_atom(
                Term::Var(0),
                Term::Const {
                    width: 64,
                    value: extension_source,
                },
            ),
            eq_atom(
                Term::ZeroExt {
                    by: 32,
                    a: Box::new(Term::Extract {
                        hi: 31,
                        lo: 0,
                        a: Box::new(Term::Var(0)),
                    }),
                },
                Term::Const {
                    width: 64,
                    value: 0x1234,
                },
            ),
        ],
    };

    let empty_after_unsat = Instance {
        width: 8,
        num_vars: 1,
        atoms: vec![
            eq_atom(Term::Var(0), Term::Const { width: 8, value: 1 }),
            eq_atom(Term::Var(0), Term::Const { width: 8, value: 2 }),
        ],
    };

    let wide_value = (1_u128 << 100) | 0x1234_5678_9abc_def0_u128;
    let wide = Instance {
        width: 128,
        num_vars: 1,
        atoms: vec![eq_atom(
            Term::Var(0),
            Term::Const {
                width: 128,
                value: wide_value,
            },
        )],
    };

    vec![
        ("concat-declared-halves", Verdict::Sat, concat),
        ("extension-declared-source", Verdict::Sat, extension),
        ("empty-model-after-unsat", Verdict::Unsat, empty_after_unsat),
        ("w128-adapter-constant", Verdict::Sat, wide),
    ]
}

#[test]
fn glaurung_width_contract_regressions_are_strict() {
    let mut arena = TermArena::new();
    let high = arena.bv_const(56, 0x12).unwrap();
    let low = arena.bv_const(1, 1).unwrap();
    let malformed_concat = arena.concat(high, low).unwrap();
    let concat_error = arena.extract(63, 8, malformed_concat).unwrap_err();
    assert!(
        concat_error.to_string().contains("out of range"),
        "unexpected concat-contract error: {concat_error}"
    );

    let child = arena.bv_var("child", 64).unwrap();
    let malformed_extension = arena.zero_ext(32, child).unwrap();
    let expected_64 = arena.bv_const(64, 0).unwrap();
    let extension_error = arena.eq(malformed_extension, expected_64).unwrap_err();
    assert!(
        extension_error.to_string().contains("sort"),
        "unexpected extension-contract error: {extension_error}"
    );

    let constant_error = arena.bv_const(8, 0x1000).unwrap_err();
    assert!(
        constant_error.to_string().contains("fit"),
        "unexpected constant-contract error: {constant_error}"
    );
}

#[test]
fn glaurung_named_qfbv_controls_agree_and_replay() {
    let cvc5 = cvc5_bin();
    let bitwuzla = bitwuzla_bin();
    if std::env::var("AXEYUM_REQUIRE_CVC5").as_deref() == Ok("1") {
        assert!(
            cvc5.is_some(),
            "AXEYUM_REQUIRE_CVC5=1 but no working cvc5 binary was found"
        );
    }
    if std::env::var("AXEYUM_REQUIRE_BITWUZLA").as_deref() == Ok("1") {
        assert!(
            bitwuzla.is_some(),
            "AXEYUM_REQUIRE_BITWUZLA=1 but no working Bitwuzla binary was found"
        );
    }

    let named = glaurung_named_instances();
    let mut tally = Tally::default();
    for (index, (name, expected, instance)) in named.iter().enumerate() {
        eprintln!("[bv-fuzz named] {name}");
        assert_eq!(
            z3_decide(instance),
            *expected,
            "named control has the wrong expected verdict:\n{}",
            instance.to_smt2()
        );
        run_instance(
            0x474c_4155_5255_4e47_u64 + u64::try_from(index).unwrap(),
            instance,
            &mut tally,
            cvc5.as_deref(),
            bitwuzla.as_deref(),
            false,
            None,
        );
    }
    assert_eq!(tally.jointly_decided, 4);
    assert_eq!(tally.agreements, 4);
    if cvc5.is_some() {
        assert_eq!(tally.three_way_agreements, 4);
    }
    if bitwuzla.is_some() {
        assert_eq!(tally.bitwuzla_agreements, 4);
    }
    if cvc5.is_some() && bitwuzla.is_some() {
        assert_eq!(tally.four_way_agreements, 4);
    }

    // The consumer bug was not that an empty model is intrinsically invalid:
    // a closed true formula legitimately has one. The contract is that only a
    // Sat result exposes it, while the contradictory control is structurally
    // Unsat and therefore carries no model payload at all.
    let (_, _, closed_sat) = &named[0];
    let (mut arena, _symbols, assertions) = closed_sat.build();
    let CheckResult::Sat(model) = solve(&mut arena, &assertions, &SolverConfig::default()).unwrap()
    else {
        panic!("closed concat control must be sat");
    };
    assert!(
        model.is_empty(),
        "closed SAT control should have an empty model"
    );

    let (_, _, contradictory) = &named[2];
    let (mut arena, _symbols, assertions) = contradictory.build();
    assert!(matches!(
        solve(&mut arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));

    // Exercise Axeyum's actual linked Z3 adapter, not only the independently
    // constructed direct-Z3 AST above. This is the exact boundary that once
    // narrowed Glaurung's 128-bit constant through u64.
    let (_, _, wide) = &named[3];
    let (arena, _symbols, assertions) = wide.build();
    let result = Z3Backend::new()
        .check(
            &arena,
            &assertions,
            &SolverConfig::default().with_timeout(Z3_TIMEOUT),
        )
        .expect("linked Z3 adapter accepts the full-width control");
    let CheckResult::Sat(model) = result else {
        panic!(
            "linked Z3 adapter failed the full-width control:\n{}",
            wide.to_smt2()
        );
    };
    for &assertion in &assertions {
        assert_eq!(
            eval(&arena, assertion, &model.to_assignment()).unwrap(),
            Value::Bool(true),
            "linked Z3 adapter model must replay on the 128-bit original"
        );
    }
}

fn assert_generator_coverage(profile: GeneratorProfile, coverage: &Coverage) {
    assert_eq!(
        &coverage.widths,
        &WIDTHS.into_iter().collect(),
        "the deterministic generator missed a declared width"
    );
    let missing_operators: Vec<_> = REQUIRED_OPERATORS
        .iter()
        .copied()
        .filter(|operator| !coverage.operators.contains(operator))
        .collect();
    assert!(
        missing_operators.is_empty(),
        "the deterministic generator missed operators: {missing_operators:?}"
    );
    if profile == GeneratorProfile::EdgeV1 {
        let missing_edges: Vec<_> = REQUIRED_EDGE_CASES
            .iter()
            .copied()
            .filter(|edge| coverage.edge_instances.get(edge).copied().unwrap_or(0) == 0)
            .collect();
        assert!(
            missing_edges.is_empty(),
            "edge-v1 missed required semantic corners: {missing_edges:?}"
        );
    }
}

fn sampled_seed_count(seed_start: u64, seed_end: u64, stride: u64) -> u64 {
    let remainder = seed_start % stride;
    let first = if remainder == 0 {
        seed_start
    } else {
        seed_start
            .checked_add(stride - remainder)
            .expect("sample start overflow")
    };
    if first >= seed_end {
        0
    } else {
        1 + (seed_end - 1 - first) / stride
    }
}

#[allow(clippy::too_many_arguments)]
fn assert_neutral_coverage(
    name: &str,
    present: bool,
    seed_start: u64,
    seed_end: u64,
    stride: u64,
    sampled: u64,
    decided: u64,
    unknown: u64,
    agreements: u64,
    require_all_decided_env: &str,
) {
    if !present {
        return;
    }
    let expected_samples = sampled_seed_count(seed_start, seed_end, stride);
    assert!(
        agreements >= expected_samples.min(200),
        "too few {name} agreements ({agreements}); the lane is vacuous"
    );
    if std::env::var(require_all_decided_env).as_deref() == Ok("1") {
        assert_eq!(sampled, expected_samples);
        assert_eq!(decided, expected_samples);
        assert_eq!(unknown, 0);
        assert_eq!(agreements, expected_samples);
    }
}

fn assert_proof_coverage(tally: &Tally, proof_stride: Option<u64>) {
    if proof_stride.is_none() {
        return;
    }
    assert!(tally.proof_selected_unsat > 0, "proof sample is vacuous");
    assert_eq!(
        tally.cnf_drat_proved + tally.cnf_drat_inconclusive,
        tally.proof_selected_unsat
    );
    assert_eq!(
        tally.end_to_end_certified + tally.end_to_end_not_certified,
        tally.proof_selected_unsat
    );
}

fn print_tally(
    config: SweepConfig,
    tally: &Tally,
    oracles: &NeutralOracles,
    proof_stride: Option<u64>,
    proof_deadline: Option<Duration>,
    coverage: &Coverage,
) {
    println!("=== QF_BV differential fuzz tally ===");
    println!("generator profile:    {}", config.profile.name());
    println!(
        "seed range:           {}..{}",
        config.seed_start, config.seed_end
    );
    println!("total instances:      {}", tally.total);
    println!("jointly decided:      {}", tally.jointly_decided);
    println!("agreements:           {}", tally.agreements);
    println!("axeyum Unknown:       {}", tally.axeyum_unknown);
    println!("axeyum timeout:       {}", tally.axeyum_timeout);
    println!("axeyum CRASHED:       {}", tally.axeyum_crashed);
    println!("Z3 Unknown (skipped): {}", tally.z3_unknown_skipped);
    println!("cvc5 sample stride:   {}", oracles.cvc5_stride);
    println!("cvc5 sampled:         {}", tally.cvc5_sampled);
    println!("cvc5 decided:         {}", tally.cvc5_decided);
    println!("cvc5 Unknown/skipped: {}", tally.cvc5_unknown_skipped);
    println!("three-way agreements: {}", tally.three_way_agreements);
    println!("Bitwuzla stride:      {}", oracles.bitwuzla_stride);
    println!("Bitwuzla sampled:     {}", tally.bitwuzla_sampled);
    println!("Bitwuzla decided:     {}", tally.bitwuzla_decided);
    println!("Bitwuzla Unknown:     {}", tally.bitwuzla_unknown_skipped);
    println!("Bitwuzla agreements:  {}", tally.bitwuzla_agreements);
    println!("four-way agreements:  {}", tally.four_way_agreements);
    println!("proof sample stride:  {proof_stride:?} (width <= 8)");
    println!("proof deadline:       {proof_deadline:?} per route");
    println!("proof-selected UNSAT: {}", tally.proof_selected_unsat);
    println!("CNF DRAT proved:       {}", tally.cnf_drat_proved);
    println!("CNF DRAT inconclusive: {}", tally.cnf_drat_inconclusive);
    println!(
        "CNF inconclusive seeds: {:?}",
        tally.cnf_drat_inconclusive_seeds
    );
    println!("end-to-end certified: {}", tally.end_to_end_certified);
    println!("end-to-end uncovered: {}", tally.end_to_end_not_certified);
    println!(
        "end-to-end uncovered seeds: {:?}",
        tally.end_to_end_not_certified_seeds
    );
    println!("Sat replays verified: {}", tally.sat_replayed);
    println!("Sat replay declined:  {}", tally.sat_replay_indeterminate);
    println!("covered widths:       {:?}", coverage.widths);
    println!("covered operators:    {:?}", coverage.operators);
    println!("edge-case instances:  {:?}", coverage.edge_instances);
    println!("DISAGREEMENTS:        0");
    if let Some((seed, dump)) = &tally.first_crash {
        println!("--- first crashing instance (seed {seed}) ---\n{dump}");
    }
}

fn json_string_array<'a>(values: impl IntoIterator<Item = &'a str>) -> String {
    let values: Vec<_> = values
        .into_iter()
        .map(|value| format!("\"{value}\""))
        .collect();
    format!("[{}]", values.join(","))
}

fn json_u64_map(values: &BTreeMap<&'static str, u64>) -> String {
    let values: Vec<_> = values
        .iter()
        .map(|(name, count)| format!("\"{name}\":{count}"))
        .collect();
    format!("{{{}}}", values.join(","))
}

#[allow(clippy::too_many_arguments)]
fn write_report(
    config: SweepConfig,
    tally: &Tally,
    oracles: &NeutralOracles,
    coverage: &Coverage,
    elapsed: Duration,
) {
    let Ok(path) = std::env::var("AXEYUM_QFBV_REPORT_PATH") else {
        return;
    };
    assert!(
        !path.is_empty(),
        "AXEYUM_QFBV_REPORT_PATH must not be empty"
    );
    let widths = coverage
        .widths
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(",");
    let operators = json_string_array(coverage.operators.iter().copied());
    let edge_cases = json_u64_map(&coverage.edge_instances);
    let report = format!(
        concat!(
            "{{\n",
            "  \"schema\": \"axeyum.qfbv-multi-oracle-fuzz.v3\",\n",
            "  \"generator_profile\": \"{}\",\n",
            "  \"seed_start\": {},\n",
            "  \"seed_end_exclusive\": {},\n",
            "  \"instances\": {},\n",
            "  \"elapsed_ms\": {},\n",
            "  \"axeyum_z3\": {{\"jointly_decided\":{},\"agreements\":{},",
            "\"axeyum_unknown\":{},\"axeyum_timeout\":{},\"axeyum_crashed\":{},",
            "\"z3_unknown\":{},\"sat_replayed\":{},\"sat_replay_indeterminate\":{}}},\n",
            "  \"cvc5\": {{\"present\":{},\"stride\":{},\"sampled\":{},",
            "\"decided\":{},\"unknown\":{},\"agreements\":{}}},\n",
            "  \"bitwuzla\": {{\"present\":{},\"stride\":{},\"sampled\":{},",
            "\"decided\":{},\"unknown\":{},\"agreements\":{}}},\n",
            "  \"four_way_agreements\": {},\n",
            "  \"coverage\": {{\"widths\":[{}],\"operators\":{},\"edge_case_instances\":{}}},\n",
            "  \"disagreements\": 0\n",
            "}}\n"
        ),
        config.profile.name(),
        config.seed_start,
        config.seed_end,
        config.instances,
        elapsed.as_millis(),
        tally.jointly_decided,
        tally.agreements,
        tally.axeyum_unknown,
        tally.axeyum_timeout,
        tally.axeyum_crashed,
        tally.z3_unknown_skipped,
        tally.sat_replayed,
        tally.sat_replay_indeterminate,
        oracles.cvc5.is_some(),
        oracles.cvc5_stride,
        tally.cvc5_sampled,
        tally.cvc5_decided,
        tally.cvc5_unknown_skipped,
        tally.three_way_agreements,
        oracles.bitwuzla.is_some(),
        oracles.bitwuzla_stride,
        tally.bitwuzla_sampled,
        tally.bitwuzla_decided,
        tally.bitwuzla_unknown_skipped,
        tally.bitwuzla_agreements,
        tally.four_way_agreements,
        widths,
        operators,
        edge_cases,
    );
    let path = Path::new(&path);
    if let Some(parent) = path.parent()
        && !parent.as_os_str().is_empty()
    {
        fs::create_dir_all(parent).unwrap_or_else(|error| {
            panic!(
                "failed to create report directory {}: {error}",
                parent.display()
            )
        });
    }
    fs::write(path, report)
        .unwrap_or_else(|error| panic!("failed to write report {}: {error}", path.display()));
}

fn run_sweep(
    config: SweepConfig,
    oracles: &NeutralOracles,
    proof_stride: Option<u64>,
    proof_deadline: Option<Duration>,
) -> (Tally, Coverage) {
    let mut tally = Tally::default();
    let mut coverage = Coverage::default();
    for seed in config.seed_start..config.seed_end {
        tally.total += 1;
        if (seed - config.seed_start).is_multiple_of(250) {
            eprintln!(
                "[bv-fuzz] seed {seed}/{} (joint={}, agree={}, \
                 ax_unknown={}, ax_timeout={}, ax_crash={})",
                config.seed_end,
                tally.jointly_decided,
                tally.agreements,
                tally.axeyum_unknown,
                tally.axeyum_timeout,
                tally.axeyum_crashed
            );
        }
        let mut rng = Lcg::new(seed);
        let instance = Instance::generate(&mut rng, config.profile, seed);
        coverage.observe(&instance);
        let cvc5 = seed
            .is_multiple_of(oracles.cvc5_stride)
            .then_some(oracles.cvc5.as_deref())
            .flatten();
        let bitwuzla = seed
            .is_multiple_of(oracles.bitwuzla_stride)
            .then_some(oracles.bitwuzla.as_deref())
            .flatten();
        let sample_proof =
            proof_stride.is_some_and(|stride| seed.is_multiple_of(stride) && instance.width <= 8);
        run_instance(
            seed,
            &instance,
            &mut tally,
            cvc5,
            bitwuzla,
            sample_proof,
            proof_deadline,
        );
    }
    (tally, coverage)
}

fn assert_sweep(
    config: SweepConfig,
    tally: &Tally,
    oracles: &NeutralOracles,
    coverage: &Coverage,
    proof_stride: Option<u64>,
) {
    assert!(
        tally.jointly_decided > 100,
        "too few jointly-decided instances ({}); the differential gate is vacuous",
        tally.jointly_decided
    );
    assert_generator_coverage(config.profile, coverage);
    assert_neutral_coverage(
        "cvc5",
        oracles.cvc5.is_some(),
        config.seed_start,
        config.seed_end,
        oracles.cvc5_stride,
        tally.cvc5_sampled,
        tally.cvc5_decided,
        tally.cvc5_unknown_skipped,
        tally.three_way_agreements,
        "AXEYUM_REQUIRE_CVC5_ALL_DECIDED",
    );
    assert_neutral_coverage(
        "Bitwuzla",
        oracles.bitwuzla.is_some(),
        config.seed_start,
        config.seed_end,
        oracles.bitwuzla_stride,
        tally.bitwuzla_sampled,
        tally.bitwuzla_decided,
        tally.bitwuzla_unknown_skipped,
        tally.bitwuzla_agreements,
        "AXEYUM_REQUIRE_BITWUZLA_ALL_DECIDED",
    );
    assert_proof_coverage(tally, proof_stride);
}

#[test]
fn bv_differential_fuzz_disagree_zero() {
    let started = Instant::now();
    // Worker `solve` panics are *caught* (a crash is adjudication-neutral, not a
    // verdict). Install a panic hook that stays silent for panics originating in
    // solver/crate source (so thousands of caught crashes don't flood stderr) but
    // still prints panics from *this test file* — the genuine soundness-gate
    // panics — at full volume.
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let from_this_test = info
            .location()
            .is_some_and(|loc| loc.file().ends_with("bv_differential_fuzz.rs"));
        if from_this_test {
            default_hook(info);
        }
    }));

    let config = SweepConfig::configured();
    let oracles = NeutralOracles::configured();
    let proof_stride = proof_sample_stride();
    let proof_deadline = proof_deadline();
    let (tally, coverage) = run_sweep(config, &oracles, proof_stride, proof_deadline);
    print_tally(
        config,
        &tally,
        &oracles,
        proof_stride,
        proof_deadline,
        &coverage,
    );
    assert_sweep(config, &tally, &oracles, &coverage, proof_stride);
    write_report(config, &tally, &oracles, &coverage, started.elapsed());
}

/// Pretty-print an axeyum model's variable bindings.
fn dump_model(syms: &[SymbolId], model: &axeyum_solver::Model) -> String {
    let mut parts = Vec::new();
    for (i, &s) in syms.iter().enumerate() {
        let v = model.get(s);
        parts.push(format!("{}={:?}", VAR_NAMES[i], v));
    }
    parts.join(", ")
}
