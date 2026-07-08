//! Per-query `Fpa2Bv` trust-step sub-case (task #69).
//!
//! FP → BV lowering (ADR-0023) happens eagerly at parse time, so by the time the
//! `QF_BV` evidence path decides a query the FP op-set is gone. The parser preserves
//! it on [`axeyum_smtlib::FpUsage`], and [`produce_evidence_smtlib`] attaches an
//! [`TrustId::Fpa2Bv`] [`TrustStep`] to any FP `unsat`:
//!
//! - **`certified: true`** iff every FP operator the reduction lowered is
//!   by-construction faithful (at the guarded `≤128`-bit widths): the exact bit ops
//!   `fp.neg`/`fp.abs`, the category predicates `fp.isNaN`/`isInfinite`/`isZero`/
//!   `isNormal`/`isSubnormal`, the sign predicates `fp.isNegative`/`isPositive`
//!   (`sign ∧ ¬NaN`), and the **proven-faithful comparison circuits**
//!   `fp.eq`/`lt`/`leq`/`gt`/`geq` (width-independent monotone `order_key` +
//!   FP8-exhaustive witness). See `axeyum-fp/tests/fpa2bv_simple_faithfulness.rs` and
//!   `fpa2bv_faithfulness.rs`.
//! - **`certified: false`** for any query using a rounding-bearing operator
//!   (`fp.add`/`sub`/`mul`/`div`/`rem`/`fma`/`sqrt`/`min`/`max`) or a conversion
//!   (`to_fp`, `fp.to_ubv`, …) — those need the by-construction rounding-circuit
//!   proof (task #70).
//!
//! The global [`TrustId::Fpa2Bv::is_certified`] stays `false` (not every FP query
//! qualifies); this is the per-run [`TrustStep::certified`] flag, exactly like the
//! `XorGaussian` pure-Gauss and `IntBlast` proven-box sub-cases.

use std::time::Duration;

use axeyum_solver::{SolverConfig, TrustId, TrustStep, produce_evidence_smtlib};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

/// The `Fpa2Bv` trust step recorded for a query, or `None` if the result carried
/// no `Fpa2Bv` step at all.
fn fpa2bv_step(input: &str) -> Option<TrustStep> {
    let report = produce_evidence_smtlib(input, &config()).expect("produce evidence");
    report
        .trusted_steps
        .iter()
        .find(|s| s.id == TrustId::Fpa2Bv)
        .copied()
}

// --- (a) certified: true — only structurally-exact simple ops ----------------

/// `isNaN(x) ∧ isZero(x)` is UNSAT (NaN needs an all-ones exponent, zero an
/// all-zero one — mutually exclusive). Both operators are structurally exact, so
/// the `Fpa2Bv` step is **certified**.
#[test]
fn isnan_and_iszero_is_certified() {
    let step = fpa2bv_step(
        "(set-logic QF_FP)\n\
         (declare-const x Float32)\n\
         (assert (fp.isNaN x))\n\
         (assert (fp.isZero x))\n\
         (check-sat)\n",
    )
    .expect("FP unsat must carry an Fpa2Bv trust step");
    assert_eq!(
        step,
        TrustStep {
            id: TrustId::Fpa2Bv,
            certified: true,
        },
        "isNaN/isZero are structurally exact — Fpa2Bv must be certified"
    );
}

/// `isInfinite(abs(x)) ∧ isZero(x)` is UNSAT (`abs` preserves ±∞, and a zero is
/// not infinite). Uses `fp.abs`, `fp.isInfinite`, `fp.isZero` — all structurally
/// exact — so the `Fpa2Bv` step is **certified**.
#[test]
fn abs_infinite_and_zero_is_certified() {
    let step = fpa2bv_step(
        "(set-logic QF_FP)\n\
         (declare-const x Float32)\n\
         (assert (fp.isInfinite (fp.abs x)))\n\
         (assert (fp.isZero x))\n\
         (check-sat)\n",
    )
    .expect("FP unsat must carry an Fpa2Bv trust step");
    assert!(
        step.certified,
        "abs/isInfinite/isZero are structurally exact — Fpa2Bv must be certified"
    );
}

/// `isNormal(neg(x)) ∧ isSubnormal(x)` is UNSAT (`neg` flips only the sign, so it
/// preserves the exponent field — a subnormal stays subnormal, never normal).
/// Uses `fp.neg`, `fp.isNormal`, `fp.isSubnormal` — all structurally exact.
#[test]
fn neg_normal_and_subnormal_is_certified() {
    let step = fpa2bv_step(
        "(set-logic QF_FP)\n\
         (declare-const x Float16)\n\
         (assert (fp.isNormal (fp.neg x)))\n\
         (assert (fp.isSubnormal x))\n\
         (check-sat)\n",
    )
    .expect("FP unsat must carry an Fpa2Bv trust step");
    assert!(
        step.certified,
        "neg/isNormal/isSubnormal are structurally exact — Fpa2Bv must be certified"
    );
}

// --- (b) certified: false — a non-simple op disqualifies ---------------------

/// `fp.lt(x, x)` is UNSAT (irreflexive; even a non-NaN `x < x` is false, NaN is
/// unordered). `fp.lt` is a **proven-faithful comparison circuit** (`¬NaN ∧
/// ¬both-zero ∧ ult(order_key)`, width-independent monotonicity + FP8-exhaustive
/// witness), so the `Fpa2Bv` step is **certified**.
#[test]
fn lt_self_is_certified() {
    let step = fpa2bv_step(
        "(set-logic QF_FP)\n\
         (declare-const x Float32)\n\
         (assert (fp.lt x x))\n\
         (check-sat)\n",
    )
    .expect("FP unsat must carry an Fpa2Bv trust step");
    assert_eq!(
        step,
        TrustStep {
            id: TrustId::Fpa2Bv,
            certified: true,
        },
        "fp.lt is a proven-faithful comparison — Fpa2Bv must be certified"
    );
}

/// A single non-simple op (`fp.add`) anywhere in the query disqualifies the whole
/// `Fpa2Bv` step, even alongside otherwise-simple operators. `isNaN(add(rne,x,x))
/// ∧ isZero(add(rne,x,x))` is UNSAT (a value cannot be both NaN and zero), but the
/// `fp.add` means the reduction is not all-simple → **not certified**.
#[test]
fn add_with_simple_ops_is_not_certified() {
    let step = fpa2bv_step(
        "(set-logic QF_FP)\n\
         (declare-const x Float32)\n\
         (assert (fp.isNaN (fp.add roundNearestTiesToEven x x)))\n\
         (assert (fp.isZero (fp.add roundNearestTiesToEven x x)))\n\
         (check-sat)\n",
    )
    .expect("FP unsat must carry an Fpa2Bv trust step");
    assert!(
        !step.certified,
        "fp.add is non-simple — one such op disqualifies the whole Fpa2Bv step"
    );
}

/// `fp.isNegative`/`fp.isPositive` are structurally-exact sign-bit classification
/// predicates (`sign ∧ ¬NaN` / `¬sign ∧ ¬NaN`), faithful by construction at every
/// width — SMT-LIB and both oracles (Z3, cvc5) classify `−0` as negative
/// (`af6c8bf`/GAP-F2), and the F16-exhaustive witness confirms the circuit. So a
/// query using ONLY them IS certified. `isNegative(x) ∧ isPositive(x)` is UNSAT
/// (sign bit cannot be both set and clear under the shared not-NaN guard).
#[test]
fn isnegative_ispositive_is_certified() {
    let step = fpa2bv_step(
        "(set-logic QF_FP)\n\
         (declare-const x Float32)\n\
         (assert (fp.isNegative x))\n\
         (assert (fp.isPositive x))\n\
         (check-sat)\n",
    )
    .expect("FP unsat must carry an Fpa2Bv trust step");
    assert_eq!(
        step,
        TrustStep {
            id: TrustId::Fpa2Bv,
            certified: true,
        },
        "isNegative/isPositive are structurally-exact sign-bit predicates — certified"
    );
}

// --- ledger invariant --------------------------------------------------------

/// The *global* ledger bit stays a trust hole regardless of the per-query flag:
/// not every FP query qualifies, so `TrustId::Fpa2Bv::is_certified()` is `false`.
#[test]
fn global_fpa2bv_ledger_bit_stays_a_trust_hole() {
    assert!(
        !TrustId::Fpa2Bv.is_certified(),
        "the global Fpa2Bv ledger bit must remain a trust hole (per-query only)"
    );
}
