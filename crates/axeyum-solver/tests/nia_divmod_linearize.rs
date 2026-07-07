//! P2.5 Phase E.0 — `QF_NIA` div/mod Euclidean linearization (`check_with_nia`).
//!
//! Covers the two clean cvc5-regress targets this slice closes (`div.03`,
//! `mod.02`), hand-built minimal versions, the SMT-LIB `div`/`mod` sign
//! convention (`0 ≤ r < |n|`), the replay-gated `sat` guard (a relaxation-`sat`
//! that must NOT become a wrong verdict), and both directions of the Euclidean
//! identity.

use std::time::Duration;

use axeyum_ir::{Op, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, check_auto, solve_smtlib};

fn ivar(a: &mut TermArena, name: &str) -> TermId {
    let s = a.declare(name, Sort::Int).unwrap();
    a.var(s)
}

fn cfg() -> SolverConfig {
    SolverConfig::default().with_timeout(Duration::from_secs(10))
}

fn verdict_smt(text: &str) -> CheckResult {
    solve_smtlib(text, &cfg())
        .expect("solve_smtlib must not error")
        .result
}

// ---------------------------------------------------------------------------
// The real cvc5-regress targets (via the front door).
// ---------------------------------------------------------------------------

const TARGET_DIR: &str = "../../corpus/public-curated/non-incremental/QF_NIA/cvc5-regress-clean/";

fn read_target(name: &str) -> String {
    std::fs::read_to_string(format!("{TARGET_DIR}{name}"))
        .unwrap_or_else(|e| panic!("read {name}: {e}"))
}

#[test]
fn div03_real_file_unsat() {
    // n>0 ∧ x≥n ∧ (div x n)<1 — unsat over ℤ (q≤0 ∧ n>0 ⇒ n·q≤0 ⇒ x=n·q+r<n),
    // but sat over ℝ (q=0.5), so only the integer linearization refutes it.
    let r = verdict_smt(&read_target("cli__regress1__arith__div.03.smt2"));
    assert!(
        matches!(r, CheckResult::Unsat),
        "div.03 must be unsat, got {r:?}"
    );
}

#[test]
fn mod02_real_file_unsat() {
    // n≠0 ∧ (mod n n)>0 — unsat (mod n n = 0 for n≠0, via the self-division arm).
    let r = verdict_smt(&read_target("cli__regress1__arith__mod.02.smt2"));
    assert!(
        matches!(r, CheckResult::Unsat),
        "mod.02 must be unsat, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// Sound congruent div-by-zero recovery (P2.5 task #40).
//
// `div.01` / `minimal_unsat_core` are nested `div(div n n) n` chains with `n = 0`.
// They are unsat for EVERY div-by-zero value: an asserted equality among nested
// quotients propagates by congruence to a value that contradicts an asserted
// `distinct`. The fresh-per-term div-0 relaxation (the P0 fix) lost this because
// the free quotients were unrelated; the eager Ackermann congruence over the
// variable-divisor `div`/`mod` groups recovers it SOUNDLY (a monotone-valid
// consequence of `div`/`mod` being total binary functions).
// ---------------------------------------------------------------------------

#[test]
fn div01_real_file_unsat_via_congruence() {
    // n=0 ∧ div-chain equality ∧ div-chain distinct — unsat for any div-0 value.
    let r = verdict_smt(&read_target("cli__regress0__arith__div.01.smt2"));
    assert!(
        matches!(r, CheckResult::Unsat),
        "div.01 must be unsat (congruent div-0 recovery), got {r:?}"
    );
}

#[test]
fn minimal_unsat_core_real_file_unsat_via_congruence() {
    let r = verdict_smt(&read_target("cli__regress1__minimal_unsat_core.smt2"));
    assert!(
        matches!(r, CheckResult::Unsat),
        "minimal_unsat_core must be unsat (congruent div-0 recovery), got {r:?}"
    );
}

// Soundness bar #3: a formula that is SAT only under a specific div-0 value must
// NOT be refuted (distinct from the P0 shape, over the VARIABLE-divisor path).
// `n = 0 ∧ (div x n) = 5` — `div(x, 0)` is a single free value; picking it = 5 is
// a legal SMT-LIB model, so this is SAT and must never be refuted.
#[test]
fn variable_div_by_zero_specific_value_is_not_refuted() {
    let mut a = TermArena::new();
    let n = ivar(&mut a, "n");
    let x = ivar(&mut a, "x");
    let zero = a.int_const(0);
    let five = a.int_const(5);
    let n_is_0 = a.eq(n, zero).unwrap();
    let dxn = a.int_div(x, n).unwrap();
    let dxn_is_5 = a.eq(dxn, five).unwrap();
    let r = check_auto(&mut a, &[n_is_0, dxn_is_5], &cfg()).unwrap();
    assert!(
        !matches!(r, CheckResult::Unsat),
        "underspecified variable div-by-zero must not be refuted, got {r:?}"
    );
}

// Soundness bar #4a: congruence holds — `div(a,0)` and `div(b,0)` with a=b MUST be
// equal, so `a=b ∧ n=0 ∧ (div a n) != (div b n)` is UNSAT (for any div-0 value).
#[test]
fn congruent_div_by_zero_equal_dividends_forces_equal_quotients() {
    let mut a = TermArena::new();
    let n = ivar(&mut a, "n");
    let av = ivar(&mut a, "a");
    let bv = ivar(&mut a, "b");
    let zero = a.int_const(0);
    let n_is_0 = a.eq(n, zero).unwrap();
    let a_is_b = a.eq(av, bv).unwrap();
    let da = a.int_div(av, n).unwrap();
    let db = a.int_div(bv, n).unwrap();
    let da_eq_db = a.eq(da, db).unwrap();
    let distinct = a.not(da_eq_db).unwrap();
    let r = check_auto(&mut a, &[n_is_0, a_is_b, distinct], &cfg()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "a=b ⇒ div(a,0)=div(b,0) (congruence): must be unsat, got {r:?}"
    );
}

// Soundness bar #4b: congruence does NOT over-constrain — `div(a,0)` and
// `div(b,0)` with a≠b MAY differ, so `a!=b ∧ n=0 ∧ (div a n) != (div b n)` is SAT
// (the two free values are allowed to differ). Must NOT be refuted.
#[test]
fn congruent_div_by_zero_distinct_dividends_may_differ() {
    let mut a = TermArena::new();
    let n = ivar(&mut a, "n");
    let av = ivar(&mut a, "a");
    let bv = ivar(&mut a, "b");
    let zero = a.int_const(0);
    let n_is_0 = a.eq(n, zero).unwrap();
    let a_eq_b = a.eq(av, bv).unwrap();
    let a_ne_b = a.not(a_eq_b).unwrap();
    let da = a.int_div(av, n).unwrap();
    let db = a.int_div(bv, n).unwrap();
    let da_eq_db = a.eq(da, db).unwrap();
    let distinct = a.not(da_eq_db).unwrap();
    let r = check_auto(&mut a, &[n_is_0, a_ne_b, distinct], &cfg()).unwrap();
    assert!(
        !matches!(r, CheckResult::Unsat),
        "a≠b allows div(a,0)≠div(b,0): must not be refuted, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// Hand-built minimal versions (arena front door).
// ---------------------------------------------------------------------------

/// `n>0 ∧ x≥n ∧ (div x n) < 1` over Int, decided by `check_with_nia`.
#[test]
fn div03_minimal_unsat() {
    let mut a = TermArena::new();
    let x = ivar(&mut a, "x");
    let n = ivar(&mut a, "n");
    let zero = a.int_const(0);
    let one = a.int_const(1);
    let a1 = a.int_gt(n, zero).unwrap();
    let a2 = a.int_ge(x, n).unwrap();
    let dxn = a.int_div(x, n).unwrap();
    let a3 = a.int_lt(dxn, one).unwrap();
    let r = check_auto(&mut a, &[a1, a2, a3], &cfg()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "div.03-minimal unsat, got {r:?}"
    );
}

/// `n≠0 ∧ (mod n n) > 0` over Int — unsat via the self-division identity.
#[test]
fn mod02_minimal_unsat() {
    let mut a = TermArena::new();
    let n = ivar(&mut a, "n");
    let zero = a.int_const(0);
    let eq0 = a.eq(n, zero).unwrap();
    let a1 = a.not(eq0).unwrap();
    let mnn = a.int_mod(n, n).unwrap();
    let a2 = a.int_gt(mnn, zero).unwrap();
    let r = check_auto(&mut a, &[a1, a2], &cfg()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "mod.02-minimal unsat, got {r:?}"
    );
}

/// A genuinely SAT variable-divisor query: `n>0 ∧ x=5 ∧ n=2 ∧ (div x n) ⋈ ...`.
/// `check_with_nia` may decide it, but only a replaying model is acceptable —
/// this asserts we never emit a WRONG verdict on a sat instance.
#[test]
fn variable_divisor_sat_replays_or_unknown() {
    // 2*q = x with x=5, n=2: (div 5 2)=2, (mod 5 2)=1. Assert div=2 ∧ mod=1.
    let mut a = TermArena::new();
    let x = ivar(&mut a, "x");
    let n = ivar(&mut a, "n");
    let five = a.int_const(5);
    let two = a.int_const(2);
    let one = a.int_const(1);
    let ax = a.eq(x, five).unwrap();
    let an = a.eq(n, two).unwrap();
    let dxn = a.int_div(x, n).unwrap();
    let mxn = a.int_mod(x, n).unwrap();
    let ad = a.eq(dxn, two).unwrap();
    let am = a.eq(mxn, one).unwrap();
    let assertions = [ax, an, ad, am];
    let r = check_auto(&mut a, &assertions, &cfg()).unwrap();
    match r {
        CheckResult::Sat(model) => {
            // The returned model MUST replay against the original div/mod atoms.
            let asg = model.to_assignment();
            for &asrt in &assertions {
                assert_eq!(
                    eval(&a, asrt, &asg).unwrap(),
                    Value::Bool(true),
                    "sat model must replay every original atom"
                );
            }
        }
        CheckResult::Unknown(_) => {} // declining is sound
        CheckResult::Unsat => panic!("this instance is SAT (x=5,n=2); wrong unsat"),
    }
}

/// The div-by-zero underspecified case (`mod.03`-shape): `(mod x n)<0 ∧
/// (div x n)<0`. z3 finds it SAT (n=0, div/mod-by-zero unconstrained), but under
/// axeyum's total `div a 0 = 0` / `mod a 0 = a` evaluator convention it does not
/// replay — so `check_with_nia`'s relaxation-`sat` must DECLINE, never a wrong
/// `unsat`. (The width ladder may also just report Unknown/timeout.)
#[test]
fn divmod_by_zero_underspecified_declines_never_wrong_unsat() {
    let mut a = TermArena::new();
    let x = ivar(&mut a, "x");
    let n = ivar(&mut a, "n");
    let zero = a.int_const(0);
    let dxn = a.int_div(x, n).unwrap();
    let mxn = a.int_mod(x, n).unwrap();
    let a1 = a.int_lt(mxn, zero).unwrap();
    let a2 = a.int_lt(dxn, zero).unwrap();
    let r = check_auto(&mut a, &[a1, a2], &cfg()).unwrap();
    // The one thing that must never happen: a wrong unsat (z3 says sat).
    assert!(
        !matches!(r, CheckResult::Unsat),
        "mod.03-shape is SAT (n=0 free div/mod); a wrong unsat is a soundness bug, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// SMT-LIB div/mod sign convention, both directions of the Euclidean identity.
// ---------------------------------------------------------------------------

/// Ground-evaluator sanity for the SMT-LIB Euclidean `div`/`mod` convention:
/// `a = n·(div a n) + (mod a n)` and `0 ≤ (mod a n) < |n|` for `n ≠ 0`, over a
/// grid of signs. This is the convention the linearization and the `sat` replay
/// both rely on, so it is pinned here directly.
#[test]
fn euclidean_convention_both_directions() {
    for a_val in -7i128..=7 {
        for n_val in [-4i128, -3, -2, -1, 1, 2, 3, 4] {
            let mut a = TermArena::new();
            let av = a.int_const(a_val);
            let nv = a.int_const(n_val);
            let q = a.int_div(av, nv).unwrap();
            let r = a.int_mod(av, nv).unwrap();
            let asg = axeyum_ir::Assignment::new();
            let qv = match eval(&a, q, &asg).unwrap() {
                Value::Int(v) => v,
                other => panic!("div not Int: {other:?}"),
            };
            let rv = match eval(&a, r, &asg).unwrap() {
                Value::Int(v) => v,
                other => panic!("mod not Int: {other:?}"),
            };
            // Identity: a = n·q + r.
            assert_eq!(
                a_val,
                n_val * qv + rv,
                "Euclidean identity ({a_val},{n_val})"
            );
            // Range: 0 ≤ r < |n|.
            assert!(
                (0..n_val.abs()).contains(&rv),
                "mod range 0≤{rv}<|{n_val}| ({a_val},{n_val})"
            );
        }
    }
}

/// The abstraction must never abstract a *constant*-divisor div/mod as a
/// nonlinear product — those are exactly linearized upstream. Sanity that a
/// pure constant-divisor query still decides.
#[test]
fn constant_divisor_still_decides() {
    // (div x 3) = 2 ∧ (mod x 3) = 1  ⇒  x = 7. Sat.
    let mut a = TermArena::new();
    let x = ivar(&mut a, "x");
    let three = a.int_const(3);
    let two = a.int_const(2);
    let one = a.int_const(1);
    let dx = a.int_div(x, three).unwrap();
    let mx = a.int_mod(x, three).unwrap();
    let a1 = a.eq(dx, two).unwrap();
    let a2 = a.eq(mx, one).unwrap();
    let assertions = [a1, a2];
    let r = check_auto(&mut a, &assertions, &cfg()).unwrap();
    match r {
        CheckResult::Sat(model) => {
            let asg = model.to_assignment();
            for &asrt in &assertions {
                assert_eq!(eval(&a, asrt, &asg).unwrap(), Value::Bool(true));
            }
        }
        other => panic!("constant-divisor query should be sat, got {other:?}"),
    }
    // Silence unused-import lint for Op in some feature configs.
    let _ = Op::IntDiv;
}
