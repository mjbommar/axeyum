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
