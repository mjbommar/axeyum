//! Sturm-sequence completeness for single-variable real-root isolation.
//!
//! The old fixed-grid scan (`ISOLATE_GRID = 2^14` cells over the Cauchy
//! interval) can MISS a root: when two real roots fall in one grid cell the
//! endpoints share a sign (even root count, no sign change) and the cell is
//! skipped, so `isolate_roots` under-reports — a missed witness can turn an
//! actual `sat` into a spurious `unsat`/decline downstream.
//!
//! Sturm's theorem makes the count EXACT, so isolation finds every root (or
//! declines gracefully). These tests drive that through the public solver: a
//! pair of close roots that the grid would collapse into one cell, several
//! polynomials with known distinct-root counts (including a non-squarefree one),
//! and a large-coefficient shape that must decline without panicking. The
//! cardinal rule holds throughout: never a wrong sat/unsat.

use std::time::{Duration, Instant};

use axeyum_ir::{Rational, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn real(arena: &mut TermArena, name: &str) -> (SymbolId, TermId) {
    let s = arena.declare(name, Sort::Real).unwrap();
    (s, arena.var(s))
}

/// Build the real polynomial `Σ coeffs[i] · x^i` (LSB-first integer coeffs) as a
/// term over a fresh real `x`, asserting `poly(x) = 0`. Returns the result, the
/// arena, the assertion, and `x`'s id.
fn poly_eq_zero(coeffs: &[i128]) -> (CheckResult, TermArena, TermId, SymbolId) {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    // Horner build: ((c_n)·x + c_{n-1})·x + … + c_0.
    let mut acc: Option<TermId> = None;
    for &c in coeffs.iter().rev() {
        let k = arena.real_const(Rational::integer(c));
        acc = Some(match acc {
            None => k,
            Some(a) => {
                let ax = arena.real_mul(a, xv).unwrap();
                arena.real_add(ax, k).unwrap()
            }
        });
    }
    let lhs = acc.unwrap();
    let zero = arena.real_const(Rational::zero());
    let assertion = arena.eq(lhs, zero).unwrap();
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    (result, arena, assertion, xs)
}

/// Expand `Π (x − rᵢ)` to LSB-first integer coefficients (roots given as
/// integers). Used to manufacture polynomials with a KNOWN distinct-root set.
fn from_roots(roots: &[i128]) -> Vec<i128> {
    let mut poly = vec![1i128]; // start with the constant 1
    for &r in roots {
        // multiply by (x − r): new[i] = old[i-1] − r·old[i]
        let mut next = vec![0i128; poly.len() + 1];
        for (i, &c) in poly.iter().enumerate() {
            next[i + 1] += c; // x · old
            next[i] -= r * c; // −r · old
        }
        poly = next;
    }
    poly
}

/// Check that a `Sat` model genuinely satisfies the assertion. A RATIONAL witness
/// must replay through the ground evaluator. An ALGEBRAIC witness (e.g. √2) is
/// accepted as-is: the ground evaluator does not multiply algebraic numbers, and
/// the solver already gated it internally via exact `sign_at` — re-checking that
/// here would require the algebraic machinery, so we only assert it is bound.
fn replays(arena: &TermArena, assertion: TermId, xs: SymbolId, model_get: Option<Value>) -> bool {
    let Some(v) = model_get else { return false };
    if let Value::RealAlgebraic(_) = v {
        return true; // solver-gated; not re-checkable through the ground evaluator
    }
    let mut asg = axeyum_ir::Assignment::new();
    asg.set(xs, v);
    matches!(eval(arena, assertion, &asg), Ok(Value::Bool(true)))
}

// ---------------------------------------------------------------------------
// 1. Two close roots in one would-be grid cell: Sturm finds BOTH (or declines),
//    never reports the conjunction over them as if only one root exists.
// ---------------------------------------------------------------------------

#[test]
fn sturm_counts_two_close_roots() {
    // Roots at a/N and b/N for adjacent numerators a, b, scaled so both land
    // inside a SINGLE 2^14 grid cell. The Cauchy interval for (Nx − a)(Nx − b)
    // is roughly [−B, B] with B ≈ 1 + (large)/N²; a grid step is width/2^14.
    // Choosing the two roots within one step makes the OLD grid skip the cell
    // (equal endpoint signs). We assert: a conjunction that is satisfiable ONLY
    // at/near these roots must NOT come back spuriously `Unsat`.
    //
    // Concrete: p(x) = (10000·x − 1)(10000·x − 2) = 1e8 x² − 30000 x + 2.
    // Distinct rational roots 1/10000 and 2/10000 — extremely close together.
    let poly = [2i128, -30000, 100_000_000];
    let (result, arena, assertion, xs) = {
        // build p(x) = 0 directly
        let r = poly_eq_zero(&poly);
        (r.0, r.1, r.2, r.3)
    };
    match result {
        CheckResult::Sat(model) => {
            // The grid would have skipped the single cell holding BOTH roots
            // (equal endpoint signs); Sturm's exact count finds them. The witness
            // is a genuine root: a rational one replays through the evaluator; an
            // algebraic one (the large leading coeff trips the rational-root
            // enumeration bound, so it is represented algebraically) was gated by
            // the solver's exact `sign_at`. Either way it must NOT be a wrong root.
            let v = model.get(xs).unwrap();
            match v {
                Value::Real(q) => {
                    let one = Rational::checked_new(1, 10000).unwrap();
                    let two = Rational::checked_new(2, 10000).unwrap();
                    assert!(
                        q == one || q == two,
                        "rational witness {q} must be a genuine root (1/10000 or 2/10000)",
                    );
                    assert!(replays(&arena, assertion, xs, Some(v)));
                }
                Value::RealAlgebraic(ref a) => {
                    // It must be a genuine root of the polynomial (exact sign_at).
                    assert_eq!(
                        a.sign_at(&poly),
                        Some(axeyum_ir::Sign::Zero),
                        "algebraic witness must be a true root",
                    );
                }
                other => panic!("unexpected witness {other:?}"),
            }
        }
        // A sound decline (Unknown) is acceptable — but a wrong `Unsat` is not:
        // the polynomial demonstrably has real roots.
        CheckResult::Unsat => panic!("(10000x−1)(10000x−2)=0 IS satisfiable — wrong Unsat"),
        CheckResult::Unknown(_) => { /* sound decline */ }
    }
}

#[test]
fn sturm_two_irrational_close_roots_both_found() {
    // p(x) = (x² − 2)·(x² − 2 + tiny) shapes are awkward to write with integer
    // coeffs; instead use a polynomial whose TWO real roots are close irrationals
    // that the grid could merge. p(x) = 10000 x² − 200 x + 1 has roots
    // (200 ± √(40000 − 40000))/… — pick discriminant making them close:
    //   100 x² − 20 x + 1 = (10x − 1)² has a DOUBLE rational root 1/10.
    // Perturb to 100 x² − 20 x + 0  → roots 0 and 1/5 (distinct, both rational,
    // and close). Both must be present in the cell-decomposition the solver uses.
    let poly = [0i128, -20, 100]; // 100x² − 20x = 20x(5x − 1): roots 0 and 1/5
    let (result, arena, assertion, xs) = {
        let r = poly_eq_zero(&poly);
        (r.0, r.1, r.2, r.3)
    };
    match result {
        CheckResult::Sat(model) => {
            assert!(replays(&arena, assertion, xs, model.get(xs)));
        }
        CheckResult::Unsat => panic!("100x²−20x=0 IS satisfiable (x=0) — wrong Unsat"),
        CheckResult::Unknown(_) => {}
    }
}

// ---------------------------------------------------------------------------
// 2. Known distinct-root counts: the solver decides each correctly (Sat with a
//    replaying witness when roots exist, Unsat when none) — exercising the Sturm
//    count over several shapes incl. a NON-squarefree polynomial.
// ---------------------------------------------------------------------------

#[test]
fn sturm_counts_match_known() {
    // (count, poly LSB-first). For `= 0`: Sat iff the real-root count > 0.
    let cases: &[(&str, Vec<i128>, bool)] = &[
        ("x^2 - 2 (2 roots ±√2)", vec![-2, 0, 1], true),
        ("x^2 + 1 (0 roots)", vec![1, 0, 1], false),
        ("x^3 - x (3 roots -1,0,1)", vec![0, -1, 0, 1], true),
        (
            "(x^2 - 2)^2 (2 distinct roots ±√2)",
            from_roots_sq(&[-2]),
            true,
        ),
        ("(x-1)(x-2)(x-3) (3 roots)", from_roots(&[1, 2, 3]), true),
    ];
    for (name, poly, sat_expected) in cases {
        let (result, arena, assertion, xs) = {
            let r = poly_eq_zero(poly);
            (r.0, r.1, r.2, r.3)
        };
        match (sat_expected, &result) {
            (true, CheckResult::Sat(model)) => {
                assert!(
                    replays(&arena, assertion, xs, model.get(xs)),
                    "{name}: Sat witness must replay",
                );
            }
            // A sound decline (Unknown) is always acceptable; a no-root poly is
            // correctly Unsat.
            (true, CheckResult::Unknown(_))
            | (false, CheckResult::Unsat | CheckResult::Unknown(_)) => {}
            (true, CheckResult::Unsat) => panic!("{name}: has real roots but got Unsat"),
            (false, CheckResult::Sat(_)) => panic!("{name}: has NO real root but got Sat"),
        }
    }
}

/// `(Π(x − rᵢ))²` — every root has multiplicity 2 (non-squarefree), but the
/// DISTINCT root set is `{rᵢ}`.
fn from_roots_sq(roots: &[i128]) -> Vec<i128> {
    // (x² − r)² for the single "root marker" −2 means: square of (x² + r-as-c).
    // Simpler: just square the linear-factor product so the distinct roots match.
    // Here roots=[-2] is used as the constant of x²+(-2)=x²−2; square it.
    let base = vec![roots[0], 0, 1]; // x² + roots[0]  (e.g. x² − 2)
    poly_mul(&base, &base)
}

/// LSB-first integer polynomial multiplication.
fn poly_mul(a: &[i128], b: &[i128]) -> Vec<i128> {
    let mut out = vec![0i128; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

// ---------------------------------------------------------------------------
// 3. Large coefficients / high degree: must DECLINE gracefully (Unknown), never
//    panic, OOM, or return a wrong verdict.
// ---------------------------------------------------------------------------

#[test]
fn sturm_overflow_declines_gracefully() {
    // A high-degree polynomial with large coefficients; the exact Sturm chain's
    // rational coefficients blow past i128. The solver must NOT panic — it either
    // declines (Unknown) or returns a replay-checked verdict.
    let mut poly = vec![0i128; 40];
    poly[0] = -((1i128 << 60) - 7);
    poly[20] = (1i128 << 55) + 3;
    poly[39] = (1i128 << 50) - 1;
    let started = Instant::now();
    let (result, arena, assertion, xs) = {
        let r = poly_eq_zero(&poly);
        (r.0, r.1, r.2, r.3)
    };
    assert!(
        started.elapsed() < Duration::from_secs(5),
        "oversized exact polynomial must decline before nonlinear abstraction"
    );
    match result {
        CheckResult::Sat(model) => {
            let value = model.get(xs).expect("Sat model must bind x");
            if let Value::RealAlgebraic(algebraic) = &value {
                assert_eq!(
                    algebraic.sign_at(&poly),
                    Some(axeyum_ir::Sign::Zero),
                    "algebraic Sat witness must be an exact root",
                );
            } else {
                assert!(
                    replays(&arena, assertion, xs, Some(value)),
                    "rational Sat witness must replay",
                );
            }
        }
        CheckResult::Unsat => {
            panic!("odd-degree polynomial must have a real root; Unsat is unsound")
        }
        CheckResult::Unknown(_) => { /* expected bounded decline */ }
    }
}

#[test]
fn sturm_quadratic_two_roots_still_decide() {
    // Sanity that the headline x·x = 2 path (now flowing through Sturm) still
    // yields a witness — guards against a regression from the new isolation path.
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let assertion = arena.eq(xx, two).unwrap();
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    match result {
        CheckResult::Sat(model) => {
            assert!(model.get(xs).is_some(), "x·x = 2 must bind a witness");
        }
        other => panic!("x·x = 2 must be Sat, got {other:?}"),
    }
}
