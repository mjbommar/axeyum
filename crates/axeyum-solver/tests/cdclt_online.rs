//! Parity + differential gates for the generic online CDCL(T) driver wired to
//! EUF (Track 1, P1.5 slice a): [`check_qf_uf_online_cdclt`].
//!
//! The new driver must decide the `QF_UF` fragment *identically* to the established
//! offline route [`check_qf_uf`] (itself differentially validated against the
//! Ackermann bit-blast, see `euf_egraph_diff.rs`). Two gates:
//!
//! 1. **Named shapes** — the exact congruence/transitivity/disjunction/model-build
//!    cases the offline path is tested on, plus the `unsat` debug-recheck: every
//!    online `unsat` is confirmed `unsat` by the offline route on the same query
//!    (this slice adds no new unsat trust surface).
//! 2. **House-LCG differential fuzz** (no Z3 needed) — ≥2000 random EUF
//!    conjunction/Boolean-structure instances, online driver vs offline route.
//!    Identical verdicts required; a `Sat`/`Unsat` split is a soundness bug and
//!    panics. One route deciding while the other is `Unknown` is allowed (counted).
//!
//! The Z3-gated `QF_UF` differential (`qf_uf_differential_fuzz.rs`) is run unchanged
//! as a separate gate; it exercises the dispatched pure-Rust stack against Z3.

use axeyum_ir::{FuncId, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, check_qf_uf, check_qf_uf_online_cdclt};

fn online(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    check_qf_uf_online_cdclt(arena, assertions, &SolverConfig::default())
}

/// A named shape: online CDCL(T) and offline `check_qf_uf` must return the same
/// verdict. When either is `unsat`, both must be `unsat` (the debug-recheck).
fn assert_same_verdict(arena: &mut TermArena, assertions: &[TermId]) {
    let on = online(arena, assertions);
    let off = check_qf_uf(arena, assertions);
    match (&on, &off) {
        (CheckResult::Unsat, CheckResult::Unsat) | (CheckResult::Sat(_), CheckResult::Sat(_)) => {}
        // A hard disagreement in either direction is a bug.
        (CheckResult::Unsat, CheckResult::Sat(_)) | (CheckResult::Sat(_), CheckResult::Unsat) => {
            panic!("online CDCL(T) {on:?} disagrees with offline check_qf_uf {off:?}");
        }
        // For these pure-EUF shapes both routes decide, so anything else is also a
        // regression we want to catch.
        _ => {
            panic!("online CDCL(T) {on:?} vs offline {off:?}: expected both to decide identically")
        }
    }
}

#[test]
fn congruence_conflict_parity() {
    // a = b ∧ f(a) ≠ f(b) — UNSAT by congruence.
    let mut arena = TermArena::new();
    let sort = Sort::BitVec(8);
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let f = arena.declare_fun("f", &[sort], sort).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let ab = arena.eq(a, b).unwrap();
    let fa_eq_fb = arena.eq(fa, fb).unwrap();
    let fa_ne_fb = arena.not(fa_eq_fb).unwrap();
    assert_eq!(online(&mut arena, &[ab, fa_ne_fb]), CheckResult::Unsat);
    assert_same_verdict(&mut arena, &[ab, fa_ne_fb]);
}

#[test]
fn transitivity_parity() {
    // a=b ∧ b=c ∧ a≠c — UNSAT.
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let c = arena.bv_var("c", 8).unwrap();
    let ab = arena.eq(a, b).unwrap();
    let bc = arena.eq(b, c).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let a_ne_c = arena.not(ac).unwrap();
    assert_eq!(online(&mut arena, &[ab, bc, a_ne_c]), CheckResult::Unsat);
    assert_same_verdict(&mut arena, &[ab, bc, a_ne_c]);
}

#[test]
fn disjunctive_refutation_parity() {
    // (a=b ∨ a=c) ∧ a≠b ∧ a≠c — needs the Boolean search; UNSAT.
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let c = arena.bv_var("c", 8).unwrap();
    let ab = arena.eq(a, b).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let disj = arena.or(ab, ac).unwrap();
    let a_ne_b = arena.not(ab).unwrap();
    let a_ne_c = arena.not(ac).unwrap();
    assert_eq!(
        online(&mut arena, &[disj, a_ne_b, a_ne_c]),
        CheckResult::Unsat
    );
    assert_same_verdict(&mut arena, &[disj, a_ne_b, a_ne_c]);
}

#[test]
fn two_argument_congruence_parity() {
    // x=y ∧ g(x,z) ≠ g(y,z) — UNSAT by two-argument congruence.
    let mut arena = TermArena::new();
    let sort = Sort::BitVec(8);
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let z = arena.bv_var("z", 8).unwrap();
    let g = arena.declare_fun("g", &[sort, sort], sort).unwrap();
    let gxz = arena.apply(g, &[x, z]).unwrap();
    let gyz = arena.apply(g, &[y, z]).unwrap();
    let xy = arena.eq(x, y).unwrap();
    let g_eq = arena.eq(gxz, gyz).unwrap();
    let g_ne = arena.not(g_eq).unwrap();
    assert_eq!(online(&mut arena, &[xy, g_ne]), CheckResult::Unsat);
    assert_same_verdict(&mut arena, &[xy, g_ne]);
}

#[test]
fn satisfiable_congruence_parity() {
    // a = b ∧ f(a) = f(b) — SAT (model must be built + replayed).
    let mut arena = TermArena::new();
    let sort = Sort::BitVec(8);
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let f = arena.declare_fun("f", &[sort], sort).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let ab = arena.eq(a, b).unwrap();
    let fa_eq_fb = arena.eq(fa, fb).unwrap();
    assert!(matches!(
        online(&mut arena, &[ab, fa_eq_fb]),
        CheckResult::Sat(_)
    ));
    assert_same_verdict(&mut arena, &[ab, fa_eq_fb]);
}

#[test]
fn satisfiable_disjunction_parity() {
    // a=b ∨ a=c — SAT.
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let c = arena.bv_var("c", 8).unwrap();
    let ab = arena.eq(a, b).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let disj = arena.or(ab, ac).unwrap();
    assert!(matches!(online(&mut arena, &[disj]), CheckResult::Sat(_)));
    assert_same_verdict(&mut arena, &[disj]);
}

// ---------------------------------------------------------------------------
// House-LCG differential fuzz: online CDCL(T) vs offline check_qf_uf.
// ---------------------------------------------------------------------------

/// Deterministic xorshift PRNG (no clock).
fn xorshift(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

fn pick(state: &mut u64, n: usize) -> usize {
    usize::try_from(xorshift(state)).unwrap_or(0) % n
}

/// Builds a random pure-equality/UF formula (BitVec(4) carrier, unary `f` + binary
/// `g`, no arithmetic operators) as a conjunction of random ≤2-literal clauses.
fn random_instance(state: &mut u64, arena: &mut TermArena, f: FuncId, g: FuncId) -> Vec<TermId> {
    let n_vars = 2 + pick(state, 3);
    let vars: Vec<TermId> = (0..n_vars)
        .map(|i| arena.bv_var(&format!("v{i}"), 4).unwrap())
        .collect();

    let mut terms = vars.clone();
    for _ in 0..3 {
        let t = if xorshift(state) & 1 == 0 {
            let a = terms[pick(state, terms.len())];
            arena.apply(f, &[a]).unwrap()
        } else {
            let a = terms[pick(state, terms.len())];
            let b = terms[pick(state, terms.len())];
            arena.apply(g, &[a, b]).unwrap()
        };
        terms.push(t);
    }

    let mut assertions = Vec::new();
    let n_clauses = 2 + pick(state, 4);
    for _ in 0..n_clauses {
        let width = 1 + pick(state, 2);
        let mut clause: Option<TermId> = None;
        for _ in 0..width {
            let s = terms[pick(state, terms.len())];
            let t = terms[pick(state, terms.len())];
            let eq = arena.eq(s, t).unwrap();
            let lit = if xorshift(state) & 1 == 0 {
                eq
            } else {
                arena.not(eq).unwrap()
            };
            clause = Some(match clause {
                None => lit,
                Some(acc) => arena.or(acc, lit).unwrap(),
            });
        }
        assertions.push(clause.unwrap());
    }
    assertions
}

#[test]
fn online_cdclt_vs_offline_differential_fuzz() {
    const INSTANCES: usize = 2500;
    let mut state = 0x0F1E_2D3C_4B5A_6978u64;
    let mut agree = 0usize;
    let mut online_unknown = 0usize;
    let mut offline_unknown = 0usize;
    let mut unsat_agree = 0usize;
    let mut sat_agree = 0usize;

    for i in 0..INSTANCES {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(4);
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort, sort], sort).unwrap();
        let assertions = random_instance(&mut state, &mut arena, f, g);

        // Run the online driver first (it adds no fresh symbols), then the offline
        // route (which declares `!euf_atom_*` helpers) on the same arena.
        let on = online(&mut arena, &assertions);
        let off = check_qf_uf(&mut arena, &assertions);

        match (&on, &off) {
            (CheckResult::Unsat, CheckResult::Sat(_))
            | (CheckResult::Sat(_), CheckResult::Unsat) => {
                panic!(
                    "DISAGREEMENT (instance {i}): online CDCL(T) = {on:?}, offline check_qf_uf = {off:?}"
                );
            }
            (CheckResult::Unsat, CheckResult::Unsat) => {
                agree += 1;
                unsat_agree += 1;
            }
            (CheckResult::Sat(_), CheckResult::Sat(_)) => {
                agree += 1;
                sat_agree += 1;
            }
            (CheckResult::Unknown(_), _) => online_unknown += 1,
            (_, CheckResult::Unknown(_)) => offline_unknown += 1,
        }
    }

    println!(
        "online-cdclt vs offline: {INSTANCES} instances | {agree} agree ({unsat_agree} unsat, {sat_agree} sat) | {online_unknown} online-unknown | {offline_unknown} offline-unknown | 0 DISAGREE"
    );
    // Both routes decide the pure-EUF fragment completely, so agreement dominates.
    assert!(
        agree >= INSTANCES / 2,
        "expected >= {} agreements, got {agree} (online-unknown {online_unknown}, offline-unknown {offline_unknown})",
        INSTANCES / 2
    );
    // The fuzz must exercise both verdicts to be meaningful.
    assert!(unsat_agree > 0, "fuzz produced no agreed UNSAT instances");
    assert!(sat_agree > 0, "fuzz produced no agreed SAT instances");
}

#[test]
fn deadline_gives_unknown_not_wrong_answer() {
    // A tiny UNSAT instance with a zero-duration deadline: the driver must degrade
    // to Unknown under the resource bound rather than return a verdict.
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let c = arena.bv_var("c", 8).unwrap();
    let ab = arena.eq(a, b).unwrap();
    let bc = arena.eq(b, c).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let a_ne_c = arena.not(ac).unwrap();
    let cfg = SolverConfig::default().with_timeout(std::time::Duration::ZERO);
    let r = check_qf_uf_online_cdclt(&mut arena, &[ab, bc, a_ne_c], &cfg);
    assert!(
        matches!(r, CheckResult::Unknown(_)),
        "zero-timeout must yield Unknown, got {r:?}"
    );
}
