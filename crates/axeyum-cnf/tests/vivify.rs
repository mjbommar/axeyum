//! Integration tests for the public `vivify` inprocessing API.
//!
//! These exercise the crate's public surface (the `pub use` re-exports from
//! `lib.rs`) end-to-end: the load-bearing **DRAT self-verification** and
//! **equisatisfiability differential with model replay** over many deterministic
//! random CNFs (no `rand`, no clock), plus the documented strengthening rules.
//! The in-crate `#[cfg(test)]` module covers the same contracts white-box; this
//! file additionally confirms the API is wired and usable from outside the crate.

use std::collections::BTreeSet;

use axeyum_cnf::{
    CnfClause, CnfFormula, CnfLit, CnfVar, ProofSolveOutcome, VivifyOptions, check_drat,
    solve_with_drat_proof, vivify, vivify_within,
};

fn pos(v: usize) -> CnfLit {
    CnfLit::positive(CnfVar::new(v).unwrap())
}
fn neg(v: usize) -> CnfLit {
    pos(v).negated()
}
fn clause(lits: &[CnfLit]) -> CnfClause {
    CnfClause::new(lits.to_vec())
}
fn formula(nvars: usize, clauses: &[&[CnfLit]]) -> CnfFormula {
    let mut f = CnfFormula::new(nvars);
    for c in clauses {
        f.add_clause(clause(c)).unwrap();
    }
    f
}
fn lit_set(lits: &[CnfLit]) -> BTreeSet<(usize, bool)> {
    lits.iter()
        .map(|l| (l.var().index(), l.is_negated()))
        .collect()
}

/// Brute-force model equivalence over `nvars` variables.
fn equivalent(a: &CnfFormula, b: &CnfFormula, nvars: usize) {
    for mask in 0u32..(1u32 << nvars) {
        let asg: Vec<bool> = (0..nvars).map(|i| (mask >> i) & 1 == 1).collect();
        assert_eq!(
            a.evaluate(&asg).unwrap(),
            b.evaluate(&asg).unwrap(),
            "disagree on {asg:?}"
        );
    }
}

/// Deterministic LCG (reproducible; no `rand`/clock).
fn lcg(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    // The raw state is never handed out: bit `k` of an LCG modulo 2^64
    // has period 2^(k+1), so `state & 1` alternates on every draw and a
    // decision made at a fixed draw offset is a constant, not a coin.
    // Measured 2026-09-16 (lane ax-proptest, bench-results/proptest-box-
    // audit-20260916): a literal costs two draws (var, sign), so every
    // sign in one clause agreed and 0 of 500 formulas had a mixed clause.
    // SplitMix64's finalizer makes every output bit depend on the state.
    let z = (*state ^ (*state >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    let z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}
fn below(state: &mut u64, bound: usize) -> usize {
    usize::try_from(lcg(state) >> 33).unwrap_or(0) % bound
}
fn random_formula(state: &mut u64, nvars: usize) -> CnfFormula {
    let nclauses = 1 + below(state, 14);
    let mut f = CnfFormula::new(nvars);
    for _ in 0..nclauses {
        let width = 1 + below(state, 4);
        let mut lits = Vec::new();
        for _ in 0..width {
            let var = below(state, nvars);
            lits.push(if lcg(state) & 1 == 0 {
                pos(var)
            } else {
                neg(var)
            });
        }
        f.add_clause(clause(&lits)).unwrap();
    }
    f
}

#[test]
fn public_api_strengthens_via_implied_literal() {
    // (a∨b∨c) with helper (a∨b): assuming a false forces b true, so the clause is
    // strengthened to (a∨b). The public re-exports must compose end-to-end.
    let f = formula(3, &[&[pos(0), pos(1), pos(2)], &[pos(0), pos(1)]]);
    let out = vivify(&f, VivifyOptions::default());
    assert!(
        out.formula
            .clauses()
            .iter()
            .any(|c| lit_set(c.lits()) == lit_set(&[pos(0), pos(1)])),
        "expected (a∨b)"
    );
    assert!(out.stats.literals_removed >= 1);
    equivalent(&f, &out.formula, 3);
    assert!(check_drat(&f, &out.proof).is_ok());
}

#[test]
fn within_deadline_variant_is_usable_and_sound() {
    // The `_within` entry with no deadline behaves like `vivify`.
    let f = formula(3, &[&[pos(0), pos(1), pos(2)], &[pos(0), pos(1)]]);
    let out = vivify_within(&f, VivifyOptions::default(), None);
    equivalent(&f, &out.formula, 3);
    assert!(check_drat(&f, &out.proof).is_ok());
}

#[test]
fn drat_self_verifies_over_many_random_cnfs() {
    const NVARS: usize = 5;
    let mut state = 0x5EED_1234_DEAD_C0DEu64;
    let mut n = 0usize;
    for _ in 0..500 {
        let f = random_formula(&mut state, NVARS);
        let out = vivify(&f, VivifyOptions::default());
        // Every emitted step must verify against the ORIGINAL (no rejected step).
        assert!(
            check_drat(&f, &out.proof).is_ok(),
            "emitted proof must self-verify"
        );
        assert!(out.formula.clauses().len() <= f.clauses().len());
        n += 1;
    }
    assert_eq!(n, 500);
}

#[test]
fn equisatisfiability_differential_with_model_replay() {
    const NVARS: usize = 5;
    let mut state = 0xFACE_FEED_0BAD_BEEFu64;
    let (mut sat_n, mut unsat_n, mut strengthen_n, mut disagree) = (0usize, 0usize, 0usize, 0usize);
    for _ in 0..500 {
        let f = random_formula(&mut state, NVARS);
        let out = vivify(&f, VivifyOptions::default());
        if !out.stats.is_empty() {
            strengthen_n += 1;
        }
        assert!(check_drat(&f, &out.proof).is_ok());

        match (
            solve_with_drat_proof(&f),
            solve_with_drat_proof(&out.formula),
        ) {
            (ProofSolveOutcome::Sat(_), ProofSolveOutcome::Sat(model)) => {
                sat_n += 1;
                // Model preservation: a vivified model satisfies the ORIGINAL.
                assert!(
                    f.evaluate(model.values()).unwrap(),
                    "vivified model must satisfy the original"
                );
            }
            (ProofSolveOutcome::Unsat(_), ProofSolveOutcome::Unsat(p)) => {
                unsat_n += 1;
                assert_eq!(check_drat(&out.formula, &p), Ok(true));
            }
            (ProofSolveOutcome::Sat(_), ProofSolveOutcome::Unsat(_))
            | (ProofSolveOutcome::Unsat(_), ProofSolveOutcome::Sat(_)) => disagree += 1,
            _ => {}
        }
    }
    assert_eq!(disagree, 0, "vivification changed satisfiability");
    assert!(sat_n > 0, "no SAT coverage");
    assert!(unsat_n > 0, "no UNSAT coverage");
    assert!(strengthen_n > 0, "no strengthening coverage");
}

/// Coverage guard for the two random sweeps above (same seeds, same counts,
/// same `random_formula`; no vivification is run).
///
/// Class: a clause containing both a positive and a negative literal (an
/// implication such as `(¬a ∨ b)`, the shape a vivification assumption
/// propagates THROUGH). With the raw-state LCG the sign draw inside one clause
/// always landed on the same parity, so every clause was all-positive or
/// all-negative: measured 2026-09-16, 0 of 500 formulas per seed contained a
/// mixed-polarity clause (lane ax-proptest,
/// `bench-results/proptest-box-audit-20260916`).
#[test]
fn the_generator_reaches_mixed_polarity_clauses() {
    const NVARS: usize = 5;
    let seeds = [0x5EED_1234_DEAD_C0DEu64, 0xFACE_FEED_0BAD_BEEFu64];
    for seed in seeds {
        let mut state = seed;
        let mut mixed_formulas = 0usize;
        let mut mixed_clauses = 0usize;
        let mut total_clauses = 0usize;
        for _ in 0..500 {
            let f = random_formula(&mut state, NVARS);
            let mut any = false;
            for c in f.clauses() {
                total_clauses += 1;
                let has_pos = c.lits().iter().any(|l| !l.is_negated());
                let has_neg = c.lits().iter().any(|l| l.is_negated());
                if has_pos && has_neg {
                    mixed_clauses += 1;
                    any = true;
                }
            }
            if any {
                mixed_formulas += 1;
            }
        }
        eprintln!(
            "seed {seed:#x}: mixed-polarity clauses {mixed_clauses}/{total_clauses}, \
             formulas with one {mixed_formulas}/500"
        );
        assert!(
            mixed_formulas >= 250,
            "seed {seed:#x}: only {mixed_formulas}/500 formulas contain a \
             mixed-polarity clause (old generator: 0)"
        );
        assert!(
            mixed_clauses >= 800,
            "seed {seed:#x}: only {mixed_clauses}/{total_clauses} clauses mix \
             polarities (old generator: 0)"
        );
    }
}
