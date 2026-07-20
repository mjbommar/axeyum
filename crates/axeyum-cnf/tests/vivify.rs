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
    *state
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
            .any(|c| lit_set(c) == lit_set(&[pos(0), pos(1)])),
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
