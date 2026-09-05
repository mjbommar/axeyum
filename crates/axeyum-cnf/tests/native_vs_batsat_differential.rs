//! Native CDCL core vs. the retired `rustsat-batsat` adapter, on identical CNF
//! (ADR-1703).
//!
//! # THIS FILE COMPILES TO ZERO TESTS WITHOUT `--features batsat-reference`
//!
//! The whole file is `#![cfg(feature = "batsat-reference")]`. Without the
//! feature `cargo test` prints `running 0 tests ... ok` and **exits 0** — a
//! green-looking gate that checked nothing. This is the same trap as
//! `--features z3` on the LRA differential fuzzes, which sat inert in a
//! pre-push hook for fifteen days. Run it as:
//!
//! ```sh
//! scripts/cargo-serialized.sh test -p axeyum-cnf --features batsat-reference \
//!     --test native_vs_batsat_differential
//! ```
//!
//! and **confirm a nonzero test count** before believing the pass.
//!
//! # What it checks, and why this shape
//!
//! ADR-1703 promotes the native core to the SAT engine on every path and keeps
//! BatSat only as an independent referee — the role ADR-0002 gives Z3. This is
//! that referee, exercised on:
//!
//! 1. every committed `corpus/micro-cnf/*.cnf`, the small fixed population the
//!    crate already ships; and
//! 2. a seeded random 3-SAT family at the satisfiability threshold ratio
//!    (`m/n ≈ 4.26`), where roughly half of the instances are satisfiable and
//!    neither verdict is the easy default — a family at ratio 2 would be
//!    satisfiable almost surely and a disagreement could hide in it.
//!
//! The assertions: the two engines must agree on `sat`/`unsat`, and every
//! `sat` model must actually satisfy the formula it came from. A model check is
//! not redundant with agreement — two engines agreeing on `sat` says nothing
//! about whether either model is a model.
//!
//! `unknown` from either side is not a disagreement (both carry budgets), so
//! those instances are skipped and **counted**; the test fails if the whole
//! population ended up skipped, which is the only way this file could pass
//! while comparing nothing.

#![cfg(feature = "batsat-reference")]

use std::path::{Path, PathBuf};

use axeyum_cnf::{
    CnfClause, CnfFormula, CnfLit, CnfVar, SatResult, parse_dimacs, solve_with_native_core,
    solve_with_rustsat_batsat,
};

/// A deterministic 64-bit LCG. Explicit and seeded, per the workspace
/// determinism promise; nothing here may depend on a system RNG.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() >> 11).expect("63-bit value fits usize") % bound
    }

    fn bool(&mut self) -> bool {
        self.next() >> 63 == 1
    }
}

fn verdict(result: &SatResult) -> &'static str {
    match result {
        SatResult::Sat(_) => "sat",
        SatResult::Unsat(_) => "unsat",
        SatResult::Unknown(_) => "unknown",
    }
}

/// Compares the two engines on `formula`. Returns `true` when a comparison
/// actually happened (neither side answered `unknown`).
fn compare(label: &str, formula: &CnfFormula) -> bool {
    let native = solve_with_native_core(formula).expect("native core must not error");
    let batsat = solve_with_rustsat_batsat(formula).expect("batsat adapter must not error");

    if let SatResult::Sat(model) = &native {
        assert!(
            model.satisfies(formula).expect("model fits the formula"),
            "{label}: the native core returned a model that does not satisfy the formula"
        );
    }
    if let SatResult::Sat(model) = &batsat {
        assert!(
            model.satisfies(formula).expect("model fits the formula"),
            "{label}: batsat returned a model that does not satisfy the formula"
        );
    }

    match (&native, &batsat) {
        (SatResult::Unknown(_), _) | (_, SatResult::Unknown(_)) => false,
        _ => {
            assert_eq!(
                verdict(&native),
                verdict(&batsat),
                "{label}: VERDICT DISAGREEMENT native={} batsat={} -- this is a P0 soundness \
                 finding, not a flake; record the file before doing anything else",
                verdict(&native),
                verdict(&batsat)
            );
            true
        }
    }
}

fn micro_cnf_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/micro-cnf")
}

#[test]
fn the_committed_micro_cnf_corpus_agrees() {
    let dir = micro_cnf_dir();
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|error| panic!("read {}: {error}", dir.display()))
        .map(|entry| entry.expect("dir entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .collect();
    paths.sort();

    assert!(
        !paths.is_empty(),
        "corpus/micro-cnf/ has no .cnf files: this test would have passed while \
         comparing nothing"
    );

    let mut compared = 0usize;
    for path in &paths {
        let text = std::fs::read_to_string(path).expect("read CNF");
        let formula = parse_dimacs(&text).expect("parse CNF");
        let label = path.file_name().expect("file name").to_string_lossy();
        if compare(&label, &formula) {
            compared += 1;
        }
    }
    assert!(
        compared > 0,
        "every one of the {} micro-CNF instances came back unknown from one side; \
         nothing was compared",
        paths.len()
    );
}

/// Random 3-SAT at the threshold ratio: `m = round(4.26 * n)` clauses of three
/// distinct variables with random signs.
fn random_3sat(rng: &mut Lcg, variables: usize) -> CnfFormula {
    let clauses = (variables as f64 * 4.26).round() as usize;
    let mut formula = CnfFormula::new(variables);
    for _ in 0..clauses {
        let mut vars: Vec<usize> = Vec::with_capacity(3);
        while vars.len() < 3 {
            let candidate = rng.below(variables);
            if !vars.contains(&candidate) {
                vars.push(candidate);
            }
        }
        let lits: Vec<CnfLit> = vars
            .into_iter()
            .map(|index| {
                let lit = CnfLit::positive(CnfVar::new(index).expect("variable in range"));
                if rng.bool() { lit.negated() } else { lit }
            })
            .collect();
        formula
            .add_clause(CnfClause::new(lits))
            .expect("clause fits the formula");
    }
    formula
}

#[test]
fn seeded_random_3sat_at_the_threshold_ratio_agrees() {
    let mut rng = Lcg(0x5eed_1703_5a71_c0de);
    let mut compared = 0usize;
    let mut sat = 0usize;
    let mut unsat = 0usize;
    for case in 0..120 {
        // 20..=39 variables: small enough that both engines decide every
        // instance well inside their budgets, large enough that the threshold
        // ratio actually produces a mix of verdicts.
        let variables = 20 + (case % 20);
        let formula = random_3sat(&mut rng, variables);
        let label = format!("random-3sat case {case} (n={variables})");
        if compare(&label, &formula) {
            compared += 1;
            match solve_with_native_core(&formula).expect("native core") {
                SatResult::Sat(_) => sat += 1,
                SatResult::Unsat(_) => unsat += 1,
                SatResult::Unknown(_) => unreachable!("compare() returned true"),
            }
        }
    }
    assert_eq!(compared, 120, "every threshold instance must be decided");
    // A family that produced only one verdict would be a much weaker referee
    // than it looks: agreement on "everything is satisfiable" is cheap. At the
    // threshold ratio both verdicts must appear.
    assert!(
        sat > 0 && unsat > 0,
        "the threshold family degenerated to one verdict: sat={sat} unsat={unsat}"
    );
}

/// Degenerate shapes the random family cannot produce: an empty formula, an
/// empty clause, a unit contradiction, and a tautological clause. Each is a
/// place where two engines' normalisation can differ silently.
#[test]
fn degenerate_formulas_agree() {
    let cases: Vec<(&str, CnfFormula)> = vec![
        ("empty formula", CnfFormula::new(0)),
        ("empty formula with reserved vars", CnfFormula::new(4)),
        (
            "empty clause",
            parse_dimacs("p cnf 1 1\n0\n").expect("parse"),
        ),
        (
            "unit contradiction",
            parse_dimacs("p cnf 1 2\n1 0\n-1 0\n").expect("parse"),
        ),
        (
            "tautological clause",
            parse_dimacs("p cnf 1 1\n1 -1 0\n").expect("parse"),
        ),
        (
            "duplicated literal",
            parse_dimacs("p cnf 2 2\n1 1 2 0\n-1 0\n").expect("parse"),
        ),
    ];
    for (label, formula) in &cases {
        assert!(
            compare(label, formula),
            "{label}: a degenerate formula must be decided, not budgeted out"
        );
    }
}
