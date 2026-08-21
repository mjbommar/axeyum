//! The propositional Craig interpolant ships a certificate an OUTSIDE checker
//! accepts.
//!
//! Every other interpolating area in this repository already had a `*_certified`
//! sibling beside its plain interpolant — `QF_BV`, `QF_UF`, `QF_LRA`, `QF_LIA`,
//! `QF_UFLRA`, `QF_UFLIA` — each of the same shape: the same verified `I`, plus two
//! externally-checkable refutations of the Craig conditions. `SAT (propositional)`
//! was the only one without, which is why it sat in band 1 of
//! `scripts/check-capability-assurance.py --rank`: "artifact already built —
//! export it and point a checker at it".
//!
//! Literally already built. `verify_interpolant` discharged `A ∧ ¬I` and `I ∧ B`
//! with the proof-producing core and checked each DRAT with `check_drat`, then
//! returned a `bool` and dropped both proofs. Nothing new is proved here; the
//! proofs are returned.
//!
//! # What each test is for
//!
//! The in-tree checks pin the certificate's internal consistency. The
//! `drat-trim` test is the one that makes the capability externally checked: an
//! independent C implementation, not ours, reading the artifact we hand out.

use std::io::Write;
use std::process::Command;

use axeyum_cnf::{
    CnfClause, CnfFormula, CnfLit, CnfVar, check_drat, propositional_interpolant,
    propositional_interpolant_certified, write_drat,
};

/// `A = x1 ∧ (¬x1 ∨ x2)`, `B = ¬x2`. Unsat, and the only shared variable is
/// `x2`, so the interpolant must be `x2` (up to representation).
fn partition() -> (CnfFormula, CnfFormula) {
    let x1 = CnfVar::new(0).expect("var x1");
    let x2 = CnfVar::new(1).expect("var x2");

    let mut a = CnfFormula::new(2);
    a.add_clause(CnfClause::new(vec![CnfLit::positive(x1)]))
        .expect("A clause 1");
    a.add_clause(CnfClause::new(vec![
        CnfLit::positive(x1).negated(),
        CnfLit::positive(x2),
    ]))
    .expect("A clause 2");

    let mut b = CnfFormula::new(2);
    b.add_clause(CnfClause::new(vec![CnfLit::positive(x2).negated()]))
        .expect("B clause 1");

    (a, b)
}

#[test]
fn the_certified_interpolant_is_the_one_the_plain_route_returns() {
    let (a, b) = partition();
    let plain = propositional_interpolant(&a, &b).expect("plain interpolant exists");
    let cert = propositional_interpolant_certified(&a, &b).expect("certified interpolant exists");
    assert_eq!(
        format!("{plain:?}"),
        format!("{:?}", cert.interpolant),
        "the certified route returned a DIFFERENT interpolant than the plain route. They must \
         share one construction; two that can disagree means the certificate proves conditions \
         about a term the plain caller never sees"
    );
}

#[test]
fn both_craig_refutations_check_against_the_carried_formulas() {
    let (a, b) = partition();
    let cert = propositional_interpolant_certified(&a, &b).expect("certified interpolant exists");
    assert_eq!(
        check_drat(&cert.a_and_not_i, &cert.a_refutation),
        Ok(true),
        "the A ∧ ¬I refutation does not check against the formula shipped with it"
    );
    assert_eq!(
        check_drat(&cert.i_and_b, &cert.b_refutation),
        Ok(true),
        "the I ∧ B refutation does not check against the formula shipped with it"
    );
    assert!(
        !cert.a_refutation.is_empty() && !cert.b_refutation.is_empty(),
        "an empty proof would 'check' against an already-contradictory formula and prove nothing"
    );
}

#[test]
fn the_vocabulary_condition_holds_so_the_certificate_is_a_craig_interpolant() {
    let (a, b) = partition();
    let cert = propositional_interpolant_certified(&a, &b).expect("certified interpolant exists");
    let shared = CnfVar::new(1).expect("var x2");
    assert!(
        cert.interpolant.vars().iter().all(|&v| v == shared),
        "the interpolant mentions a non-shared variable; conditions 1 and 2 can both hold for a \
         term that is not an interpolant at all"
    );
}

/// Negative control for the two checks above.
///
/// They are only worth something if `check_drat` can REJECT. Dropping the last
/// step of a refutation must break it — otherwise the proof was not being read.
#[test]
fn a_truncated_refutation_is_rejected() {
    let (a, b) = partition();
    let cert = propositional_interpolant_certified(&a, &b).expect("certified interpolant exists");
    let mut truncated = cert.a_refutation.clone();
    truncated
        .pop()
        .expect("the refutation has at least one step");
    assert_ne!(
        check_drat(&cert.a_and_not_i, &truncated),
        Ok(true),
        "a refutation with its final step removed still 'verified'. The checker is not deriving \
         the empty clause from these steps, so accepting the full proof means nothing"
    );
}

/// Negative control: a refutation must not "check" against a SATISFIABLE formula.
///
/// The obvious control — checking the `A ∧ ¬I` proof against the `I ∧ B`
/// formula — is vacuous here and was removed after being written. Both of this
/// partition's conjunctions refute by unit propagation alone, so both DRAT
/// proofs are the single step `0`, and one empty-clause derivation legitimately
/// checks against either. A control has to be one the artifact could fail:
/// `A` on its own is satisfiable (`x1 = x2 = true`), so nothing refutes it.
#[test]
fn a_refutation_does_not_check_against_a_satisfiable_formula() {
    let (a, b) = partition();
    let cert = propositional_interpolant_certified(&a, &b).expect("certified interpolant exists");
    assert_ne!(
        check_drat(&a, &cert.a_refutation),
        Ok(true),
        "the refutation verified against A alone, which is satisfiable. A checker that accepts \
         a proof of a satisfiable formula accepts anything, so its acceptance of the real \
         certificate would establish nothing"
    );
}

/// `PHP(3,2)`: three pigeons, two holes. Every variable is shared.
///
/// Exists because the partition above refutes by unit propagation, so its
/// exported proofs are one step long — a thin demonstration that we can hand out
/// a *proof*. This one needs case analysis, so the refutation has real
/// resolution steps in it.
fn pigeonhole_partition() -> (CnfFormula, CnfFormula) {
    // p(i, j) = pigeon i occupies hole j, for i in 0..3, j in 0..2.
    let p = |i: usize, j: usize| {
        CnfLit::positive(CnfVar::new(i * 2 + j).expect("pigeonhole variable index"))
    };
    let vars = 6;

    // A: every pigeon is in some hole. Satisfiable on its own.
    let mut a = CnfFormula::new(vars);
    for i in 0..3 {
        a.add_clause(CnfClause::new(vec![p(i, 0), p(i, 1)]))
            .expect("pigeon clause");
    }

    // B: no hole holds two pigeons. Also satisfiable on its own (all false).
    let mut b = CnfFormula::new(vars);
    for j in 0..2 {
        for i in 0..3 {
            for k in (i + 1)..3 {
                b.add_clause(CnfClause::new(vec![p(i, j).negated(), p(k, j).negated()]))
                    .expect("hole clause");
            }
        }
    }
    (a, b)
}

/// The export works on a refutation that is not a one-liner.
#[test]
fn a_pigeonhole_refutation_exports_and_checks() {
    let (a, b) = pigeonhole_partition();
    let cert = propositional_interpolant_certified(&a, &b)
        .expect("PHP(3,2) is unsat and conjunctively interpolable");
    assert_eq!(check_drat(&cert.a_and_not_i, &cert.a_refutation), Ok(true));
    assert_eq!(check_drat(&cert.i_and_b, &cert.b_refutation), Ok(true));
    let steps = cert.a_refutation.len() + cert.b_refutation.len();
    assert!(
        steps > 2,
        "the pigeonhole refutations totalled {steps} steps, which is no more than the trivial \
         partition needs. This test exists to exercise a proof with real resolution in it; if \
         PHP(3,2) now refutes by propagation alone, pick a harder instance"
    );
    eprintln!("PHP(3,2): {steps} exported proof steps across both Craig conditions");
}

/// And an independent checker accepts THAT one too.
#[test]
fn an_independent_checker_accepts_the_pigeonhole_certificate() {
    let Some(bin) = drat_trim() else {
        eprintln!("SKIP: no drat-trim binary");
        return;
    };
    let (a, b) = pigeonhole_partition();
    let cert = propositional_interpolant_certified(&a, &b).expect("PHP(3,2) interpolates");
    for (label, formula, proof) in [
        ("php_A_and_not_I", &cert.a_and_not_i, &cert.a_refutation),
        ("php_I_and_B", &cert.i_and_b, &cert.b_refutation),
    ] {
        let verdict = run_drat_trim(&bin, &formula.to_dimacs(), &write_drat(proof), label);
        assert!(
            verdict.contains("s VERIFIED"),
            "{label}: drat-trim rejected the exported pigeonhole certificate: {verdict}"
        );
    }
}

/// Locate `drat-trim`, or `None` to skip. `AXEYUM_REQUIRE_DRAT_TRIM=1` turns a
/// missing binary into a failure, for CI.
fn drat_trim() -> Option<String> {
    if let Ok(path) = std::env::var("AXEYUM_DRAT_TRIM_BIN") {
        return std::path::Path::new(&path).is_file().then_some(path);
    }
    let vendored = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../references/drat-trim/drat-trim"
    );
    std::path::Path::new(vendored)
        .is_file()
        .then(|| vendored.to_string())
}

/// **The test that makes this capability externally checked**: an independent C
/// implementation reads the artifact and agrees.
///
/// `drat-trim` is Marijn Heule's checker, cloned by `scripts/fetch-references.sh`
/// and not built by default, so a missing binary SKIPS rather than fails —
/// except under `AXEYUM_REQUIRE_DRAT_TRIM=1`.
#[test]
fn an_independent_checker_accepts_both_refutations() {
    let Some(bin) = drat_trim() else {
        assert!(
            std::env::var("AXEYUM_REQUIRE_DRAT_TRIM").unwrap_or_default() != "1",
            "AXEYUM_REQUIRE_DRAT_TRIM=1 but no drat-trim binary; build it with \
             `scripts/fetch-references.sh`"
        );
        eprintln!("SKIP: no drat-trim binary (scripts/fetch-references.sh builds it)");
        return;
    };
    let (a, b) = partition();
    let cert = propositional_interpolant_certified(&a, &b).expect("certified interpolant exists");

    for (label, formula, proof) in [
        ("A_and_not_I", &cert.a_and_not_i, &cert.a_refutation),
        ("I_and_B", &cert.i_and_b, &cert.b_refutation),
    ] {
        let verdict = run_drat_trim(&bin, &formula.to_dimacs(), &write_drat(proof), label);
        assert!(
            verdict.contains("s VERIFIED"),
            "{label}: drat-trim did not verify the exported certificate. Either the DIMACS and \
             the DRAT disagree about the formula, or the proof is wrong; both are defects in \
             what we hand a third party. Output: {verdict}"
        );
    }
}

/// Negative control for the external checker itself.
///
/// `s VERIFIED` is only evidence if this binary can say otherwise on our own
/// artifacts — an external checker that accepts anything is worth no more than a
/// gate that cannot fail.
#[test]
fn the_independent_checker_rejects_a_tampered_certificate() {
    let Some(bin) = drat_trim() else {
        eprintln!("SKIP: no drat-trim binary");
        return;
    };
    let (a, b) = partition();
    let cert = propositional_interpolant_certified(&a, &b).expect("certified interpolant exists");

    // Same proof, pointed at the SATISFIABLE half of the partition. Nothing
    // refutes A alone, so a checker that reads the proof must refuse it.
    let verdict = run_drat_trim(
        &bin,
        &a.to_dimacs(),
        &write_drat(&cert.a_refutation),
        "tampered",
    );
    assert!(
        !verdict.contains("s VERIFIED"),
        "drat-trim verified a refutation of a satisfiable formula, so its acceptance of the real \
         certificate above establishes nothing. Output: {verdict}"
    );
}

fn run_drat_trim(bin: &str, dimacs: &str, drat: &str, label: &str) -> String {
    let dir =
        std::env::temp_dir().join(format!("axeyum-interp-cert-{label}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let cnf = dir.join("f.cnf");
    let prf = dir.join("f.drat");
    std::fs::File::create(&cnf)
        .and_then(|mut f| f.write_all(dimacs.as_bytes()))
        .expect("write cnf");
    std::fs::File::create(&prf)
        .and_then(|mut f| f.write_all(drat.as_bytes()))
        .expect("write drat");
    let out = Command::new(bin)
        .arg(&cnf)
        .arg(&prf)
        .output()
        .expect("drat-trim runs");
    let _ = std::fs::remove_dir_all(&dir);
    String::from_utf8_lossy(&out.stdout).into_owned()
}
