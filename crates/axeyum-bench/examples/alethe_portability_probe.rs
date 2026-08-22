//! Is an `unsat` artifact one an **external** checker can read? Measured per file.
//!
//! Two questions, one binary, because they are the same question at two depths.
//!
//! **`--portability` (default)** runs the shipped `produce_evidence` over each
//! file and prints the evidence kind, what `Evidence::portable_artifact` claims,
//! and — for Alethe artifacts — every rule name Carcara has no checker for. The
//! published "N of M certified `unsat` carry an artifact an external checker can
//! read" figure had no committed tool behind it; this is that tool. A rule name
//! the external checker does not know turns a "portable" artifact into an
//! `unknown rule` error, so the rule column is the claim, not the variant.
//!
//! **`--array-shapes`** censuses the `unsat-array-axiom` family — the largest
//! internal-only certified-`unsat` family — by `ArrayAxiomKind` and by the shape
//! of the refuted assertion, and reports how far each rung of the Alethe ladder
//! gets on it. Written to size a portability push before building one; the answer
//! it gave was that the rule vocabulary is not the binding constraint (see
//! `docs/research/07-verification/array-elimination-alethe-proofs.md`).
//!
//! Usage:
//! ```text
//! cargo run -p axeyum-bench --example alethe_portability_probe -- [--array-shapes] <file.smt2> ...
//! ```

use std::collections::BTreeMap;
use std::env;
use std::fs;

use axeyum_cnf::{AletheCommand, check_alethe, non_carcara_checked_rules};
use axeyum_ir::{Op, TermArena, TermId, TermNode};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    ArrayAxiomKind, Evidence, SolverConfig, array_axiom_refutation, produce_evidence_smtlib,
    prove_qf_abv_unsat_alethe, prove_qf_abv_unsat_alethe_via_elimination, prove_qf_bv_unsat_alethe,
    prove_qf_dt_unsat_alethe_via_simplification, prove_qf_uf_unsat_alethe,
    prove_qf_ufbv_unsat_alethe,
};

/// The `zero_trust_alethe_certificate` ladder, reproduced over the public API so
/// the probe measures what `produce_evidence` would emit if the array-axiom
/// structural certificate did not shadow it.
fn zero_trust_alethe(arena: &mut TermArena, assertions: &[TermId]) -> Option<Vec<AletheCommand>> {
    if let Some(p) = prove_qf_abv_unsat_alethe(arena, assertions)
        && matches!(check_alethe(&p), Ok(true))
    {
        return Some(p);
    }
    if let Some(p) = prove_qf_uf_unsat_alethe(arena, assertions)
        && matches!(check_alethe(&p), Ok(true))
    {
        return Some(p);
    }
    if let Some(p) = prove_qf_ufbv_unsat_alethe(arena, assertions)
        && matches!(check_alethe(&p), Ok(true))
    {
        return Some(p);
    }
    if let Some(p) = prove_qf_abv_unsat_alethe_via_elimination(arena, assertions)
        && matches!(check_alethe(&p), Ok(true))
    {
        return Some(p);
    }
    if let Some(p) = prove_qf_dt_unsat_alethe_via_simplification(arena, assertions)
        && matches!(check_alethe(&p), Ok(true))
    {
        return Some(p);
    }
    None
}

fn rules(proof: &[AletheCommand]) -> Vec<String> {
    let mut out: Vec<String> = proof
        .iter()
        .filter_map(|c| match c {
            AletheCommand::Step { rule, .. } => Some(rule.clone()),
            AletheCommand::Assume { .. } => None,
        })
        .collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// Per-file portability census over the shipped evidence route.
fn portability_census(files: &[String]) {
    // kind -> (instances, claimed portable)
    let mut by_kind: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    let mut foreign_rules: BTreeMap<String, usize> = BTreeMap::new();
    let config = SolverConfig::default();

    for path in files {
        let Ok(text) = fs::read_to_string(path) else {
            println!("{path}\tread-error");
            continue;
        };
        let report = match produce_evidence_smtlib(&text, &config) {
            Ok(report) => report,
            Err(error) => {
                println!("{path}\terror\t{error}");
                continue;
            }
        };
        let kind = report.evidence.kind_label().to_owned();
        // NOTE: `PortableArtifact` is not re-exported from `axeyum_solver`, so a
        // consumer outside the crate can call `portable_artifact` but cannot name
        // its return type. Reduced to a boolean here rather than worked around.
        let portable = report.evidence.portable_artifact().is_some();
        // The rules Carcara has no checker for, for whichever variant carries a
        // proof. Reported even when `portable_artifact` says `None`, because the
        // interesting case is an artifact that LOOKS portable.
        let foreign = match &report.evidence {
            Evidence::UnsatAletheProof(proof)
            | Evidence::UnsatArithAletheProof(proof)
            | Evidence::UnsatGuardedQuantAletheProof { proof, .. } => {
                non_carcara_checked_rules(proof)
            }
            _ => Vec::new(),
        };
        for rule in &foreign {
            *foreign_rules.entry(rule.clone()).or_default() += 1;
        }
        let entry = by_kind.entry(kind.clone()).or_default();
        entry.0 += 1;
        if portable {
            entry.1 += 1;
        }
        println!(
            "{path}\t{kind}\tportable={}\tnon-carcara-rules={}",
            if portable { "yes" } else { "no" },
            if foreign.is_empty() {
                "-".to_owned()
            } else {
                foreign.join(",")
            }
        );
    }

    println!();
    println!(
        "{:<40} {:>10} {:>10}",
        "evidence kind", "instances", "portable"
    );
    println!("{}", "-".repeat(62));
    let (mut t, mut p) = (0usize, 0usize);
    for (kind, (n, portable)) in &by_kind {
        t += n;
        p += portable;
        println!("{kind:<40} {n:>10} {portable:>10}");
    }
    println!("{:<40} {t:>10} {p:>10}", "TOTAL");
    if foreign_rules.is_empty() {
        println!("\nno artifact named a rule Carcara lacks");
    } else {
        println!("\nrules Carcara has no checker for (files naming each):");
        for (rule, n) in &foreign_rules {
            println!("  {rule:<28} {n}");
        }
    }
}

fn kind_label(kind: ArrayAxiomKind) -> &'static str {
    match kind {
        ArrayAxiomKind::ReadOverWrite => "ReadOverWrite",
        ArrayAxiomKind::SelectIte => "SelectIte",
        ArrayAxiomKind::StoreIteSelect => "StoreIteSelect",
        ArrayAxiomKind::ReadCongruence => "ReadCongruence",
        ArrayAxiomKind::StoreShadowing => "StoreShadowing",
    }
}

fn app(arena: &TermArena, t: TermId, want: Op) -> Option<&[TermId]> {
    match arena.node(t) {
        TermNode::App { op, args } if *op == want => Some(args),
        _ => None,
    }
}

/// `(not (= a b))` → `(a, b)`.
fn not_eq(arena: &TermArena, t: TermId) -> Option<(TermId, TermId)> {
    let args = app(arena, t, Op::BoolNot)?;
    let [inner] = args else { return None };
    let eq = app(arena, *inner, Op::Eq)?;
    let [a, b] = eq else { return None };
    Some((*a, *b))
}

/// `select(store(a, i, v), i)` vs `v`, either orientation.
fn row_same(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let one = |sel: TermId, val: TermId| -> bool {
        let Some([inner, j]) = app(arena, sel, Op::Select) else {
            return false;
        };
        let Some([_a, i, v]) = app(arena, *inner, Op::Store) else {
            return false;
        };
        *j == *i && *v == val
    };
    one(lhs, rhs) || one(rhs, lhs)
}

/// `select(store(a, i, v), j)` vs `select(a, j)`, either orientation.
fn row_diff(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let one = |sel: TermId, other: TermId| -> bool {
        let Some([inner, j]) = app(arena, sel, Op::Select) else {
            return false;
        };
        let Some([a, _i, _v]) = app(arena, *inner, Op::Store) else {
            return false;
        };
        let Some([oa, oj]) = app(arena, other, Op::Select) else {
            return false;
        };
        *oa == *a && *oj == *j
    };
    one(lhs, rhs) || one(rhs, lhs)
}

/// `select(store(a, i, v), j)` vs `ite(= i j, v, select(a, j))`, either orientation.
fn row_ite(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let one = |sel: TermId, other: TermId| -> bool {
        let Some([inner, j]) = app(arena, sel, Op::Select) else {
            return false;
        };
        let Some([a, i, v]) = app(arena, *inner, Op::Store) else {
            return false;
        };
        let Some([cond, then_b, else_b]) = app(arena, other, Op::Ite) else {
            return false;
        };
        let Some([ci, cj]) = app(arena, *cond, Op::Eq) else {
            return false;
        };
        let Some([ea, ej]) = app(arena, *else_b, Op::Select) else {
            return false;
        };
        ((*ci == *i && *cj == *j) || (*ci == *j && *cj == *i))
            && *then_b == *v
            && *ea == *a
            && *ej == *j
    };
    one(lhs, rhs) || one(rhs, lhs)
}

fn main() {
    let mut args: Vec<String> = env::args().skip(1).collect();
    let shapes = args.iter().any(|a| a == "--array-shapes");
    args.retain(|a| !a.starts_with("--"));
    let files = args;
    if files.is_empty() {
        eprintln!("usage: alethe_portability_probe [--array-shapes] <file.smt2> ...");
        return;
    }
    if shapes {
        array_shape_census(&files);
    } else {
        portability_census(&files);
    }
}

/// Census of the `unsat-array-axiom` family by `ArrayAxiomKind` and assertion shape.
#[allow(clippy::too_many_lines)]
fn array_shape_census(files: &[String]) {
    // kind -> counters
    let mut totals: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut top_level: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut diseq: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut same: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut diff: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut ite: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut alethe: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut elim_bv_ok: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut no_cert = 0usize;

    for path in files {
        let Ok(text) = fs::read_to_string(path) else {
            println!("{path}\tread-error");
            continue;
        };
        let mut script = match parse_script(&text) {
            Ok(script) => script,
            Err(error) => {
                println!("{path}\tparse-error\t{error}");
                continue;
            }
        };
        let arena = &script.arena;
        let Some(cert) = array_axiom_refutation(arena, &script.assertions) else {
            no_cert += 1;
            println!("{path}\tno-array-axiom-cert");
            continue;
        };
        let label = kind_label(cert.kind);
        *totals.entry(label).or_default() += 1;

        let is_top = script.assertions.contains(&cert.assertion);
        if is_top {
            *top_level.entry(label).or_default() += 1;
        }
        let is_diseq = not_eq(arena, cert.assertion)
            .is_some_and(|(a, b)| (a, b) == (cert.lhs, cert.rhs) || (b, a) == (cert.lhs, cert.rhs));
        if is_diseq {
            *diseq.entry(label).or_default() += 1;
        }
        let s = row_same(arena, cert.lhs, cert.rhs);
        let d = row_diff(arena, cert.lhs, cert.rhs);
        let i = row_ite(arena, cert.lhs, cert.rhs);
        if s {
            *same.entry(label).or_default() += 1;
        }
        if d {
            *diff.entry(label).or_default() += 1;
        }
        if i {
            *ite.entry(label).or_default() += 1;
        }
        let head = match arena.node(cert.assertion) {
            TermNode::App { op, .. } => format!("{op:?}"),
            other => format!("{other:?}"),
        };
        let nodes = axeyum_ir::TermStats::compute(arena, &[cert.assertion]).dag_nodes;
        let assertions = script.assertions.clone();
        // Would a bit-blast Alethe proof close the ELIMINATED (QF_BV) problem?
        // That is the ceiling for any route that justifies the array-elimination
        // rewrites and then bit-blasts: if this declines, no amount of array-rule
        // work makes the instance portable.
        let elim_bv = {
            let mut probe_arena = script.arena.clone();
            axeyum_rewrite::eliminate_arrays(&mut probe_arena, &assertions)
                .ok()
                .filter(axeyum_rewrite::ArrayElimination::had_arrays)
                .map(|e| e.assertions().to_vec())
                .and_then(|reduced| {
                    prove_qf_bv_unsat_alethe(&probe_arena, &reduced)
                        .filter(|p| matches!(check_alethe(p), Ok(true)))
                })
                .is_some()
        };
        if elim_bv {
            *elim_bv_ok.entry(label).or_default() += 1;
        }
        let zt = zero_trust_alethe(&mut script.arena, &assertions);
        let zt_rules = zt.as_deref().map(rules);
        if zt.is_some() {
            *alethe.entry(label).or_default() += 1;
        }
        println!(
            "{path}\t{label}\ttop={is_top}\tdiseq={is_diseq}\tsame={s}\tdiff={d}\tite={i}\thead={head}\tnodes={nodes}\telimbv={elim_bv}\talethe={}",
            zt_rules.map_or_else(|| "none".to_owned(), |r| r.join(","))
        );
    }

    println!();
    println!(
        "{:<18} {:>6} {:>9} {:>7} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "kind", "total", "top-level", "diseq", "same", "diff", "ite", "alethe", "elim-bv"
    );
    println!("{}", "-".repeat(82));
    let get = |m: &BTreeMap<&'static str, usize>, k: &'static str| *m.get(k).unwrap_or(&0);
    let mut grand = 0usize;
    for (kind, total) in &totals {
        grand += total;
        println!(
            "{kind:<18} {total:>6} {:>9} {:>7} {:>6} {:>6} {:>6} {:>7} {:>7}",
            get(&top_level, kind),
            get(&diseq, kind),
            get(&same, kind),
            get(&diff, kind),
            get(&ite, kind),
            get(&alethe, kind),
            get(&elim_bv_ok, kind),
        );
    }
    println!("TOTAL              {grand:>6}");
    println!("files with no array-axiom certificate: {no_cert}");
}
