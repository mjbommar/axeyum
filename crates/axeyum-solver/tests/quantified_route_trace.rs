//! Route attribution for **quantified** inputs (roadmap item 1.8).
//!
//! # What was wrong
//!
//! `auto::solve`'s quantified ladder — seventeen rungs, from a ground-subset
//! refutation to ℕ-induction — recorded nothing at all. It reported to stderr
//! under `AXEYUM_QTRACE` and nowhere else. That alone would be a missing
//! trace; what made it a *wrong* one is that the ladder sits **above**
//! `check_auto`, so `route_trace::with_outermost_dispatch`'s depth counter did
//! not cover it. Every speculative sub-solve a rung made — a validity check,
//! a witness validation, an MBQI ground round, an induction base/step query —
//! entered the attribution as an OUTERMOST dispatch and published its whole
//! quantifier-free route trail.
//!
//! Measured on the twelve `uflia_induction` corpus files before the fix
//! (10 s budget, this host):
//!
//! ```text
//! guarded_linear_closed_form.smt2   unsat    decided_by=lia-dpll
//! guarded_linear_nonneg.smt2        unsat    decided_by=lia-dpll
//! guarded_monotone_step.smt2        unsat    decided_by=lia-dpll
//! guarded_parity_range.smt2         unsat    decided_by=lia-dpll
//! guarded_false_base.smt2           unknown  decided_by=uf-arithmetic  (recorded SAT)
//! guarded_false_step.smt2           unknown  decided_by=uf-arithmetic  (recorded SAT)
//! guarded_product_factorial_bound   unknown  decided_by=uf-arithmetic  (recorded SAT)
//! guarded_sum_gauss.smt2            unknown  decided_by=uf-arith-online(recorded SAT)
//! guarded_wrong_slope.smt2          unknown  decided_by=uf-arithmetic  (recorded SAT)
//! unguarded_int_even_or_odd.smt2    unknown  decided_by=uf-arithmetic  (recorded SAT)
//! ```
//!
//! Every one of those four `unsat`s was decided by ℕ-induction, not by
//! `lia-dpll`; and on six files the named route's recorded verdict was `sat`
//! while the file's verdict was `unknown` — a route that did not decide the
//! file, reporting a verdict the file does not have.
//!
//! # What these tests pin
//!
//! The load-bearing invariant is [`decider_agrees_with_the_verdict`]: a
//! quantified file's trace may name a decider only if the file *was* decided,
//! and the decider's recorded verdict must be the file's verdict. That single
//! property fails on both halves of the old behaviour — on the misattributed
//! `unsat`s (the route is a QF one, caught by the companion assertion that the
//! decider is a ladder rung or a front-door stage) and on the six
//! `unknown`-with-a-`sat`-decider files directly.
//!
//! The rung vocabulary is read from `route_trace::quant_rung::ALL` — the
//! authority — rather than from a literal list here, so a rung added to the
//! ladder without a label cannot leave this suite green by omission.
#![cfg(feature = "full")]

use std::path::{Path, PathBuf};
use std::time::Duration;

use axeyum_solver::{
    CheckResult, RouteAttributionGuard, RouteOutcome, RouteTrace, SolverConfig, Verdict,
    last_route_attribution, route_trace, solve_smtlib,
};

/// Per-file wall budget. Large enough that the ℕ-induction rung (the last and
/// most expensive one) reaches a verdict on the files that have one, small
/// enough to keep the suite bounded. Files that hit it come back `unknown`,
/// which is a first-class result and exercises the undecided path — which is
/// exactly where the old behaviour was most wrong.
const BUDGET: Duration = Duration::from_millis(8_000);

/// The smallest quantified population this suite will accept. A shrunken
/// corpus would make every assertion below weaker without failing one.
const MIN_QUANTIFIED_FILES: usize = 10;

fn corpus_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/regression")
}

fn collect_smt2(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    paths.sort();
    for p in paths {
        if p.is_dir() {
            collect_smt2(&p, out);
        } else if p.extension().is_some_and(|e| e == "smt2") {
            out.push(p);
        }
    }
}

/// Every committed regression file carrying a quantifier, with its text.
fn quantified_corpus() -> Vec<(PathBuf, String)> {
    let root = corpus_root();
    assert!(
        root.is_dir(),
        "regression corpus missing at {}",
        root.display()
    );
    let mut files = Vec::new();
    collect_smt2(&root, &mut files);
    let quantified: Vec<(PathBuf, String)> = files
        .into_iter()
        .filter_map(|p| std::fs::read_to_string(&p).ok().map(|t| (p, t)))
        .filter(|(_, text)| text.contains("(forall ") || text.contains("(exists "))
        .collect();
    assert!(
        quantified.len() >= MIN_QUANTIFIED_FILES,
        "expected at least {MIN_QUANTIFIED_FILES} quantified corpus files, found {} — \
         a shrunken population would make every assertion below weaker without failing",
        quantified.len()
    );
    quantified
}

fn config() -> SolverConfig {
    SolverConfig {
        timeout: Some(BUDGET),
        ..SolverConfig::default()
    }
}

/// Solves `text` with attribution on, returning the verdict tag and the trace.
fn solve_traced(text: &str) -> (&'static str, RouteTrace) {
    let cfg = config();
    let guard = RouteAttributionGuard::enable();
    let outcome = solve_smtlib(text, &cfg);
    drop(guard);
    let tag = match &outcome {
        Ok(o) => match o.result {
            CheckResult::Sat(_) => "sat",
            CheckResult::Unsat => "unsat",
            CheckResult::Unknown(_) => "unknown",
        },
        Err(_) => "error",
    };
    (tag, last_route_attribution())
}

/// Whether `route` is a label the ladder or the front door owns, as opposed to
/// a quantifier-free dispatch route. Derived from the authority
/// (`quant_rung::ALL`) plus the `fd:` prefix the front-door stages carry.
fn is_ladder_or_front_door(route: &str) -> bool {
    route_trace::quant_rung::ALL.contains(&route) || route.starts_with("fd:")
}

/// THE property. A quantified file's trace names a decider only when the file
/// was decided, and that decider's recorded verdict is the file's verdict.
///
/// Both halves of the pre-fix behaviour violate this: the four misattributed
/// `unsat`s named a route that is neither a rung nor a front-door stage, and
/// six `unknown` files named a route recorded as `sat`.
#[test]
fn decider_agrees_with_the_verdict() {
    let mut checked = 0usize;
    let mut decided = 0usize;
    let mut failures: Vec<String> = Vec::new();

    for (path, text) in quantified_corpus() {
        let (tag, trace) = solve_traced(&text);
        if tag == "error" {
            continue;
        }
        checked += 1;
        let name = path.display().to_string();
        match (tag, trace.decided_by()) {
            ("unknown", Some((_, attempt, _))) => {
                failures.push(format!(
                    "{name}: verdict is unknown but the trace names {} as the decider ({})",
                    attempt.route, attempt.outcome
                ));
            }
            ("unknown", None) => {}
            (_, None) => {
                failures.push(format!(
                    "{name}: verdict is {tag} but the trace names no decider"
                ));
            }
            (_, Some((_, attempt, _))) => {
                decided += 1;
                let recorded = match attempt.outcome {
                    RouteOutcome::Decided(Verdict::Sat) => "sat",
                    RouteOutcome::Decided(Verdict::Unsat) => "unsat",
                    _ => unreachable!("decided_by returns only Decided outcomes"),
                };
                if recorded != tag {
                    failures.push(format!(
                        "{name}: verdict is {tag} but the decider {} recorded {recorded}",
                        attempt.route
                    ));
                }
                if !is_ladder_or_front_door(attempt.route) {
                    failures.push(format!(
                        "{name}: verdict is {tag} but the decider is the quantifier-free route \
                         {} — a quantified file must be attributed to the ladder rung that \
                         decided it, not to a sub-route one of its probes fell into",
                        attempt.route
                    ));
                }
            }
        }
    }

    assert!(
        failures.is_empty(),
        "{} quantified file(s) misattributed:\n{}",
        failures.len(),
        failures.join("\n")
    );
    assert!(
        checked >= MIN_QUANTIFIED_FILES,
        "only {checked} quantified files solved without error"
    );
    // Non-vacuity: an all-`unknown` population would satisfy the loop above
    // perfectly while checking nothing about attribution.
    assert!(
        decided >= 4,
        "only {decided} quantified corpus files were decided; with fewer than 4 this gate \
         cannot distinguish a correct attribution from an absent one"
    );
}

/// Every quantified file's trace contains at least one ladder rung entry.
///
/// This is the anti-vacuity partner of the test above: a recorder that stopped
/// writing entirely would make `decided_by()` `None` everywhere and satisfy the
/// "unknown ⇒ no decider" half of the invariant for free.
#[test]
fn every_quantified_file_records_at_least_one_rung() {
    let mut without: Vec<String> = Vec::new();
    let mut total = 0usize;
    for (path, text) in quantified_corpus() {
        let (tag, trace) = solve_traced(&text);
        if tag == "error" {
            continue;
        }
        total += 1;
        if !trace
            .attempts()
            .iter()
            .any(|a| route_trace::quant_rung::ALL.contains(&a.route))
        {
            without.push(path.display().to_string());
        }
    }
    assert!(total > 0, "no quantified corpus file was solved");
    assert!(
        without.is_empty(),
        "{} of {total} quantified file(s) recorded no ladder rung at all:\n{}",
        without.len(),
        without.join("\n")
    );
}

/// The exit criterion, stated on the rung that motivated the item: the
/// `uflia_induction` files that come back `unsat` are decided by ℕ-induction,
/// and the trace says so.
///
/// Before this change all four named `lia-dpll` — a route that ran only inside
/// the induction rung's own base/step sub-queries.
#[test]
fn nat_induction_names_itself() {
    let mut by_nat_induction = 0usize;
    let mut wrong: Vec<String> = Vec::new();
    for (path, text) in quantified_corpus() {
        if !path.to_string_lossy().contains("uflia_induction") {
            continue;
        }
        let (tag, trace) = solve_traced(&text);
        if tag != "unsat" {
            continue;
        }
        match trace.decided_by() {
            Some((_, attempt, _)) if attempt.route == route_trace::quant_rung::NAT_INDUCTION => {
                by_nat_induction += 1;
            }
            Some((_, attempt, _)) => wrong.push(format!(
                "{}: unsat attributed to {} instead of {}",
                path.display(),
                attempt.route,
                route_trace::quant_rung::NAT_INDUCTION
            )),
            None => wrong.push(format!("{}: unsat with no decider", path.display())),
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    assert!(
        by_nat_induction >= 1,
        "no uflia_induction file was decided at all, so this gate proved nothing about the \
         ℕ-induction rung's attribution"
    );
}

/// A rung that reduces the query to a quantifier-free residual keeps the QF
/// dispatch's own route entries underneath its own — the ladder attribution
/// replaces the misattribution, it does not throw the detail away.
#[test]
fn a_reduce_to_qf_rung_keeps_the_dispatch_detail() {
    let text =
        std::fs::read_to_string(corpus_root().join("uflia_induction/unguarded_int_nonneg.smt2"))
            .expect("unguarded_int_nonneg.smt2 is a committed corpus file");
    let (tag, trace) = solve_traced(&text);
    assert_eq!(tag, "sat", "corpus verdict moved");
    let routes: Vec<&str> = trace.attempts().iter().map(|a| a.route).collect();
    let rung = routes
        .iter()
        .position(|r| *r == route_trace::quant_rung::SKOLEM_QF)
        .expect("skolemization-to-QF rung should be recorded");
    let closing = routes
        .iter()
        .rposition(|r| *r == route_trace::quant_rung::SKOLEM_QF)
        .expect("the rung closes the trail");
    assert!(
        closing > rung,
        "the rung should appear twice — a probe before the dispatch and its result after: {routes:?}"
    );
    assert!(
        routes[rung + 1..closing]
            .iter()
            .any(|r| !is_ladder_or_front_door(r)),
        "the quantifier-free dispatch's own routes should sit between the rung's probe and its \
         result: {routes:?}"
    );
    let (_, attempt, _) = trace.decided_by().expect("a sat file has a decider");
    assert_eq!(
        attempt.route,
        route_trace::quant_rung::SKOLEM_QF,
        "the rung, not the QF sub-route, is the decider: {routes:?}"
    );
}

/// THE ATTRIBUTION GUARD FOR ADR-1906.
///
/// The full MBQI pass records its verdict **last** in
/// `finish_quantified_solve`'s terminal arm, on purpose, so MBQI owns the
/// trail's last word instead of a declined finite-model probe. The route trail
/// charges a segment to whoever records NEXT, so before ADR-1906 that deferral
/// also deferred the COST: `q:mbqi` read ~5 **microseconds** on every file
/// while its real seconds were billed to `q:uf-fmf-full`, and
/// `bound_by=q:uf-fmf-full` meant "MBQI plus the finder".
///
/// # How the ground truth was established
///
/// Not by assumption. On these same nine committed files, measured 2026-09-10
/// with the pre-fix and post-fix binaries plus `AXEYUM_QTRACE` — a genuinely
/// separate instrument (stderr checkpoint stamps, not the `RouteTrace`):
///
/// ```text
/// file                             q:mbqi  fmf-full  |  q:mbqi  fmf-full  |  qtrace mbqi
///                                  ---- pre-fix ----    ---- post-fix ---
/// guarded_linear_nonneg.smt2         0 ms    352 ms       359 ms     0 ms       350 ms
/// unguarded_int_even_or_odd.smt2     0 ms    453 ms       455 ms     0 ms       435 ms
/// guarded_false_step.smt2            0 ms     31 ms        31 ms     0 ms        31 ms
/// ```
///
/// The independent instrument agrees with the post-fix column to within a few
/// percent, so the quantity that used to be labelled `q:uf-fmf-full` was
/// entirely MBQI's. Verdicts were identical in both arms on all nine.
///
/// # Why the threshold is what it is
///
/// The smallest true MBQI pass in this population is 31 ms; the pre-fix reading
/// was ~5 us. `MIN_MBQI_MS` sits at 5 — a 6x margin below the smallest real
/// value and about a thousand-fold above what the deferred-cost defect
/// produced — so restoring the old ordering (dropping the
/// `take_attribution_open_segment` at the pass's return, or recording MBQI
/// through the plain sink) fails this test, and nothing is close enough to the
/// line to make it flaky.
#[test]
fn the_full_mbqi_rung_is_charged_its_own_wall_clock() {
    /// A real MBQI pass here is 31 ms at the smallest; the deferred-cost defect
    /// produced ~0.005 ms. See the doc comment for the measured table.
    const MIN_MBQI_MS: u128 = 5;
    /// Below this the test is measuring nothing and must say so rather than
    /// pass. Nine of the twelve `uflia_induction` files reach the terminal arm.
    const MIN_FILES_REACHING_THE_ARM: usize = 6;

    let dir = corpus_root().join("uflia_induction");
    let mut files: Vec<PathBuf> = Vec::new();
    collect_smt2(&dir, &mut files);
    assert!(
        !files.is_empty(),
        "the uflia_induction corpus is missing at {}",
        dir.display()
    );

    let mut reached = Vec::new();
    let mut too_cheap = Vec::new();
    for path in files {
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        let (_, trace) = solve_traced(&text);
        let Some(i) = trace
            .attempts()
            .iter()
            .position(|a| a.route == route_trace::quant_rung::MBQI)
        else {
            continue;
        };
        let ms = trace.elapsed()[i].as_millis();
        let name = path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .into_owned();
        reached.push((name.clone(), ms));
        if ms < MIN_MBQI_MS {
            too_cheap.push((name, ms));
        }
    }

    assert!(
        reached.len() >= MIN_FILES_REACHING_THE_ARM,
        "only {} file(s) reached the terminal MBQI arm; below {MIN_FILES_REACHING_THE_ARM} this \
         test cannot fail for the reason it exists and is reporting a vacuous pass: {reached:?}",
        reached.len()
    );
    assert!(
        too_cheap.is_empty(),
        "q:mbqi must be charged its OWN pass, not ~0 while q:uf-fmf-full carries it (ADR-1906). \
         These files recorded a sub-{MIN_MBQI_MS}ms MBQI segment: {too_cheap:?} \
         (all files reaching the arm: {reached:?})"
    );
}

/// The other half of ADR-1906, which the guard above cannot see: the cost that
/// moved onto `q:mbqi` must have come OUT of `q:uf-fmf-full`, not been created.
///
/// A fix that handed MBQI an explicit duration **without** taking it off the
/// running clock would satisfy the guard above and silently double-count —
/// inflating `total_ms`, which is the denominator every published clock share
/// divides by. That failure is invisible per-rung and visible only here.
///
/// The finder's own segment on this population is sub-millisecond (measured:
/// 42-196 us across all nine files), because on a file that reaches this arm
/// with an `unknown` from MBQI the finder is entered with the budget already
/// spent. So `q:uf-fmf-full` carrying an MBQI-sized segment means the take did
/// not happen; both rungs carrying one means it happened twice.
#[test]
fn the_finder_keeps_only_its_own_segment() {
    /// The finder's real segment here is under 1 ms. A pre-fix reading was
    /// 31-453 ms — MBQI's pass. 10 ms separates the two by 3x and 45x.
    const MAX_FINDER_MS: u128 = 10;
    const MIN_FILES_REACHING_THE_ARM: usize = 6;

    let dir = corpus_root().join("uflia_induction");
    let mut files: Vec<PathBuf> = Vec::new();
    collect_smt2(&dir, &mut files);

    let mut reached = Vec::new();
    let mut overcharged = Vec::new();
    for path in files {
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        let (_, trace) = solve_traced(&text);
        let Some(i) = trace
            .attempts()
            .iter()
            .position(|a| a.route == route_trace::quant_rung::UF_FMF_FULL)
        else {
            continue;
        };
        let ms = trace.elapsed()[i].as_millis();
        let name = path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .into_owned();
        reached.push((name.clone(), ms));
        if ms > MAX_FINDER_MS {
            overcharged.push((name, ms));
        }
    }

    assert!(
        reached.len() >= MIN_FILES_REACHING_THE_ARM,
        "only {} file(s) recorded q:uf-fmf-full; this test would be vacuous: {reached:?}",
        reached.len()
    );
    assert!(
        overcharged.is_empty(),
        "q:uf-fmf-full must carry ONLY the finder's own segment, never MBQI's pass as well \
         (ADR-1906). Overcharged: {overcharged:?} (all: {reached:?})"
    );
}
