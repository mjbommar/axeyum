//! A/B the CDCL core's search policies on real DIMACS, in one binary.
//!
//! ```sh
//! cargo run --release -p axeyum-cnf --example clause_db_policy_ab -- \
//!     [--arms tiered,legacy] [--max-conflicts N] [--seconds S] <file.cnf>...
//! ```
//!
//! The quantity this reports is **conflicts to solution**, not wall time. A
//! clause-database policy is a claim about search *quality*: it should let the
//! search reach the same verdict after fewer conflicts. Wall time is reported
//! too, because a policy that halves the conflicts and triples the per-conflict
//! cost has not helped, but the conflict count is the number the change targets.
//!
//! Both arms run in the **same binary** on the **same trajectory code**; the only
//! difference is the [`SearchPolicies`] object. That removes build variance,
//! compiler-version variance and mtime-staleness from the comparison, all three
//! of which have produced wrong A/B answers in this repository before.
//!
//! A run that hits `max_conflicts` or the deadline reports `resource_out` /
//! `interrupted` and its conflict count is a *budget*, not a measurement — such
//! rows must not be averaged into a conflicts-to-solution claim, and the output
//! labels them so a driver can drop them.
//!
//! Output is one JSON object per (file, arm) on stdout.

use std::hint::black_box;
use std::time::{Duration, Instant};

use axeyum_bv::lower_terms;
use axeyum_cnf::clause_db_policy::DeleteFraction;
use axeyum_cnf::{
    CnfFormula, DratSink, SearchCounters, SearchPolicies, StreamingProofOutcome, parse_dimacs,
    solve_with_drat_proof_counted_with_policies, tseitin_encode,
};
use axeyum_ir::{Sort, TermArena};

/// The no-proof control sink: accepts every step and keeps nothing, so the
/// measurement is search cost and not proof-recording cost. The core still
/// *calls* it at every learned clause and every deletion, which is structural.
#[derive(Default)]
struct CountingNullSink {
    steps: u64,
    deletions: u64,
}

impl DratSink for CountingNullSink {
    fn add_clause(
        &mut self,
        _lits: &[axeyum_cnf::CnfLit],
    ) -> Result<(), axeyum_cnf::ProofSinkError> {
        self.steps += 1;
        Ok(())
    }

    fn delete_clause(
        &mut self,
        _lits: &[axeyum_cnf::CnfLit],
    ) -> Result<(), axeyum_cnf::ProofSinkError> {
        self.steps += 1;
        self.deletions += 1;
        Ok(())
    }
}

/// A tier policy with `max_used` overridden -- the knob that decides how many
/// reduce rounds a tier1 clause survives after its last use, and therefore how
/// large the clause database grows.
fn tiered_with_max_used(max_used: u8) -> SearchPolicies {
    let mut p = SearchPolicies::default();
    p.clause_db.max_used = max_used;
    p
}

/// A tier policy with a flat deletion fraction instead of the 50->90 ramp, in
/// per mille. `CaDiCaL` uses a flat 75%.
fn tiered_with_fraction(permille: u32) -> SearchPolicies {
    let mut p = SearchPolicies::default();
    p.clause_db.fraction = DeleteFraction::Fixed { permille };
    p
}

/// Both knobs at once: the shortened tier1 lifetime and a flat aggressive
/// fraction, the pair that a measurement on the claim corpus suggested.
fn tiered_tuned(max_used: u8, permille: u32) -> SearchPolicies {
    let mut p = SearchPolicies::default();
    p.clause_db.max_used = max_used;
    p.clause_db.fraction = DeleteFraction::Fixed { permille };
    p
}

/// A **bit-blasted** instance built in process, named on the command line as
/// `bitblast:<factor_width>x<constraints>` where a plain path would go.
///
/// The committed CNF in this repository is combinatorial (van der Waerden,
/// Rado), and a clause-database or watch-layout change measured only on those
/// is measured on the wrong shape: our real workload is `QF_BV` bit-blasted
/// through `axeyum-bv` and Tseitin-encoded, which has a completely different
/// clause-length profile — in particular a far larger binary population, since
/// a Tseitin AND gate emits two binary clauses and one ternary. Bit-blasted
/// files from the real corpus are 2-270 MB and cannot be committed, so the
/// fixture is *generated*: `constraints` independent bounded-factor
/// multiplications of `factor_width`-bit factors against fixed semiprimes, the
/// same construction as `benches/proof_sat_propagate.rs`, whose measured shape
/// sits in the p4dfa range rather than the pigeonhole range.
///
/// Deterministic and seed-free: the two integers in the name fix the formula.
fn bitblast_formula(factor_width: u32, constraints: usize) -> CnfFormula {
    // Primes just under 2^31, so both factors of every product need the full
    // 32-bit width and the degenerate `N x 1` factorisation is unrepresentable.
    const PRIMES: [u128; 5] = [
        2_147_483_647,
        2_147_483_629,
        2_147_483_587,
        2_147_483_579,
        2_147_483_563,
    ];
    let product_width = factor_width * 2;
    let mut arena = TermArena::new();
    let zero = arena.bv_const(factor_width, 0).unwrap();
    let mut conjuncts = Vec::with_capacity(constraints);
    for i in 0..constraints {
        // A fixed, index-derived pair of distinct primes: no randomness.
        let p = PRIMES[i % PRIMES.len()];
        let q = PRIMES[(i / PRIMES.len() + i % PRIMES.len() + 1) % PRIMES.len()];
        let mask = if factor_width >= 128 {
            u128::MAX
        } else {
            (1u128 << factor_width) - 1
        };
        let n = (p & mask) * (q & mask);
        let a_sym = arena
            .declare(&format!("a{i}"), Sort::BitVec(factor_width))
            .unwrap();
        let b_sym = arena
            .declare(&format!("b{i}"), Sort::BitVec(factor_width))
            .unwrap();
        let a = arena.var(a_sym);
        let b = arena.var(b_sym);
        // Zero-extend by concatenation so the product cannot wrap.
        let a_wide = arena.concat(zero, a).unwrap();
        let b_wide = arena.concat(zero, b).unwrap();
        let product = arena.bv_mul(a_wide, b_wide).unwrap();
        let target = arena.bv_const(product_width, n).unwrap();
        conjuncts.push(arena.eq(product, target).unwrap());
    }
    let lowering = lower_terms(&arena, &conjuncts).unwrap();
    let roots: Vec<_> = lowering.roots().iter().map(|r| r.bits()[0]).collect();
    let encoding = tseitin_encode(lowering.aig(), &roots).expect("fixed AIG encodes cleanly");
    encoding.formula().clone()
}

/// Resolves a command-line instance name to a formula: either a DIMACS path or
/// a `bitblast:<width>x<count>` synthetic instance.
fn load(name: &str) -> CnfFormula {
    if let Some(spec) = name.strip_prefix("bitblast:") {
        let (width, count) = spec
            .split_once('x')
            .expect("bitblast spec is <factor_width>x<constraints>");
        return bitblast_formula(
            width.parse().expect("factor width is an integer"),
            count.parse().expect("constraint count is an integer"),
        );
    }
    let text = std::fs::read_to_string(name).expect("read the DIMACS file");
    parse_dimacs(&text).expect("parse the DIMACS file")
}

fn arm(name: &str) -> Option<SearchPolicies> {
    if let Some(rest) = name.strip_prefix("tiered-tuned") {
        let (used, frac) = rest.split_once('-')?;
        return Some(tiered_tuned(used.parse().ok()?, frac.parse().ok()?));
    }
    if let Some(rest) = name.strip_prefix("tiered-frac") {
        return rest.parse::<u32>().ok().map(tiered_with_fraction);
    }
    if let Some(rest) = name.strip_prefix("tiered-used") {
        return rest
            .parse::<u8>()
            .ok()
            .filter(|&n| n >= 1)
            .map(tiered_with_max_used);
    }
    match name {
        // The shipped default: tier clause database, pinned phasing.
        "tiered" => Some(SearchPolicies::default()),
        // The tier database with the pre-2026-09 reduce-round watch sweep
        // (clear all lists, re-push a pair per live clause from the arena).
        // Isolates the R10 sweep change from everything else: this arm and
        // `tiered` differ ONLY in how the watch lists are restored after a
        // reduce round.
        "tiered-rebuild" => {
            let mut p = SearchPolicies::default();
            p.clause_db.watch_sweep = axeyum_cnf::clause_db_policy::WatchSweep::Rebuild;
            Some(p)
        }
        // Everything as it was before 2026-09.
        "legacy" => Some(SearchPolicies::legacy()),
        // Only the clause database reverted -- isolates the tier change.
        "legacy-db" => Some(SearchPolicies::legacy_clause_db()),
        // Tier database plus the target-mark release, no reinstallation.
        "released-phase" => Some(SearchPolicies::releasing_phase()),
        // Tier database plus the full (B I B O) rephase schedule.
        "scheduled-phase" => Some(SearchPolicies::scheduled_phase()),
        _ => None,
    }
}

fn verdict(outcome: &StreamingProofOutcome) -> &'static str {
    match outcome {
        StreamingProofOutcome::Sat(_) => "sat",
        StreamingProofOutcome::Unsat => "unsat",
        StreamingProofOutcome::ResourceOut => "resource_out",
        StreamingProofOutcome::Interrupted => "interrupted",
        StreamingProofOutcome::SinkFailed(_) => "sink_failed",
    }
}

#[allow(clippy::cast_precision_loss, clippy::too_many_lines)]
fn main() {
    let mut arms = vec!["tiered".to_string(), "legacy".to_string()];
    let mut max_conflicts = 2_000_000usize;
    let mut seconds: Option<u64> = None;
    let mut files: Vec<String> = Vec::new();

    let argv: Vec<String> = std::env::args().skip(1).collect();
    let mut i = 0;
    while i < argv.len() {
        match argv[i].as_str() {
            "--arms" => {
                i += 1;
                arms = argv[i].split(',').map(ToString::to_string).collect();
            }
            "--max-conflicts" => {
                i += 1;
                max_conflicts = argv[i].parse().expect("--max-conflicts takes an integer");
            }
            "--seconds" => {
                i += 1;
                seconds = Some(argv[i].parse().expect("--seconds takes an integer"));
            }
            other => files.push(other.to_string()),
        }
        i += 1;
    }
    assert!(
        !files.is_empty(),
        "usage: clause_db_policy_ab [--arms a,b] [--max-conflicts N] [--seconds S] \
         <file.cnf | bitblast:WIDTHxCOUNT>..."
    );
    for name in &arms {
        assert!(arm(name).is_some(), "unknown arm {name:?}");
    }

    for path in &files {
        let formula = load(path);
        for name in &arms {
            let policies = arm(name).expect("arm was validated above");
            let mut sink = CountingNullSink::default();
            let deadline = seconds.map(|s| Instant::now() + Duration::from_secs(s));
            let started = Instant::now();
            let (outcome, c) = solve_with_drat_proof_counted_with_policies(
                &formula,
                deadline,
                max_conflicts,
                &mut sink,
                &policies,
            );
            let elapsed = started.elapsed().as_secs_f64();
            black_box(&outcome);
            // Every `sat` is replayed against the original formula before it is
            // reported. A measurement tool that prints an unchecked `sat` can
            // manufacture a capability win out of a soundness bug, and the whole
            // point of an A/B is that a policy must not change the verdict --
            // so the verdict is the one thing that gets independently checked.
            if let StreamingProofOutcome::Sat(model) = &outcome {
                assert_eq!(
                    model.satisfies(&formula),
                    Ok(true),
                    "WRONG SAT from arm {name} on {path}: the reported model does \
                     not satisfy the formula"
                );
            }
            emit(path, name, &outcome, c, elapsed, sink.deletions);
        }
    }
}

#[allow(clippy::cast_precision_loss)]
fn emit(
    path: &str,
    arm_name: &str,
    outcome: &StreamingProofOutcome,
    c: SearchCounters,
    seconds: f64,
    deletions: u64,
) {
    let conflicts = c.conflicts.max(1) as f64;
    let recomputes = c.tier_recomputes.max(1) as f64;
    let decided = matches!(
        outcome,
        StreamingProofOutcome::Sat(_) | StreamingProofOutcome::Unsat
    );
    println!(
        "{{\"file\":\"{path}\",\"arm\":\"{arm_name}\",\"verdict\":\"{}\",\
         \"decided\":{decided},\"conflicts\":{},\"seconds\":{seconds:.3},\
         \"decisions\":{},\"propagations\":{},\"restarts\":{},\"reductions\":{},\
         \"proof_deletions\":{deletions},\
         \"reduce_candidates\":{},\"reduce_deleted\":{},\"reduce_empty_rounds\":{},\
         \"reduce_tier1_seen\":{},\"reduce_tier2_seen\":{},\"reduce_tier3_seen\":{},\
         \"reduce_kept_tier1\":{},\"reduce_kept_tier2\":{},\"reduce_locked\":{},\
         \"clause_used_marks\":{},\"clause_promotions\":{},\
         \"tier_recomputes\":{},\"tier1_last\":{},\"tier2_last\":{},\
         \"tier1_mean\":{:.2},\"tier2_mean\":{:.2},\
         \"target_snapshots\":{},\"best_snapshots\":{},\"rephases\":{},\
         \"target_resets\":{},\
         \"watch_visits\":{},\"clause_visits\":{},\"resolutions\":{},\
         \"binary_watch_visits\":{},\"binary_arena_derefs_avoided\":{},\
         \"binary_watch_visit_rate\":{:.3},\
         \"reduce_headers_scanned\":{},\"reduce_headers_skipped\":{},\
         \"reduce_watch_entries_scanned\":{},\
         \"conflicts_per_second\":{:.1},\"props_per_conflict\":{:.1},\
         \"watch_visits_per_conflict\":{:.1},\"clause_deref_rate\":{:.3},\
         \"mean_live_learned\":{:.0},\
         \"used_marks_per_conflict\":{:.2}}}",
        verdict(outcome),
        c.conflicts,
        c.decisions,
        c.propagations,
        c.restarts,
        c.reductions,
        c.reduce_candidates,
        c.reduce_deleted,
        c.reduce_empty_rounds,
        c.reduce_tier1_seen,
        c.reduce_tier2_seen,
        c.reduce_tier3_seen,
        c.reduce_kept_tier1,
        c.reduce_kept_tier2,
        c.reduce_locked,
        c.clause_used_marks,
        c.clause_promotions,
        c.tier_recomputes,
        c.tier1_limit_last,
        c.tier2_limit_last,
        c.tier1_limit_sum as f64 / recomputes,
        c.tier2_limit_sum as f64 / recomputes,
        c.target_phase_snapshots,
        c.best_phase_snapshots,
        c.rephases,
        c.target_phase_resets,
        c.watch_visits,
        c.clause_visits,
        c.resolutions,
        c.binary_watch_visits,
        c.binary_arena_derefs_avoided,
        c.binary_watch_visit_rate(),
        c.reduce_headers_scanned,
        c.reduce_headers_skipped,
        c.reduce_watch_entries_scanned,
        c.conflicts as f64 / seconds.max(1e-9),
        c.propagations as f64 / conflicts,
        c.watch_visits_per_conflict(),
        c.clause_deref_rate(),
        (c.reduce_tier1_seen + c.reduce_tier2_seen + c.reduce_tier3_seen) as f64
            / c.reductions.max(1) as f64,
        c.clause_used_marks as f64 / conflicts,
    );
}
