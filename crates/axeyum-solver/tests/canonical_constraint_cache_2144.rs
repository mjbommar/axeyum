//! ADR-2144: the canonical constraint cache is a library feature of the warm
//! engine, keyed on the sorted, duplicate-elided set of live assertion
//! identities (ADR-0303), OFF as shipped.
//!
//! The two invariants the sizing note pins, each with the test that dies when
//! it is false:
//!
//! 1. **A cached `sat` is served only after its model replays against the
//!    live set.** `a_cached_model_that_no_longer_replays_is_rejected_never_served`
//!    extends the path with an assertion the cached model violates and demands
//!    a fresh, replaying model plus a counted rejection.
//! 2. **A cached `unsat` is served only for a superset of the cached set.**
//!    `unsat_is_never_served_for_a_subset` is the soundness-negative and the
//!    mutation control: with the subset test deleted from the lookup, a
//!    satisfiable query whose largest member matches a cached `unsat` set is
//!    answered `unsat`, and exactly this test dies.
//!
//! The rest: order and duplicates and assumption-vs-stack placement do not
//! change the key; a superset of a cached `unsat` IS served; a model of a
//! subset is reused when it replays; eviction is bounded and deterministic;
//! `unknown` is never cached; the lever ships off; and the corpus identity --
//! cache on and off decide every flat `QF_BV` fixture with the same verdict
//! and, on the first (fresh) check, the same model, while every hit's model
//! replays.
#![cfg(feature = "full")]

use std::path::{Path, PathBuf};
use std::time::Duration;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CanonicalConstraintCachePolicy, CheckResult, DEFAULT_CANONICAL_CACHE, IncrementalBvSolver,
    SolverConfig, check_model,
};

const LEVER: &str = "AXEYUM_CANONICAL_CACHE";

fn require_lever_unset() {
    if let Ok(value) = std::env::var(LEVER) {
        panic!(
            "{LEVER}={value:?} is set; this suite measures the SHIPPED default and must run \
             with the lever unset (`env -u {LEVER}`)"
        );
    }
}

fn cached_solver() -> IncrementalBvSolver {
    let mut solver = IncrementalBvSolver::new();
    solver
        .enable_canonical_constraint_cache(CanonicalConstraintCachePolicy::new(64, 4096, 65_536))
        .unwrap();
    solver
}

fn sat_model(result: CheckResult) -> axeyum_solver::Model {
    match result {
        CheckResult::Sat(model) => model,
        other => panic!("expected sat, got {other:?}"),
    }
}

fn holds(arena: &TermArena, term: TermId, model: &axeyum_solver::Model) -> bool {
    eval(arena, term, &model.to_assignment()) == Ok(Value::Bool(true))
}

/// `x` (8 bits, returned as its symbol) and three constraints interned in
/// the order `a < b < c`: `a: x = 1`, `b: x < 10`, `c: x = 2`.
fn abc() -> (TermArena, SymbolId, TermId, TermId, TermId) {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("cache_x", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_sym);
    let one = arena.bv_const(8, 1).unwrap();
    let ten = arena.bv_const(8, 10).unwrap();
    let two = arena.bv_const(8, 2).unwrap();
    let a = arena.eq(x, one).unwrap();
    let b = arena.bv_ult(x, ten).unwrap();
    let c = arena.eq(x, two).unwrap();
    assert!(
        a < b && b < c,
        "the test relies on interning order a < b < c"
    );
    (arena, x_sym, a, b, c)
}

#[test]
fn the_lever_ships_off_and_the_explicit_config_turns_it_on() {
    require_lever_unset();
    // Read through a binding so the assertion is about the registered
    // default's value rather than a constant predicate clippy folds away.
    let shipped: bool = DEFAULT_CANONICAL_CACHE;
    assert!(
        !shipped,
        "the shipped default must be off -- a moved default is an ADR, not a diff"
    );
    assert!(!SolverConfig::default().canonical_constraint_cache);
    assert!(!IncrementalBvSolver::new().canonical_constraint_cache_enabled());

    let (arena, _, _, b, _) = abc();
    let mut off = IncrementalBvSolver::new();
    off.assert(&arena, b).unwrap();
    assert!(matches!(off.check(&arena).unwrap(), CheckResult::Sat(_)));
    assert!(matches!(off.check(&arena).unwrap(), CheckResult::Sat(_)));
    let stats = off.stats();
    assert_eq!((stats.cache_hits, stats.cache_misses), (0, 0));
    assert_eq!(off.canonical_constraint_cache_stats().insertions, 0);

    let mut on = IncrementalBvSolver::with_config(
        SolverConfig::default().with_canonical_constraint_cache(true),
    );
    assert!(on.canonical_constraint_cache_enabled());
    on.assert(&arena, b).unwrap();
    assert!(matches!(on.check(&arena).unwrap(), CheckResult::Sat(_)));
    assert!(matches!(on.check(&arena).unwrap(), CheckResult::Sat(_)));
    let stats = on.stats();
    assert_eq!((stats.cache_hits, stats.cache_misses), (1, 1));
    let detail = on.canonical_constraint_cache_stats();
    assert_eq!(detail.exact_sat_hits, 1);
    assert_eq!(detail.entries, 1);
}

#[test]
fn zero_bounds_are_refused() {
    let mut solver = IncrementalBvSolver::new();
    // Explicitly off first, so this test is about the bounds and not about
    // the shipped default (which has its own test above).
    solver.disable_canonical_constraint_cache();
    for policy in [
        CanonicalConstraintCachePolicy::new(0, 1, 1),
        CanonicalConstraintCachePolicy::new(1, 0, 1),
        CanonicalConstraintCachePolicy::new(1, 1, 0),
    ] {
        assert!(solver.enable_canonical_constraint_cache(policy).is_err());
        assert!(!solver.canonical_constraint_cache_enabled());
    }
}

#[test]
fn an_exact_set_hits_regardless_of_assertion_order_and_frame_shape() {
    let (arena, x, a, b, _) = abc();
    let mut solver = cached_solver();
    solver.push().unwrap();
    solver.assert(&arena, a).unwrap();
    solver.assert(&arena, b).unwrap();
    let first = sat_model(solver.check(&arena).unwrap());
    assert_eq!(first.get(x), Some(Value::Bv { width: 8, value: 1 }));
    assert!(solver.pop());

    // Reverse order, two frames instead of one: the same canonical set.
    solver.push().unwrap();
    solver.assert(&arena, b).unwrap();
    solver.push().unwrap();
    solver.assert(&arena, a).unwrap();
    let second = sat_model(solver.check(&arena).unwrap());
    assert_eq!(first, second);
    assert!(holds(&arena, a, &second) && holds(&arena, b, &second));
    let stats = solver.canonical_constraint_cache_stats();
    assert_eq!(stats.exact_sat_hits, 1);
    assert_eq!(stats.misses, 1);
    assert_eq!(stats.entries, 1);
}

#[test]
fn a_duplicate_assertion_is_elided_from_the_key() {
    let (arena, _, _, b, _) = abc();
    let mut solver = cached_solver();
    solver.assert(&arena, b).unwrap();
    let first = sat_model(solver.check(&arena).unwrap());
    solver.push().unwrap();
    solver.assert(&arena, b).unwrap();
    solver.assert(&arena, b).unwrap();
    let second = sat_model(solver.check(&arena).unwrap());
    assert_eq!(first, second);
    let stats = solver.canonical_constraint_cache_stats();
    assert_eq!(stats.exact_sat_hits, 1);
    assert_eq!(stats.entries, 1, "{{b}} and {{b, b, b}} are one set");
}

#[test]
fn an_assumption_and_a_stack_assertion_are_the_same_identity() {
    let (arena, _, a, b, _) = abc();
    let mut solver = cached_solver();
    solver.assert(&arena, b).unwrap();
    let first = sat_model(solver.check_assuming(&arena, &[a]).unwrap());
    solver.push().unwrap();
    solver.assert(&arena, a).unwrap();
    let second = sat_model(solver.check(&arena).unwrap());
    assert_eq!(first, second);
    assert!(solver.pop());
    let third = sat_model(solver.check_assuming(&arena, &[a, b, a]).unwrap());
    assert_eq!(first, third);
    let stats = solver.canonical_constraint_cache_stats();
    assert_eq!(stats.exact_sat_hits, 2);
    assert_eq!(stats.entries, 1);
}

/// Invariant 1. The path is extended with an assertion the cached model
/// violates: the cached model is a reuse candidate for the new (superset)
/// live set, it fails replay, the rejection is counted, and the verdict is a
/// FRESH `sat` whose model satisfies every live assertion. Never the stale
/// model, never an error.
#[test]
fn a_cached_model_that_no_longer_replays_is_rejected_never_served() {
    let (mut arena, x, _, b, _) = abc();
    let x_term = arena.var(x);
    let mut solver = cached_solver();
    solver.assert(&arena, b).unwrap();
    let cached = sat_model(solver.check(&arena).unwrap());
    let Some(Value::Bv { value, .. }) = cached.get(x) else {
        panic!("x must be in the model");
    };
    let chosen = arena.bv_const(8, value).unwrap();
    let is_chosen = arena.eq(x_term, chosen).unwrap();
    let not_chosen = arena.not(is_chosen).unwrap();
    assert!(!holds(&arena, not_chosen, &cached));

    solver.push().unwrap();
    solver.assert(&arena, not_chosen).unwrap();
    let fresh = sat_model(solver.check(&arena).unwrap());
    assert!(holds(&arena, b, &fresh) && holds(&arena, not_chosen, &fresh));
    assert_ne!(fresh.get(x), cached.get(x));
    let stats = solver.canonical_constraint_cache_stats();
    assert_eq!(
        stats.replay_rejections, 1,
        "the stale candidate was tried and refused"
    );
    assert_eq!(stats.model_reuse_hits, 0);
    assert_eq!(stats.hits, 0);
    assert_eq!(stats.misses, 2);
    assert_eq!(solver.stats().cache_replay_rejections, 1);
    // The candidate is still a model of ITS set, so it was not dropped.
    assert_eq!(stats.entries, 2);
}

#[test]
fn a_model_of_a_subset_is_reused_when_it_replays() {
    let (mut arena, x, _, b, _) = abc();
    let x_term = arena.var(x);
    let twenty = arena.bv_const(8, 20).unwrap();
    let under_twenty = arena.bv_ult(x_term, twenty).unwrap();
    let mut solver = cached_solver();
    solver.assert(&arena, b).unwrap();
    let cached = sat_model(solver.check(&arena).unwrap());
    solver.push().unwrap();
    solver.assert(&arena, under_twenty).unwrap();
    let reused = sat_model(solver.check(&arena).unwrap());
    assert_eq!(cached, reused);
    assert!(holds(&arena, under_twenty, &reused));
    let stats = solver.canonical_constraint_cache_stats();
    assert_eq!(stats.model_reuse_hits, 1);
    assert_eq!(stats.hits, 1);
    assert_eq!(
        stats.entries, 2,
        "the extended set gained its own exact entry"
    );
    // ... which the next identical check hits exactly.
    let again = sat_model(solver.check(&arena).unwrap());
    assert_eq!(again, reused);
    assert_eq!(solver.canonical_constraint_cache_stats().exact_sat_hits, 1);
}

/// Invariant 2, the served side: a superset of a cached `unsat` set is
/// `unsat` without a solve.
#[test]
fn a_superset_of_a_cached_unsat_set_is_served_unsat() {
    let (arena, _, a, b, c) = abc();
    let mut solver = cached_solver();
    solver.push().unwrap();
    solver.assert(&arena, a).unwrap();
    solver.assert(&arena, c).unwrap();
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Unsat));
    assert!(solver.pop());
    let before = solver.stats();

    solver.push().unwrap();
    solver.assert(&arena, c).unwrap();
    solver.assert(&arena, b).unwrap();
    solver.assert(&arena, a).unwrap();
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Unsat));
    assert!(matches!(
        solver.check_assuming(&arena, &[b]).unwrap(),
        CheckResult::Unsat
    ));
    let stats = solver.canonical_constraint_cache_stats();
    assert_eq!(stats.superset_hits, 1);
    assert_eq!(
        stats.exact_unsat_hits, 1,
        "the second superset check is an exact hit"
    );
    let delta = solver.stats().delta_since(before);
    assert_eq!(delta.cache_superset_hits, 1);
    assert_eq!(delta.cache_hits, 2);
    assert_eq!(delta.cache_misses, 0);
}

/// Invariant 2, the soundness-negative and the MUTATION CONTROL. `{a, c}` is
/// cached `unsat` and its largest member `c` is in the live set `{b, c}`, so a
/// lookup that skips the subset test would answer `unsat` from that entry.
/// `{b, c}` is satisfiable (`x = 2 < 10`) and must be decided `sat`.
#[test]
fn unsat_is_never_served_for_a_subset() {
    let (arena, x, a, b, c) = abc();
    let mut solver = cached_solver();
    solver.push().unwrap();
    solver.assert(&arena, a).unwrap();
    solver.assert(&arena, c).unwrap();
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Unsat));
    assert!(solver.pop());

    solver.push().unwrap();
    solver.assert(&arena, b).unwrap();
    solver.assert(&arena, c).unwrap();
    let model = sat_model(solver.check(&arena).unwrap());
    assert_eq!(model.get(x), Some(Value::Bv { width: 8, value: 2 }));
    assert!(solver.pop());

    // The strict subset `{c}` alone, and `{a}` alone: both satisfiable.
    assert!(matches!(
        solver.check_assuming(&arena, &[c]).unwrap(),
        CheckResult::Sat(_)
    ));
    assert!(matches!(
        solver.check_assuming(&arena, &[a]).unwrap(),
        CheckResult::Sat(_)
    ));
    let stats = solver.canonical_constraint_cache_stats();
    assert_eq!(stats.superset_hits, 0);
    assert_eq!(stats.exact_unsat_hits, 0);
}

#[test]
fn unknown_is_never_cached() {
    let (arena, _, _, b, _) = abc();
    let mut solver = IncrementalBvSolver::with_config(
        SolverConfig::default()
            .with_timeout(Duration::ZERO)
            .with_canonical_constraint_cache(true),
    );
    solver.assert(&arena, b).unwrap();
    for _ in 0..2 {
        let CheckResult::Unknown(_) = solver.check(&arena).unwrap() else {
            panic!("a zero budget is unknown, and unknown is never served from the cache");
        };
    }
    let stats = solver.canonical_constraint_cache_stats();
    assert_eq!(stats.declined_unknown, 2);
    assert_eq!(stats.entries, 0);
    assert_eq!(stats.hits, 0);
    assert_eq!(stats.misses, 2);
}

#[test]
fn eviction_is_bounded_and_deterministic() {
    let (arena, _, a, b, c) = abc();
    let mut solver = IncrementalBvSolver::new();
    solver
        .enable_canonical_constraint_cache(CanonicalConstraintCachePolicy::new(2, 64, 512))
        .unwrap();
    for set in [&[a][..], &[b], &[c]] {
        assert!(matches!(
            solver.check_assuming(&arena, set).unwrap(),
            CheckResult::Sat(_)
        ));
    }
    let stats = solver.canonical_constraint_cache_stats();
    assert_eq!(stats.entries, 2);
    assert_eq!(stats.evictions, 1);
    // `{a}` was the least recently used and is gone; `{b}` and `{c}` remain.
    assert!(matches!(
        solver.check_assuming(&arena, &[b]).unwrap(),
        CheckResult::Sat(_)
    ));
    assert!(matches!(
        solver.check_assuming(&arena, &[c]).unwrap(),
        CheckResult::Sat(_)
    ));
    assert_eq!(solver.canonical_constraint_cache_stats().exact_sat_hits, 2);
    assert!(matches!(
        solver.check_assuming(&arena, &[a]).unwrap(),
        CheckResult::Sat(_)
    ));
    let stats = solver.canonical_constraint_cache_stats();
    assert_eq!(stats.misses, 4);
    assert_eq!(stats.evictions, 2);
    assert_eq!(stats.entries, 2);
}

#[test]
fn deferred_theory_assumptions_bypass_the_cache_and_still_refuse() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("cache_uf_x", 8).unwrap();
    let f = arena
        .declare_fun("cache_uf_f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let uf = arena.eq(fx, x).unwrap();
    let mut solver = cached_solver();
    assert!(solver.check_assuming(&arena, &[uf]).is_err());
    let stats = solver.canonical_constraint_cache_stats();
    assert_eq!((stats.hits, stats.misses, stats.entries), (0, 0, 0));
}

// --------------------------------------------------------------------------
// The corpus identity.
// --------------------------------------------------------------------------

const BUDGET: Duration = Duration::from_secs(5);

fn corpus_dirs() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    ["regression/qf_bv", "regression/cvc5/qf_bv", "micro"]
        .iter()
        .map(|d| root.join(d))
        .collect()
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect(&path, out);
        } else if path.extension().is_some_and(|e| e == "smt2") {
            out.push(path);
        }
    }
}

/// Every committed flat `QF_BV` fixture, derived from the corpus directories
/// so a fixture added tomorrow is compared tomorrow.
fn qf_bv_fixtures() -> Vec<(String, String)> {
    let mut files = Vec::new();
    for dir in corpus_dirs() {
        collect(&dir, &mut files);
    }
    let mut out = Vec::new();
    for path in files {
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        if !text.contains("(set-logic QF_BV)") {
            continue;
        }
        if ["(push", "(pop", "reset-assertions", "(reset"]
            .iter()
            .any(|kw| text.contains(kw))
        {
            continue;
        }
        out.push((path.display().to_string(), text));
    }
    assert!(
        out.len() >= 30,
        "expected the committed QF_BV corpora to hold >= 30 flat fixtures, found {}",
        out.len()
    );
    out
}

fn verdict(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

/// One fixture's sequence: assert everything, check, check again under an
/// empty frame, pop, check again. `None` when the warm path refuses an
/// assertion (a coverage gap, not a cache finding).
fn drive(
    arena: &TermArena,
    assertions: &[TermId],
    cache: bool,
) -> Option<(IncrementalBvSolver, [CheckResult; 3])> {
    let mut solver = IncrementalBvSolver::with_config(
        SolverConfig::default()
            .with_timeout(BUDGET)
            .with_canonical_constraint_cache(cache),
    );
    for &term in assertions {
        solver.assert(arena, term).ok()?;
    }
    let first = solver.check(arena).ok()?;
    solver.push().ok()?;
    let second = solver.check(arena).ok()?;
    assert!(solver.pop());
    let third = solver.check(arena).ok()?;
    Some((solver, [first, second, third]))
}

/// Cache on and cache off return the same verdict at every step of every
/// fixture and the same model on the fresh first check; every model served
/// on a hit replays against the fixture's assertions. The counts are printed
/// so a run that compared nothing is visible, and the hit count must be
/// nonzero so the "on" arm demonstrably took the cache path.
#[test]
fn cache_on_and_off_agree_on_every_flat_qf_bv_fixture() {
    require_lever_unset();
    let mut compared = 0usize;
    let mut sat = 0usize;
    let mut hits = 0u64;
    let mut skipped = 0usize;
    for (name, text) in qf_bv_fixtures() {
        let Ok(script) = parse_script(&text) else {
            skipped += 1;
            continue;
        };
        let Some((_, off)) = drive(&script.arena, &script.assertions, false) else {
            skipped += 1;
            continue;
        };
        let (on_solver, on) = drive(&script.arena, &script.assertions, true)
            .unwrap_or_else(|| panic!("{name}: the cache-on arm refused what cache-off accepted"));
        for (step, (off, on)) in off.iter().zip(on.iter()).enumerate() {
            assert_eq!(
                verdict(off),
                verdict(on),
                "{name}: step {step} verdict differs between cache off and on"
            );
        }
        if let (CheckResult::Sat(off_model), CheckResult::Sat(on_model)) = (&off[0], &on[0]) {
            assert_eq!(off_model, on_model, "{name}: the fresh first models differ");
            sat += 1;
            for served in &on[1..] {
                let CheckResult::Sat(model) = served else {
                    unreachable!("verdicts agreed above");
                };
                assert!(
                    check_model(&script.arena, &script.assertions, model).unwrap_or(false),
                    "{name}: a model served from the cache does not replay"
                );
            }
        }
        hits += on_solver.stats().cache_hits;
        compared += 1;
    }
    println!(
        "canonical_constraint_cache_2144: identity compared={compared} sat={sat} \
         cache_hits={hits} skipped={skipped}"
    );
    assert!(
        sat >= 5,
        "only {sat} sat fixtures -- the identity compared too few models"
    );
    assert!(
        hits >= 2 * (sat as u64),
        "cache_hits={hits} for {sat} sat fixtures -- the on arm did not take the cache path"
    );
}
