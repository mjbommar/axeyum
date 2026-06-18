//! Differential soundness net for the `QF_BV` decision backends (DISAGREE=0).
//!
//! Two agents concurrently mutate the solver and a brand-new `LazyBvBackend`
//! (CEGAR abstraction-refinement) just landed; the project's load-bearing
//! invariant is **never a wrong `sat`/`unsat`**. This harness generates seeded
//! random well-typed `QF_BV` formulas (small width so both the eager mountain
//! builder and the lazy refiner decide in milliseconds) and cross-checks every
//! pair of concrete decisions:
//!
//! - **No disagreement:** if two backends both decide concretely, they agree.
//!   `unknown` is first-class (an admitted miss), never a disagreement.
//! - **Every `sat` replays:** each `sat` model, lifted independently here via
//!   `Model::to_assignment` + the ground evaluator, must satisfy *every original
//!   assertion* — catching a bad model lift or reconstruction even when the
//!   verdict matches.
//!
//! Backends compared: the eager `SatBvBackend` (default), the lazy
//! `LazyBvBackend` (the new path under test), and — when the `z3` feature is on
//! — the `Z3Backend` oracle. Deterministic (fixed seeds, no clock/RNG service);
//! a small batch is always-on, a larger batch is `#[ignore]`.

use std::time::Duration;

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, LazyBvBackend, PblsBackend, SatBvBackend, SolverBackend, SolverConfig,
};

const WIDTH: u32 = 4;

/// Deterministic xorshift PRNG (no clock / RNG service); matches the idiom in
/// `euf_egraph_diff.rs`.
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

fn cfg() -> SolverConfig {
    SolverConfig::default().with_timeout(Duration::from_secs(5))
}

/// A `(name, decision)` pair from one backend run on the shared arena.
struct Run {
    name: &'static str,
    result: CheckResult,
}

/// Builds a random well-typed `QF_BV` conjunction over `WIDTH`-bit terms: a pool
/// of variables grown by random unary/binary BV operators (including `bvmul`,
/// the heavy op the lazy path abstracts, and the total `bvudiv`/`bvurem`), then
/// a conjunction of clauses, each a small disjunction of (dis)equality and
/// unsigned/signed comparison literals.
fn random_formula(state: &mut u64, arena: &mut TermArena) -> Vec<TermId> {
    let sort = Sort::BitVec(WIDTH);
    let n_vars = 2 + pick(state, 3); // 2..=4
    let mut terms: Vec<TermId> = (0..n_vars)
        .map(|i| {
            let sym = arena.declare(&format!("v{i}"), sort).unwrap();
            arena.var(sym)
        })
        .collect();

    // Grow the term pool with a few derived operator nodes.
    for _ in 0..4 {
        let a = terms[pick(state, terms.len())];
        let term = match xorshift(state) % 11 {
            0 => arena.bv_add(a, terms[pick(state, terms.len())]).unwrap(),
            1 => arena.bv_sub(a, terms[pick(state, terms.len())]).unwrap(),
            2 => arena.bv_mul(a, terms[pick(state, terms.len())]).unwrap(),
            3 => arena.bv_and(a, terms[pick(state, terms.len())]).unwrap(),
            4 => arena.bv_or(a, terms[pick(state, terms.len())]).unwrap(),
            5 => arena.bv_xor(a, terms[pick(state, terms.len())]).unwrap(),
            6 => arena.bv_shl(a, terms[pick(state, terms.len())]).unwrap(),
            7 => arena.bv_lshr(a, terms[pick(state, terms.len())]).unwrap(),
            8 => arena.bv_udiv(a, terms[pick(state, terms.len())]).unwrap(),
            9 => arena.bv_urem(a, terms[pick(state, terms.len())]).unwrap(),
            _ => arena.bv_neg(a).unwrap(),
        };
        terms.push(term);
    }

    let n_clauses = 2 + pick(state, 4); // 2..=5
    let mut assertions = Vec::with_capacity(n_clauses);
    for _ in 0..n_clauses {
        let lits = 1 + pick(state, 2); // 1..=2 literals per clause
        let mut clause: Option<TermId> = None;
        for _ in 0..lits {
            let s = terms[pick(state, terms.len())];
            let t = terms[pick(state, terms.len())];
            let atom = match xorshift(state) % 5 {
                0 => arena.eq(s, t).unwrap(),
                1 => arena.bv_ult(s, t).unwrap(),
                2 => arena.bv_ule(s, t).unwrap(),
                3 => arena.bv_slt(s, t).unwrap(),
                _ => arena.bv_sle(s, t).unwrap(),
            };
            let lit = if xorshift(state) & 1 == 0 {
                atom
            } else {
                arena.not(atom).unwrap()
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

/// Independently re-checks that a `sat` model satisfies every original
/// assertion (a bad lift/reconstruction is caught here even when the verdict
/// matches the other backends).
fn assert_model_replays(
    arena: &TermArena,
    assertions: &[TermId],
    assignment: &Assignment,
    who: &str,
) {
    for &term in assertions {
        assert_eq!(
            eval(arena, term, assignment).unwrap(),
            Value::Bool(true),
            "{who}: sat model must satisfy every original assertion"
        );
    }
}

/// Cross-checks all backend runs on one formula: pairwise no-disagreement +
/// per-`sat` independent model replay.
fn assert_consistent(arena: &TermArena, assertions: &[TermId], runs: &[Run], seed: u64) {
    for r in runs {
        if let CheckResult::Sat(model) = &r.result {
            assert_model_replays(arena, assertions, &model.to_assignment(), r.name);
        }
    }
    for (i, a) in runs.iter().enumerate() {
        for b in &runs[i + 1..] {
            let disagree = matches!(
                (&a.result, &b.result),
                (CheckResult::Sat(_), CheckResult::Unsat)
                    | (CheckResult::Unsat, CheckResult::Sat(_))
            );
            assert!(
                !disagree,
                "DISAGREE (seed {seed}): {} says {:?} but {} says {:?}",
                a.name,
                verdict(&a.result),
                b.name,
                verdict(&b.result)
            );
        }
    }
}

fn verdict(r: &CheckResult) -> &'static str {
    match r {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

/// Runs the eager + lazy + local-search backends (and Z3 when the feature is on)
/// on the shared arena. The pure-Rust backends take `&TermArena`, so one build
/// serves all. PBLS is one-sided (`Sat`/`Unknown`, never `Unsat`), so it can only
/// add `Sat` verdicts the harness then replays and cross-checks against the
/// complete backends.
fn run_backends(arena: &TermArena, assertions: &[TermId], include_pbls: bool) -> Vec<Run> {
    let config = cfg();
    let mut runs = vec![
        Run {
            name: "eager",
            result: SatBvBackend::new()
                .check(arena, assertions, &config)
                .expect("eager backend invocation succeeds"),
        },
        Run {
            name: "lazy",
            result: LazyBvBackend::new()
                .check(arena, assertions, &config)
                .expect("lazy backend invocation succeeds"),
        },
    ];
    if include_pbls {
        // Local search burns its whole budget on the unsatisfiable instances it
        // cannot refute, so cap it tightly — it only ever contributes `Sat`
        // verdicts (replayed + cross-checked) or `Unknown` (no disagreement).
        let pbls_config = SolverConfig::default().with_timeout(Duration::from_millis(100));
        runs.push(Run {
            name: "pbls",
            result: PblsBackend::new()
                .check(arena, assertions, &pbls_config)
                .expect("local-search backend invocation succeeds"),
        });
    }
    #[cfg(feature = "z3")]
    runs.push(Run {
        name: "z3",
        result: axeyum_solver::Z3Backend::new()
            .check(arena, assertions, &config)
            .expect("z3 backend invocation succeeds"),
    });
    runs
}

fn run_batch(seed: u64, n: usize, include_pbls: bool) {
    let mut state = seed;
    let mut decided = 0usize;
    for _ in 0..n {
        // Snapshot the seed for this instance so a failure is reproducible.
        let instance_seed = state;
        let mut arena = TermArena::new();
        let assertions = random_formula(&mut state, &mut arena);
        let runs = run_backends(&arena, &assertions, include_pbls);
        if runs
            .iter()
            .any(|r| !matches!(r.result, CheckResult::Unknown(_)))
        {
            decided += 1;
        }
        assert_consistent(&arena, &assertions, &runs, instance_seed);
    }
    // Sanity: the small-width generator should decide the vast majority; a
    // collapse to all-unknown would silently void the net.
    assert!(
        decided * 5 >= n * 4,
        "expected ≥80% decided, got {decided}/{n} (net would be vacuous)"
    );
}

#[test]
fn eager_and_lazy_agree_on_random_qfbv_small_batch() {
    // Always-on: the complete backends only, so it stays fast.
    run_batch(0x5EED_0BAD_1234_9F01, 200, false);
}

#[test]
#[ignore = "larger soundness sweep (incl. local search); run with --ignored"]
fn eager_lazy_pbls_agree_on_random_qfbv_large_batch() {
    // Three independent seeds, 1500 total, with the local-search engine included
    // so its one-sided `Sat` verdicts are replayed and cross-checked at scale.
    run_batch(0xA11C_E5DE_FEC8_ED01_u64, 500, true);
    run_batch(0x0FF1_CEC0_FFEE_9931_u64, 500, true);
    run_batch(0xDEAD_BEEF_FEED_5AFE, 500, true);
}
