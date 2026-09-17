//! Differential and unit tests for the online (incremental, backtrackable)
//! `QF_LIA` theory solver ([`axeyum_solver::LiaTheory`] /
//! [`axeyum_solver::check_qf_lia_online`]).
//!
//! The load-bearing test is the differential fuzz: a deterministic LCG (no
//! `rand`, no clock) drives random `QF_LIA` conjunctions AND random
//! `push`/`pop`/`assert` sequences, and the online verdict (sat/unsat) must AGREE
//! with the trusted offline [`axeyum_solver::check_with_lia_simplex`] on EVERY
//! instance — zero disagreements. Every `sat` model is replayed against the
//! original atoms with **integer** values (the trust anchor for `sat`); every
//! `unsat` conflict core is itself `check_with_lia_simplex`-`unsat`. A
//! disagreement is a hard failure (a wrong sat/unsat is unacceptable; a graceful
//! `Unknown` is fine and never counts as a disagreement).
#![cfg(feature = "full")]

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, LiaTheory, Model, SolverConfig, TheorySolver, check_qf_lia_online,
    check_with_lia_simplex,
};

/// A tiny deterministic LCG (Numerical Recipes constants) — reproducible, no
/// `rand`, no clock.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        // The raw state is never handed out: bit `k` of an LCG modulo 2^64
        // has period 2^(k+1), so `state & 1` alternates on every draw and a
        // decision made at a fixed draw offset is a constant, not a coin.
        // Measured 2026-09-16 (lane ax-proptest, bench-results/proptest-box-
        // audit-20260916): `below(4)` advanced by +3 mod 4 per draw, so the
        // push/pop/assert schedule never drew an explicit pop at depth > 0
        // (0 of 7200 steps) and depth climbed monotonically to 24.
        // SplitMix64's finalizer makes every output bit depend on the state.
        let z = (self.0 ^ (self.0 >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        let z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }

    /// A small signed integer coefficient/constant in `[-range, range]`.
    fn small(&mut self, range: i128) -> i128 {
        let span = u64::try_from(2 * range + 1).expect("range fits u64");
        i128::from(self.below(span)) - range
    }
}

/// Builds a random linear-integer atom over the given variables and returns its
/// `TermId`. Shape: `Σ cᵢ·xᵢ  <rel>  k`, with a random relation and small
/// coefficients/constant — including divisibility-flavored cases via `2*x`-shaped
/// coefficients.
fn random_atom(arena: &mut TermArena, vars: &[TermId], rng: &mut Lcg) -> TermId {
    // Left-hand side: a small linear combination of the variables.
    let mut lhs: Option<TermId> = None;
    for &v in vars {
        let coeff = rng.small(3);
        if coeff == 0 {
            continue;
        }
        let c = arena.int_const(coeff);
        let term = arena.int_mul(c, v).expect("int mul");
        lhs = Some(match lhs {
            None => term,
            Some(acc) => arena.int_add(acc, term).expect("int add"),
        });
    }
    let lhs = lhs.unwrap_or_else(|| arena.int_const(0));
    let k = arena.int_const(rng.small(4));
    match rng.below(5) {
        0 => arena.int_lt(lhs, k).expect("int lt"),
        1 => arena.int_le(lhs, k).expect("int le"),
        2 => arena.int_gt(lhs, k).expect("int gt"),
        3 => arena.int_ge(lhs, k).expect("int ge"),
        _ => arena.eq(lhs, k).expect("int eq"),
    }
}

/// Builds a random linear-integer **order** atom (`<,<=,>,>=`, never equality) —
/// every such atom has a representable single-constraint negation, the precondition
/// the theory-propagation gate needs. Same `Σ cᵢ·xᵢ <rel> k` shape as
/// [`random_atom`] but with the relation drawn only from the four order relations.
fn random_order_atom(arena: &mut TermArena, vars: &[TermId], rng: &mut Lcg) -> TermId {
    let mut lhs: Option<TermId> = None;
    for &v in vars {
        let coeff = rng.small(3);
        if coeff == 0 {
            continue;
        }
        let c = arena.int_const(coeff);
        let term = arena.int_mul(c, v).expect("int mul");
        lhs = Some(match lhs {
            None => term,
            Some(acc) => arena.int_add(acc, term).expect("int add"),
        });
    }
    let lhs = lhs.unwrap_or_else(|| arena.int_const(0));
    let k = arena.int_const(rng.small(4));
    match rng.below(4) {
        0 => arena.int_lt(lhs, k).expect("int lt"),
        1 => arena.int_le(lhs, k).expect("int le"),
        2 => arena.int_gt(lhs, k).expect("int gt"),
        _ => arena.int_ge(lhs, k).expect("int ge"),
    }
}

/// Replays a `sat` model against `assertions` requiring **integer** values; panics
/// on any non-integer value or any assertion not satisfied.
fn assert_integer_model(arena: &TermArena, assertions: &[TermId], model: &Model) {
    let mut assignment = Assignment::new();
    for (symbol, value) in model.iter() {
        assert!(
            matches!(value, Value::Int(_)),
            "online LIA sat model must assign integer values, got {value:?}"
        );
        assignment.set(symbol, value);
    }
    for &a in assertions {
        assert_eq!(
            eval(arena, a, &assignment).ok(),
            Some(Value::Bool(true)),
            "online LIA sat model must satisfy every original assertion"
        );
    }
}

#[test]
fn strict_tightening_unsat_core_is_offline_unsat() {
    // 0 < x  and  x < 1: integer-UNSAT though rationally SAT — the LIA point.
    let mut arena = TermArena::new();
    let s = arena.declare("x", Sort::Int).expect("declare");
    let x = arena.var(s);
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let gt = arena.int_gt(x, zero).expect("x>0");
    let lt = arena.int_lt(x, one).expect("x<1");

    let mut theory = LiaTheory::new(&arena, &[gt, lt]);
    assert!(theory.assert(0, true).is_ok());
    let core = theory.assert(1, true).expect_err("integer-infeasible");
    assert!(!core.is_empty());
    let core_terms: Vec<TermId> = core
        .iter()
        .map(|l| if l.atom == 0 { gt } else { lt })
        .collect();
    assert_eq!(
        check_with_lia_simplex(&arena, &core_terms).expect("decidable"),
        CheckResult::Unsat,
        "the strict-tightening conflict core must be offline-unsat"
    );
}

#[test]
fn push_assert_pop_restores_feasibility() {
    let mut arena = TermArena::new();
    let s = arena.declare("x", Sort::Int).expect("declare");
    let x = arena.var(s);
    let zero = arena.int_const(0);
    let neg1 = arena.int_const(-1);
    let ge = arena.int_ge(x, zero).expect("x>=0");
    let le = arena.int_le(x, neg1).expect("x<=-1");

    let mut theory = LiaTheory::new(&arena, &[ge, le]);
    assert!(theory.assert(0, true).is_ok());
    theory.push();
    assert!(theory.assert(1, true).is_err(), "x>=0 ∧ x<=-1 infeasible");
    theory.pop();
    theory.push();
    assert!(theory.assert(1, false).is_ok(), "x>=0 ∧ ¬(x<=-1) feasible");
}

/// ADR-2143, the soundness-negative sequence from the ax-proptest audit
/// (`bench-results/proptest-box-audit-20260916/README.md`, seed 9 of the
/// push/pop fuzz):
///
/// ```text
/// push; assert(x ≥ 10)      -> Ok
/// push; assert(¬(x ≥ 10))   -> MUST be a conflict (was: Ok, silent overwrite)
/// pop                       -> MUST leave x ≥ 10 live (was: atom set to None)
/// assert(x ≤ 0)             -> MUST be a conflict (was: Ok — a wrong `sat`)
/// ```
///
/// Every step is asserted on its own so a mutation of the conflict check and a
/// mutation of the pop restore die at different lines.
#[test]
fn opposite_polarity_reassert_conflicts_and_pop_keeps_the_outer_assignment() {
    let mut arena = TermArena::new();
    let s = arena.declare("x", Sort::Int).expect("declare");
    let x = arena.var(s);
    let ten = arena.int_const(10);
    let zero = arena.int_const(0);
    let ge10 = arena.int_ge(x, ten).expect("x>=10");
    let le0 = arena.int_le(x, zero).expect("x<=0");

    let mut theory = LiaTheory::new(&arena, &[ge10, le0]);
    theory.push();
    assert!(theory.assert(0, true).is_ok(), "x>=10 alone is feasible");
    theory.push();
    let core = theory
        .assert(0, false)
        .expect_err("¬(x>=10) while x>=10 is live at the enclosing level is a conflict");
    assert!(
        core.contains(&axeyum_solver::TheoryLit {
            atom: 0,
            value: false
        }) && core.contains(&axeyum_solver::TheoryLit {
            atom: 0,
            value: true
        }),
        "the core names both polarities of the atom: {core:?}"
    );
    // Driver discipline: backtrack past the conflicting assertion.
    theory.pop();
    // The outer x>=10 must still be live: x<=0 conflicts with it.
    assert!(
        theory.assert(1, true).is_err(),
        "x<=0 must conflict with the still-live x>=10 (the audit's wrong-sat step)"
    );
    // And idempotence still holds for the live polarity.
    assert!(
        theory.assert(0, true).is_ok(),
        "re-assert at the live polarity is a no-op"
    );
    // Popping the outer level frees the atom entirely.
    theory.pop();
    assert!(
        theory.assert(0, false).is_ok(),
        "after the outer pop ¬(x>=10) is feasible"
    );
    assert!(theory.assert(1, true).is_ok(), "and x<=0 with it");
}

#[test]
fn non_lia_atom_declines_gracefully() {
    // A BV equality atom is a no-op; asserting it never panics or conflicts.
    let mut arena = TermArena::new();
    let bv = arena.declare("b", Sort::BitVec(8)).expect("declare bv");
    let v = arena.var(bv);
    let k = arena.bv_const(8, 5).expect("bv const");
    let eq = arena.eq(v, k).expect("bv eq");

    let mut theory = LiaTheory::new(&arena, &[eq]);
    assert!(!theory.tracks(0));
    theory.push();
    assert!(theory.assert(0, true).is_ok());
    // ADR-2143: the two polarities are separated by a `pop` — even an
    // untracked atom is an ASSERTION, and `a ∧ ¬a` at one level is a
    // conflict, pinned by `opposite_polarity_reassert_conflicts_and_pop_keeps_the_outer_assignment`
    // rather than here (one guard, one test).
    theory.pop();
    assert!(
        theory.assert(0, false).is_ok(),
        "after the pop either polarity is a no-op"
    );
}

/// The load-bearing differential fuzz over random conjunctions: the online
/// `check_qf_lia_online` must agree with the offline `check_with_lia_simplex` on
/// every instance (sat/unsat), every sat model replays with integer values, and
/// the run exercises both sat and unsat. Zero disagreements.
#[test]
fn differential_fuzz_conjunctions_agree_with_offline() {
    let mut sat_count = 0_u32;
    let mut unsat_count = 0_u32;
    let mut decided = 0_u32;

    for seed in 0..400_u64 {
        let mut rng = Lcg::new(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1));
        let mut arena = TermArena::new();
        let nvars = 1 + usize::try_from(rng.below(3)).expect("fits"); // 1..=3 vars
        let vars: Vec<TermId> = (0..nvars)
            .map(|i| {
                let s = arena
                    .declare(&format!("x{i}"), Sort::Int)
                    .expect("declare int");
                arena.var(s)
            })
            .collect();

        let natoms = 2 + usize::try_from(rng.below(4)).expect("fits"); // 2..=5 atoms
        let assertions: Vec<TermId> = (0..natoms)
            .map(|_| random_atom(&mut arena, &vars, &mut rng))
            .collect();

        let offline = check_with_lia_simplex(&arena, &assertions).expect("offline decidable");
        let online = check_qf_lia_online(&arena, &assertions, &SolverConfig::default())
            .expect("online decidable");

        match (&offline, &online) {
            (CheckResult::Sat(_), CheckResult::Sat(model)) => {
                assert_integer_model(&arena, &assertions, model);
                sat_count += 1;
                decided += 1;
            }
            (CheckResult::Unsat, CheckResult::Unsat) => {
                unsat_count += 1;
                decided += 1;
            }
            // One side `Unknown` is a graceful decline, never a disagreement.
            (CheckResult::Unknown(_), _) | (_, CheckResult::Unknown(_)) => {}
            (a, b) => panic!(
                "DISAGREEMENT on seed {seed}: offline={a:?} online={b:?} \
                 (a wrong sat/unsat is unacceptable)"
            ),
        }
    }

    eprintln!("COVERAGE conjunctions: sat={sat_count} unsat={unsat_count} decided={decided}");
    assert!(decided > 0, "fuzz must decide at least some instances");
    assert!(sat_count > 0, "fuzz must cover at least one sat case");
    assert!(unsat_count > 0, "fuzz must cover at least one unsat case");
}

/// Fuzz random `push`/`pop`/`assert` sequences against a [`LiaTheory`], and at
/// each step confirm that "the theory currently reports a conflict" agrees with
/// "deciding the currently-asserted live atom set offline is unsat". Zero
/// disagreements; covers both feasible and infeasible states.
/// One step of the push/pop/assert schedule fuzzed by
/// [`differential_fuzz_push_pop_assert_sequences_agree`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScheduleStep {
    Push,
    /// An explicit pop (only drawn while `depth > 0`).
    Pop,
    Assert {
        atom: usize,
        value: bool,
    },
}

/// Seeds, per-seed shape draws and the step schedule shared by the push/pop
/// fuzz and its coverage guard.
const SCHEDULE_SEEDS: u64 = 300;
const SCHEDULE_STEPS: usize = 24;

fn schedule_rng(seed: u64) -> Lcg {
    Lcg::new(seed.wrapping_mul(0xD1B5_4A32_D192_ED03).wrapping_add(7))
}

/// Draws the next schedule step: `below(4)` picks push (0), pop (1, but only
/// while `depth > 0`; at depth 0 the draw falls through to an assert) or an
/// assert of a random atom with a random polarity (2, 3 and the fallthrough).
fn draw_schedule_step(rng: &mut Lcg, natoms: usize, depth: u32) -> ScheduleStep {
    match rng.below(4) {
        0 => ScheduleStep::Push,
        1 if depth > 0 => ScheduleStep::Pop,
        _ => {
            let atom = usize::try_from(rng.below(natoms as u64)).expect("fits");
            let value = rng.below(2) == 1;
            ScheduleStep::Assert { atom, value }
        }
    }
}

#[test]
fn differential_fuzz_push_pop_assert_sequences_agree() {
    let mut conflict_steps = 0_u32;
    let mut clean_steps = 0_u32;
    let mut explicit_pops = 0_u32;
    let mut polarity_conflicts = 0_u32;

    for seed in 0..SCHEDULE_SEEDS {
        let mut rng = schedule_rng(seed);
        let mut arena = TermArena::new();
        let nvars = 1 + usize::try_from(rng.below(2)).expect("fits"); // 1..=2 vars
        let vars: Vec<TermId> = (0..nvars)
            .map(|i| {
                let s = arena
                    .declare(&format!("y{i}"), Sort::Int)
                    .expect("declare int");
                arena.var(s)
            })
            .collect();

        let natoms = 3 + usize::try_from(rng.below(4)).expect("fits"); // 3..=6 atoms
        let atoms: Vec<TermId> = (0..natoms)
            .map(|_| random_atom(&mut arena, &vars, &mut rng))
            .collect();

        let mut theory = LiaTheory::new(&arena, &atoms);
        // Mirror the theory's own state exactly: an append-only assignment LOG
        // (`(atom, value)` in assert order, matching `assigned_log`) plus markers
        // storing the log length at each `push`. The effective per-atom value is
        // the LATEST log entry — so a backtrack is a plain `truncate`, never a
        // reorder (the bug a "retain+push" mirror would introduce).
        let mut log: Vec<(usize, bool)> = Vec::new();
        let mut marks: Vec<usize> = Vec::new();
        let mut depth = 0_u32;

        for _ in 0..SCHEDULE_STEPS {
            match draw_schedule_step(&mut rng, natoms, depth) {
                // push
                ScheduleStep::Push => {
                    theory.push();
                    marks.push(log.len());
                    depth += 1;
                }
                // pop (only drawn while we have a mark)
                ScheduleStep::Pop => {
                    theory.pop();
                    let mark = marks.pop().expect("depth>0 has a mark");
                    log.truncate(mark);
                    depth -= 1;
                    explicit_pops += 1;
                }
                // assert (default and the pop-with-no-mark fallthrough). Each
                // assertion is wrapped in its own `push`, and on a reported
                // conflict we `pop` to undo it — faithfully mirroring how a
                // CDCL(T) driver backtracks past a theory conflict so the theory
                // and the mirror stay in a consistent state after every step.
                ScheduleStep::Assert { atom, value } => {
                    theory.push();
                    marks.push(log.len());
                    depth += 1;

                    let result = theory.assert(atom, value);
                    let current = effective(&log, atom);
                    // A conflict core is a lemma `¬⋀core`, so every literal it
                    // names must be ASSERTED at that polarity: the mirrored live
                    // value, or the trigger literal itself. A core naming the
                    // other polarity is a false lemma — the shape a stale
                    // marker produces (ADR-2143, `rows_to_core`'s
                    // `unwrap_or(true)`).
                    if let Err(core) = &result {
                        for lit in core {
                            let asserted = effective(&log, lit.atom) == Some(lit.value)
                                || (lit.atom == atom && lit.value == value);
                            assert!(
                                asserted,
                                "DISAGREEMENT seed {seed}: core literal {lit:?} is not asserted \
                                 (live={:?}, trigger=({atom}, {value}))",
                                effective_set(&log, natoms)
                            );
                        }
                    }
                    // ADR-2143: an atom whose OPPOSITE polarity is live at this
                    // or an enclosing level is a conflict — `a ∧ ¬a` — and the
                    // theory must say so without touching its state. Until the
                    // repair it overwrote the value in place and logged only the
                    // index, so the `pop` below dropped the OUTER assignment
                    // (seed 9: `x ≥ 10` vanished and `x ≤ 0` was then accepted).
                    // The mirror records nothing for the rejected step; the
                    // driver-discipline pop below undoes the wrapping push.
                    if current == Some(!value) {
                        assert!(
                            result.is_err(),
                            "DISAGREEMENT seed {seed}: atom {atom} is live at {current:?} and \
                             the theory accepted its negation (live={:?})",
                            effective_set(&log, natoms)
                        );
                        polarity_conflicts += 1;
                        theory.pop();
                        let mark = marks.pop().expect("just pushed a mark");
                        log.truncate(mark);
                        depth -= 1;
                        continue;
                    }
                    // The theory logs a (possibly-changed) assignment only when the
                    // value differs from the current effective one (idempotence).
                    if current != Some(value) {
                        log.push((atom, value));
                    }

                    // The offline verdict for the current effective constraint set
                    // (built in its own arena so polarity `not` terms resolve).
                    let live = effective_set(&log, natoms);
                    let (live_arena, live_terms) = live_query(&arena, &atoms, &live);
                    let offline = if live_terms.is_empty() {
                        CheckResult::Sat(Model::new())
                    } else {
                        check_with_lia_simplex(&live_arena, &live_terms).expect("offline decidable")
                    };

                    match (result.is_err(), &offline) {
                        (true, CheckResult::Unsat) => conflict_steps += 1,
                        (false, CheckResult::Sat(_)) => clean_steps += 1,
                        // The theory only ever reports a conflict via the offline
                        // decider, and only when the live set is offline-unsat. The
                        // forbidden combinations are a reported conflict on a
                        // non-`unsat` live set, or no conflict on an `unsat` set.
                        (true, CheckResult::Sat(_)) => panic!(
                            "DISAGREEMENT seed {seed}: theory reported a conflict but the \
                             live set is offline-SAT (live={live:?})"
                        ),
                        (false, CheckResult::Unsat) => panic!(
                            "DISAGREEMENT seed {seed}: theory reported no conflict but the \
                             live set is offline-UNSAT (live={live:?})"
                        ),
                        // offline `Unknown` on either branch: graceful, no claim.
                        (_, CheckResult::Unknown(_)) => {}
                    }

                    // On a conflict, backtrack past this assertion (driver
                    // discipline) so the next step starts from a consistent state.
                    if result.is_err() {
                        theory.pop();
                        let mark = marks.pop().expect("just pushed a mark");
                        log.truncate(mark);
                        depth -= 1;
                    }
                }
            }
        }
    }

    eprintln!(
        "COVERAGE push/pop/assert: conflict_steps={conflict_steps} clean_steps={clean_steps} \
         explicit_pops={explicit_pops} polarity_conflicts={polarity_conflicts}"
    );
    assert!(
        conflict_steps > 0,
        "push/pop/assert fuzz must reach at least one conflict state"
    );
    assert!(
        polarity_conflicts > 0,
        "push/pop/assert fuzz must re-assert a live atom at the opposite polarity \
         (the ADR-2143 shape) at least once"
    );
    assert!(
        clean_steps > 0,
        "push/pop/assert fuzz must reach at least one feasible state"
    );
}

/// Coverage guard for `differential_fuzz_push_pop_assert_sequences_agree` (same
/// seeds, same per-seed shape draws, same `draw_schedule_step`; no theory and no
/// offline decider is run).
///
/// Class: an EXPLICIT pop (`ScheduleStep::Pop`, drawn only at `depth > 0`),
/// including a pop that returns to level 0 and an assert issued after a pop (a
/// re-solve on the restored state). With the raw-state LCG `below(4)` advanced by
/// +3 mod 4 per draw, so a pop was never drawn at depth > 0: measured 2026-09-16,
/// 0 of 7200 steps (lane ax-proptest, `bench-results/proptest-box-audit-20260916`).
///
/// The mirror here assumes the theory never conflicts (a conflict pops the
/// assert's own frame, which only lowers `depth`); the fuzz prints the live
/// `explicit_pops=` count it actually executed alongside this one.
///
/// Not guarded here because it is structural, not an LCG artefact:
/// `theory_propagation_is_sound_and_fires` only ever calls `assert(i, true)`, so a
/// propagation whose reason holds a false-polarity literal is unreachable by
/// construction.
#[test]
fn the_generator_reaches_explicit_pops() {
    let mut steps = 0u32;
    let mut pops = 0u32;
    let mut pops_to_level_zero = 0u32;
    let mut asserts_after_pop = 0u32;
    let mut seeds_with_pop = 0u32;
    for seed in 0..SCHEDULE_SEEDS {
        let mut rng = schedule_rng(seed);
        let mut arena = TermArena::new();
        let nvars = 1 + usize::try_from(rng.below(2)).expect("fits"); // 1..=2 vars
        let vars: Vec<TermId> = (0..nvars)
            .map(|i| {
                let s = arena
                    .declare(&format!("y{i}"), Sort::Int)
                    .expect("declare int");
                arena.var(s)
            })
            .collect();
        let natoms = 3 + usize::try_from(rng.below(4)).expect("fits"); // 3..=6 atoms
        let _atoms: Vec<TermId> = (0..natoms)
            .map(|_| random_atom(&mut arena, &vars, &mut rng))
            .collect();

        let mut depth = 0u32;
        let mut last_was_pop = false;
        let mut any_pop = false;
        for _ in 0..SCHEDULE_STEPS {
            steps += 1;
            let step = draw_schedule_step(&mut rng, natoms, depth);
            match step {
                ScheduleStep::Push => depth += 1,
                ScheduleStep::Pop => {
                    depth -= 1;
                    pops += 1;
                    any_pop = true;
                    if depth == 0 {
                        pops_to_level_zero += 1;
                    }
                }
                ScheduleStep::Assert { .. } => {
                    // Conflict-free mirror: the assert's own frame stays.
                    depth += 1;
                    if last_was_pop {
                        asserts_after_pop += 1;
                    }
                }
            }
            last_was_pop = step == ScheduleStep::Pop;
        }
        if any_pop {
            seeds_with_pop += 1;
        }
    }
    eprintln!(
        "lia_online schedule coverage: explicit pops {pops}/{steps} steps, pops to level 0 \
         {pops_to_level_zero}, asserts after a pop {asserts_after_pop}, seeds with a pop \
         {seeds_with_pop}/{SCHEDULE_SEEDS}"
    );
    assert!(
        pops >= 400,
        "only {pops}/{steps} steps are explicit pops (old generator: 0)"
    );
    assert!(
        pops_to_level_zero >= 25,
        "only {pops_to_level_zero} explicit pops return to level 0 (old generator: 0)"
    );
    assert!(
        asserts_after_pop >= 200,
        "only {asserts_after_pop} asserts follow an explicit pop (old generator: 0)"
    );
    assert!(
        seeds_with_pop >= 150,
        "only {seeds_with_pop}/{SCHEDULE_SEEDS} schedules contain an explicit pop \
         (old generator: 0)"
    );
}

/// Builds the polarity-applied term for an order atom: the atom itself for
/// `true`, its `BoolNot` for `false` (in a working arena clone).
fn polarity_term(arena: &mut TermArena, atom: TermId, value: bool) -> TermId {
    if value {
        atom
    } else {
        arena.not(atom).expect("not")
    }
}

/// Offline integer verdict for a conjunction: `Some(true)` = `sat`, `Some(false)`
/// = `unsat`, `None` = the offline decider declined (`Unknown`). Built in a clone
/// so polarity `not` terms resolve without mutating the caller's arena.
fn offline_int_verdict(arena: &TermArena, terms: &[TermId]) -> Option<bool> {
    match check_with_lia_simplex(arena, terms) {
        Ok(CheckResult::Sat(_)) => Some(true),
        Ok(CheckResult::Unsat) => Some(false),
        Ok(CheckResult::Unknown(_)) | Err(_) => None,
    }
}

/// The soundness-and-fires gate for `LIA` theory propagation (Slice 1), the
/// integer analogue of `lra_online`'s `theory_propagation_is_sound_and_fires`.
///
/// Over a large LCG corpus of order-atom conjunctions, asserts a random subset
/// true and, for every literal [`LiaTheory::propagate`] emits, checks BOTH:
///   1. **Genuine entailment**: `asserted ∧ ¬entailed` is offline integer-UNSAT
///      (the propagation never fabricates an entailment — the soundness anchor).
///   2. **Asserted-only reason**: every reason literal is an asserted atom at its
///      asserted polarity, and `reason ∧ ¬entailed` is itself integer-UNSAT (the
///      explanation is a genuine core, not just the full state).
///
/// Also counts how often propagation FIRES, asserting Slice 1 meaningfully engages
/// (so the pruning is exercised, not merely falling through).
#[test]
fn theory_propagation_is_sound_and_fires() {
    let mut rng = Lcg::new(0x9e37_79b9_7f4a_7c15);
    let mut fired = 0_u32;
    let mut props_checked = 0_u32;

    for _ in 0..2000 {
        let mut arena = TermArena::new();
        let nvars = 1 + usize::try_from(rng.below(2)).expect("fits"); // 1..=2 vars
        let vars: Vec<TermId> = (0..nvars)
            .map(|i| {
                let s = arena
                    .declare(&format!("z{i}"), Sort::Int)
                    .expect("declare int");
                arena.var(s)
            })
            .collect();

        // Order atoms only (each has a representable single-constraint negation).
        let pool: Vec<TermId> = (0..5)
            .map(|_| random_order_atom(&mut arena, &vars, &mut rng))
            .collect();

        let mut theory = LiaTheory::new(&arena, &pool);
        if !(0..pool.len()).all(|i| theory.tracks(i)) {
            continue;
        }

        // Assert a random subset true; stop at the first conflict.
        let mut asserted: Vec<usize> = Vec::new();
        let mut conflicted = false;
        for i in 0..pool.len() {
            if rng.below(2) == 0 {
                continue;
            }
            if theory.assert(i, true).is_err() {
                conflicted = true;
                break;
            }
            asserted.push(i);
        }
        if conflicted || asserted.is_empty() {
            continue;
        }
        let asserted_terms: Vec<TermId> = asserted.iter().map(|&i| pool[i]).collect();

        for prop in theory.propagate() {
            fired += 1;
            // ¬entailed: the witness that must be refuted by the asserted state.
            let entailed_neg = polarity_term(&mut arena, pool[prop.lit.atom], !prop.lit.value);

            // (1) Genuine entailment: asserted ∧ ¬entailed must be integer-UNSAT.
            let mut full = asserted_terms.clone();
            full.push(entailed_neg);
            if let Some(sat) = offline_int_verdict(&arena, &full) {
                assert!(
                    !sat,
                    "UNSOUND PROPAGATION: asserted ∧ ¬entailed is integer-SAT (lit {:?})",
                    prop.lit
                );
                props_checked += 1;
            }

            // (2) Asserted-only reason, itself a genuine integer-UNSAT core.
            let mut reason_terms: Vec<TermId> = Vec::new();
            for r in &prop.reason {
                assert!(
                    r.value,
                    "reason literal must be asserted-true here (got false), lit {r:?}"
                );
                assert!(
                    asserted.contains(&r.atom),
                    "reason names a NON-asserted atom {} — unsound explanation",
                    r.atom
                );
                reason_terms.push(pool[r.atom]);
            }
            reason_terms.push(entailed_neg);
            if let Some(sat) = offline_int_verdict(&arena, &reason_terms) {
                assert!(
                    !sat,
                    "UNSOUND REASON: reason ∧ ¬entailed is integer-SAT (lit {:?}, reason {:?})",
                    prop.lit, prop.reason
                );
            }
        }
    }

    eprintln!(
        "LIA theory-propagation gate: fired={fired} propagations, \
         {props_checked} entailments integer-offline-confirmed, 0 unsound"
    );
    assert!(
        fired > 50,
        "LIA theory propagation never meaningfully fired ({fired}) — Slice 1 not exercised"
    );
    assert!(
        props_checked > 20,
        "too few LIA propagations integer-offline-confirmed ({props_checked})"
    );
}

/// A directed sanity case that propagation FIRES and is sound: `x >= 5` is
/// asserted; over ℤ this entails `¬(x <= 4)` (i.e. the atom `x <= 4` is forced
/// false). The LP relaxation already refutes `x >= 5 ∧ x <= 4`, so propagation must
/// emit it with an asserted-only reason naming `x >= 5`.
#[test]
fn propagation_fires_on_a_forced_order_atom() {
    let mut arena = TermArena::new();
    let s = arena.declare("x", Sort::Int).expect("declare");
    let x = arena.var(s);
    let five = arena.int_const(5);
    let four = arena.int_const(4);
    let ge5 = arena.int_ge(x, five).expect("x>=5");
    let le4 = arena.int_le(x, four).expect("x<=4");

    let mut theory = LiaTheory::new(&arena, &[ge5, le4]);
    assert!(theory.assert(0, true).is_ok(), "x>=5 feasible");

    let props = theory.propagate();
    let forced = props
        .iter()
        .find(|p| p.lit.atom == 1)
        .expect("x<=4 must be forced false by x>=5 over ℤ");
    assert!(!forced.lit.value, "x<=4 must be entailed FALSE");
    assert!(
        forced.reason.iter().all(|r| r.atom == 0 && r.value),
        "reason must name only the asserted x>=5 (atom 0, true), got {:?}",
        forced.reason
    );
}

/// The latest value an `atom` was assigned in the append-only log, or `None` if
/// it has no live assignment — mirrors the theory's effective `assigned[atom]`.
fn effective(log: &[(usize, bool)], atom: usize) -> Option<bool> {
    log.iter().rev().find(|(a, _)| *a == atom).map(|(_, v)| *v)
}

/// The effective `(atom, value)` set over all atoms: the latest log entry per
/// atom, in atom-index order — the live constraint set the offline query mirrors.
fn effective_set(log: &[(usize, bool)], natoms: usize) -> Vec<(usize, bool)> {
    (0..natoms)
        .filter_map(|atom| effective(log, atom).map(|value| (atom, value)))
        .collect()
}

/// Rebuilds the offline conjunctive query for a live `(atom, value)` stack: each
/// order atom and each *true* equality atom contributes its polarity-applied term;
/// a *false* equality atom (disequality) is dropped (the conjunctive decider and
/// the online theory both decline it — keeping the offline mirror aligned).
fn live_query(
    arena: &TermArena,
    atoms: &[TermId],
    live: &[(usize, bool)],
) -> (TermArena, Vec<TermId>) {
    let mut arena = arena.clone();
    let mut terms = Vec::new();
    for &(atom, value) in live {
        let t = atoms[atom];
        let is_eq = matches!(
            arena.node(t),
            axeyum_ir::TermNode::App {
                op: axeyum_ir::Op::Eq,
                ..
            }
        );
        if is_eq && !value {
            // Disequality: declined by both engines, contributes nothing.
            continue;
        }
        let term = if value { t } else { arena.not(t).expect("not") };
        terms.push(term);
    }
    (arena, terms)
}
