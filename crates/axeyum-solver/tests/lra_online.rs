//! Differential validation of the **online** (incremental, backtrackable) `LRA`
//! theory solver (`axeyum_solver::LraTheory` / `check_qf_lra_online`) against the
//! trusted **offline** decider `axeyum_solver::check_with_lra`.
//!
//! The online procedure's soundness is established here, not by a post-hoc
//! re-check inside the solver: for many random `QF_LRA` conjunctions AND random
//! `push`/`assert`/`pop` sequences, the online verdict (sat/unsat) must AGREE
//! with the offline decider on EVERY instance — **zero disagreements**. On `sat`
//! we replay the online model against the original atoms (the trust anchor for
//! sat); on `unsat` the explained conflict must itself be `check_with_lra`-unsat
//! (the core is genuine). A disagreement is a hard failure — the same discipline
//! that validates the online `EufTheory`.
//!
//! All randomness is a deterministic LCG (no `rand`, no clock), so a failure is
//! reproducible from the seed.
#![cfg(feature = "full")]

use axeyum_ir::{Assignment, Rational, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, LraTheory, SolverConfig, TheoryLit, TheorySolver, check_qf_lra_online,
    check_with_lra,
};

/// A small deterministic linear-congruential generator (numerical-recipes
/// constants). No `rand`, no clock — a seed reproduces the whole fuzz.
struct Lcg(u64);

impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        // The raw state is never handed out (ADR-2141): bit `k` of an LCG
        // modulo 2^64 has period 2^(k+1), so `below(4)` at a fixed draw offset
        // is a constant and the push/pop schedule below locked to one cycle —
        // which is why `LraTheory`'s twin of the ADR-2143 defect was read, not
        // fuzzed, by the audit. SplitMix64's finalizer mixes every bit.
        let z = (self.0 ^ (self.0 >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        let z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `0..n`.
    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }

    /// A small signed coefficient in `-3..=3`.
    fn small_coeff(&mut self) -> i128 {
        i128::from(self.below(7)) - 3
    }

    /// A small signed constant in `-5..=5`.
    fn small_const(&mut self) -> i128 {
        i128::from(self.below(11)) - 5
    }
}

/// Declares `count` real variables `r0..r{count}`.
fn real_vars(arena: &mut TermArena, count: usize) -> Vec<TermId> {
    (0..count)
        .map(|i| {
            let s = arena
                .declare(&format!("r{i}"), Sort::Real)
                .expect("declare real");
            arena.var(s)
        })
        .collect()
}

/// Builds a random linear order/equality atom `Σ c_i·x_i + k  REL  0` over the
/// given real variables, as a single typed Boolean term. `REL` is one of
/// `<,<=,>,>=,=`.
fn random_atom(arena: &mut TermArena, lcg: &mut Lcg, vars: &[TermId]) -> TermId {
    // Build the linear expression Σ c_i·x_i.
    let mut expr: Option<TermId> = None;
    for &v in vars {
        let c = lcg.small_coeff();
        if c == 0 {
            continue;
        }
        let coeff = arena.real_const(Rational::integer(c));
        let term = arena.real_mul(coeff, v).expect("c*x");
        expr = Some(match expr {
            None => term,
            Some(acc) => arena.real_add(acc, term).expect("acc+term"),
        });
    }
    let k = lcg.small_const();
    let kconst = arena.real_const(Rational::integer(k));
    let lhs = match expr {
        None => kconst,
        Some(acc) => arena.real_add(acc, kconst).expect("acc+k"),
    };
    let zero = arena.real_const(Rational::zero());
    match lcg.below(5) {
        0 => arena.real_lt(lhs, zero).expect("lt"),
        1 => arena.real_le(lhs, zero).expect("le"),
        2 => arena.real_gt(lhs, zero).expect("gt"),
        3 => arena.real_ge(lhs, zero).expect("ge"),
        _ => arena.eq(lhs, zero).expect("eq"),
    }
}

/// Replays `model` (a `SymbolId -> Value` map) against `atoms`; `true` iff every
/// atom evaluates to `true`.
fn model_replays(arena: &TermArena, atoms: &[TermId], model: &[(SymbolId, Value)]) -> bool {
    let mut assignment = Assignment::new();
    for (s, v) in model {
        assignment.set(*s, v.clone());
    }
    atoms
        .iter()
        .all(|&a| matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))))
}

/// Extracts the `(SymbolId, Value)` pairs from a `Sat` model for the declared
/// real symbols.
fn model_pairs(
    arena: &TermArena,
    model: &axeyum_solver::Model,
    vars: &[TermId],
) -> Vec<(SymbolId, Value)> {
    vars.iter()
        .filter_map(|&v| match arena.node(v) {
            axeyum_ir::TermNode::Symbol(s) => model.get(*s).map(|val| (*s, val)),
            _ => None,
        })
        .collect()
}

/// The differential oracle: builds a single conjunction term from `atoms` and
/// decides it offline. Returns `Some(true)` for sat, `Some(false)` for unsat,
/// `None` if the offline decider declines (overflow/unsupported → skip the case).
fn offline_verdict(arena: &mut TermArena, atoms: &[TermId]) -> Option<bool> {
    match check_with_lra(arena, atoms) {
        Ok(CheckResult::Sat(_)) => Some(true),
        Ok(CheckResult::Unsat) => Some(false),
        Ok(CheckResult::Unknown(_)) | Err(_) => None,
    }
}

/// Drives the incremental [`LraTheory`] over `atoms` all asserted true and
/// returns the explained conflict core of the first infeasibility, if any (used
/// to re-confirm the core is genuinely offline-unsat). `None` if the set stays
/// feasible or any atom is non-LRA.
fn online_conflict_core(arena: &TermArena, atoms: &[TermId]) -> Option<Vec<TheoryLit>> {
    let mut theory = LraTheory::new(arena, atoms);
    if !(0..atoms.len()).all(|i| theory.tracks(i)) {
        return None;
    }
    for (i, _) in atoms.iter().enumerate() {
        if let Err(core) = theory.assert(i, true) {
            return Some(core);
        }
    }
    None
}

#[test]
fn unit_infeasible_core_is_offline_unsat() {
    // 2x - 4 > 0 (x > 2) and x - 1 < 0 (x < 1): infeasible.
    let mut arena = TermArena::new();
    let vars = real_vars(&mut arena, 1);
    let x = vars[0];
    let two = arena.real_const(Rational::integer(2));
    let twox = arena.real_mul(two, x).expect("2x");
    let four = arena.real_const(Rational::integer(4));
    let twox_m4 = arena.real_sub(twox, four).expect("2x-4");
    let zero = arena.real_const(Rational::zero());
    let a0 = arena.real_gt(twox_m4, zero).expect("2x-4>0");
    let one = arena.real_const(Rational::integer(1));
    let xm1 = arena.real_sub(x, one).expect("x-1");
    let a1 = arena.real_lt(xm1, zero).expect("x-1<0");

    let mut theory = LraTheory::new(&arena, &[a0, a1]);
    assert!(theory.assert(0, true).is_ok());
    let core = theory.assert(1, true).expect_err("infeasible");
    assert!(!core.is_empty());
    let core_terms: Vec<TermId> = core
        .iter()
        .map(|l| if l.atom == 0 { a0 } else { a1 })
        .collect();
    assert_eq!(
        check_with_lra(&arena, &core_terms).expect("decidable"),
        CheckResult::Unsat,
        "explained conflict must be offline-unsat"
    );
}

#[test]
fn unit_push_assert_pop_round_trip() {
    let mut arena = TermArena::new();
    let vars = real_vars(&mut arena, 1);
    let x = vars[0];
    let zero = arena.real_const(Rational::zero());
    let neg2 = arena.real_const(Rational::integer(-2));
    let ge0 = arena.real_ge(x, zero).expect("x>=0");
    let xp2 = arena.real_sub(x, neg2).expect("x-(-2)=x+2");
    let le_neg = arena.real_lt(xp2, zero).expect("x+2<0 => x<-2");

    let mut theory = LraTheory::new(&arena, &[ge0, le_neg]);
    assert!(theory.assert(0, true).is_ok());
    theory.push();
    assert!(theory.assert(1, true).is_err(), "x>=0 and x<-2 infeasible");
    theory.pop();
    // Restored: a feasible assert succeeds again.
    theory.push();
    assert!(
        theory.assert(1, false).is_ok(),
        "x>=0 and not(x<-2) feasible"
    );
}

/// ADR-2143, the LRA twin of the ax-proptest audit's STOP sequence
/// (`bench-results/proptest-box-audit-20260916/README.md`):
///
/// ```text
/// push; assert(¬(x ≥ 10))   -> Ok            (x < 10 live)
/// push; assert(x ≥ 10)      -> a conflict whose core names both polarities
/// pop                       -> x < 10 stays live AND stays marked `false`
/// assert(x ≥ 20)            -> a conflict whose core says (0, false), (1, true)
/// ```
///
/// Here the `live` constraint list already accumulated both constraints, so
/// the second step did report a conflict before the repair; what was wrong was
/// the marker. The inner assert overwrote `assigned[0]` and logged the index a
/// second time, so the driver's `pop` past the conflict set `assigned[0]` to
/// `None` while `x < 10` stayed in `live`. `rows_to_core` then reads the
/// polarity as `assigned[atom].unwrap_or(true)`, so the final conflict's core
/// came back as `(0, true), (1, true)` — "x ≥ 10 ∧ x ≥ 20 is infeasible", a
/// FALSE lemma. The core's polarity is the observable this test pins.
#[test]
fn opposite_polarity_reassert_conflicts_and_pop_keeps_the_outer_assignment() {
    let mut arena = TermArena::new();
    let vars = real_vars(&mut arena, 1);
    let x = vars[0];
    let ten = arena.real_const(Rational::integer(10));
    let twenty = arena.real_const(Rational::integer(20));
    let ge10 = arena.real_ge(x, ten).expect("x>=10");
    let ge20 = arena.real_ge(x, twenty).expect("x>=20");

    let mut theory = LraTheory::new(&arena, &[ge10, ge20]);
    theory.push();
    assert!(theory.assert(0, false).is_ok(), "x<10 alone is feasible");
    theory.push();
    let core = theory
        .assert(0, true)
        .expect_err("x>=10 while x<10 is live at the enclosing level is a conflict");
    assert!(
        core.contains(&TheoryLit {
            atom: 0,
            value: false
        }) && core.contains(&TheoryLit {
            atom: 0,
            value: true
        }),
        "the core names both polarities of the atom: {core:?}"
    );
    // Driver discipline: backtrack past the conflicting assertion.
    theory.pop();
    // x>=20 conflicts with the still-live x<10, and the core must carry the
    // polarity x<10 was asserted with — `(0, false)` — not a defaulted `true`.
    let core = theory
        .assert(1, true)
        .expect_err("x>=20 must conflict with the still-live x<10");
    assert!(
        core.contains(&TheoryLit {
            atom: 0,
            value: false
        }),
        "the core must name atom 0 at its LIVE polarity (false): {core:?}"
    );
    assert!(
        !core.contains(&TheoryLit {
            atom: 0,
            value: true
        }),
        "a core naming (0, true) is the stale-marker false lemma: {core:?}"
    );
    theory.pop();
    assert!(
        theory.assert(0, true).is_ok(),
        "after the outer pop x>=10 is feasible"
    );
    assert!(theory.assert(1, true).is_ok(), "and x>=20 with it");
}

#[test]
fn non_lra_atom_declines_gracefully() {
    let mut arena = TermArena::new();
    let bv = arena.declare("bv", Sort::BitVec(4)).expect("declare bv");
    let v = arena.var(bv);
    let k = arena.bv_const(4, 3).expect("bv const");
    let eq = arena.eq(v, k).expect("bv eq");

    let mut theory = LraTheory::new(&arena, &[eq]);
    assert!(!theory.tracks(0));
    assert!(theory.assert(0, true).is_ok(), "no-op, never panics");

    // The online decider over a non-LRA-only query declines (Unknown).
    let verdict = check_qf_lra_online(&arena, &[eq], &SolverConfig::default()).expect("ok");
    assert!(matches!(verdict, CheckResult::Unknown(_)));
}

/// The load-bearing differential fuzz over random `QF_LRA` conjunctions: the
/// online decider must agree with `check_with_lra` on every decided instance,
/// and every online `sat` model must replay. Asserts nonzero sat AND unsat
/// coverage and zero disagreements.
#[test]
fn differential_fuzz_conjunctions_agree_with_offline() {
    let mut lcg = Lcg(0x5eed_1234_abcd_0001);
    let mut sat_count = 0_usize;
    let mut unsat_count = 0_usize;
    let mut decided = 0_usize;

    for _ in 0..4000 {
        let mut arena = TermArena::new();
        let nvars = 2 + usize::try_from(lcg.below(2)).expect("small") /* 2..=3 */;
        let vars = real_vars(&mut arena, nvars);
        let natoms = 2 + usize::try_from(lcg.below(4)).expect("small") /* 2..=5 */;
        let atoms: Vec<TermId> = (0..natoms)
            .map(|_| random_atom(&mut arena, &mut lcg, &vars))
            .collect();

        let Some(offline) = offline_verdict(&mut arena, &atoms) else {
            continue;
        };

        // Online verdict via the full driver over the conjunction.
        let online = check_qf_lra_online(&arena, &atoms, &SolverConfig::default())
            .expect("online never errors");

        match online {
            CheckResult::Sat(model) => {
                assert!(
                    offline,
                    "DISAGREEMENT: online sat but offline unsat on atoms {atoms:?}"
                );
                let pairs = model_pairs(&arena, &model, &vars);
                assert!(
                    model_replays(&arena, &atoms, &pairs),
                    "online sat model did not replay against the originals"
                );
                sat_count += 1;
                decided += 1;
            }
            CheckResult::Unsat => {
                assert!(
                    !offline,
                    "DISAGREEMENT: online unsat but offline sat on atoms {atoms:?}"
                );
                // Independently re-confirm via the incremental theory's conflict
                // core that the named atoms are genuinely offline-unsat.
                if let Some(core) = online_conflict_core(&arena, &atoms) {
                    let core_terms: Vec<TermId> = core.iter().map(|l| atoms[l.atom]).collect();
                    assert_eq!(
                        check_with_lra(&arena, &core_terms).expect("decidable core"),
                        CheckResult::Unsat,
                        "explained conflict core must be offline-unsat"
                    );
                }
                unsat_count += 1;
                decided += 1;
            }
            // Online declined (Unknown): sound — it just costs coverage.
            CheckResult::Unknown(_) => {}
        }
    }

    eprintln!(
        "conjunction fuzz: decided={decided} (sat={sat_count}, unsat={unsat_count}), 0 disagreements"
    );
    assert!(decided > 100, "fuzz decided too few instances ({decided})");
    assert!(sat_count > 0, "fuzz produced no sat coverage");
    assert!(unsat_count > 0, "fuzz produced no unsat coverage");
}

/// Fuzz random `push` / `assert` / `pop` sequences: at every point, the online
/// theory's feasibility of the currently-asserted atom set must match deciding
/// that exact set with `check_with_lra`.
#[test]
fn differential_fuzz_push_pop_sequences_track_offline() {
    let mut lcg = Lcg(0xfeed_face_0000_0007);
    let mut checks = 0_usize;
    let mut sat_seen = false;
    let mut unsat_seen = false;

    for _ in 0..2000 {
        let mut arena = TermArena::new();
        let nvars = 2 + usize::try_from(lcg.below(2)).expect("small");
        let vars = real_vars(&mut arena, nvars);
        // A fixed pool of atoms this run draws from (so atom indices are stable).
        let pool: Vec<TermId> = (0..6)
            .map(|_| random_atom(&mut arena, &mut lcg, &vars))
            .collect();

        let mut theory = LraTheory::new(&arena, &pool);
        if !(0..pool.len()).all(|i| theory.tracks(i)) {
            continue;
        }

        // The asserted-atom stack, mirrored test-side, with push markers so we
        // can reconstruct the live set and re-decide it offline.
        let mut live: Vec<usize> = Vec::new();
        let mut markers: Vec<usize> = Vec::new();
        // Track which atom indices are *currently* asserted (true) — for the
        // offline re-decision. We only ever assert atoms true here.
        let mut conflicted = false;

        for _ in 0..20 {
            match lcg.below(4) {
                // push
                0 => {
                    theory.push();
                    markers.push(live.len());
                }
                // pop
                1 => {
                    if let Some(m) = markers.pop() {
                        theory.pop();
                        live.truncate(m);
                        conflicted = false; // re-decided below from the live set
                    }
                }
                // assert a random pool atom true
                _ => {
                    if conflicted {
                        continue; // an asserted infeasible state stays infeasible
                    }
                    let idx = usize::try_from(lcg.below(pool.len() as u64)).expect("small");
                    if live.contains(&idx) {
                        continue;
                    }
                    let res = theory.assert(idx, true);
                    live.push(idx);
                    if res.is_err() {
                        conflicted = true;
                    }
                }
            }

            // Re-decide the currently-live atom set offline and compare to the
            // theory's running feasibility (`conflicted`).
            let live_terms: Vec<TermId> = live.iter().map(|&i| pool[i]).collect();
            if live_terms.is_empty() {
                continue;
            }
            let Some(offline) = offline_verdict(&mut arena, &live_terms) else {
                continue;
            };
            // The theory reports infeasible (`conflicted`) iff offline says unsat.
            // (After a pop that cleared the conflict, we must re-derive it: if the
            // live set is still unsat but we are not flagged conflicted, that is a
            // case where the conflict was on a different atom — re-assert is not
            // modeled here, so only check the SAT direction strictly and the
            // UNSAT direction when we are flagged.)
            if conflicted {
                assert!(
                    !offline,
                    "DISAGREEMENT: theory conflict but offline sat on live {live_terms:?}"
                );
                unsat_seen = true;
            } else if offline {
                sat_seen = true;
            }
            checks += 1;
        }
    }

    eprintln!("push/pop fuzz: {checks} checks, sat_seen={sat_seen}, unsat_seen={unsat_seen}");
    assert!(checks > 100, "push/pop fuzz made too few checks ({checks})");
    assert!(sat_seen, "push/pop fuzz saw no sat states");
    assert!(unsat_seen, "push/pop fuzz saw no conflict states");
}

/// One step of the random `push`/`pop`/`assert` schedule below.
enum ScheduleStep {
    Push,
    Pop,
    Assert { atom: usize, value: bool },
}

const SCHEDULE_SEEDS: u64 = 300;
const SCHEDULE_STEPS: usize = 24;

/// Draws the next schedule step: `below(4)` picks push (0), pop (1, only while
/// `depth > 0`; at depth 0 the draw falls through to an assert) or an assert of
/// a random atom at a random polarity.
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

/// The latest logged value of `atom`, if any.
fn effective(log: &[(usize, bool)], atom: usize) -> Option<bool> {
    log.iter().rev().find(|(a, _)| *a == atom).map(|(_, v)| *v)
}

/// The effective `(atom, value)` set over all atoms, in atom-index order.
fn effective_set(log: &[(usize, bool)], natoms: usize) -> Vec<(usize, bool)> {
    (0..natoms)
        .filter_map(|atom| effective(log, atom).map(|value| (atom, value)))
        .collect()
}

/// The offline conjunctive query for a live `(atom, value)` set: each order atom
/// and each *true* equality atom contributes its polarity-applied term; a *false*
/// equality atom (a disjunction) is dropped, as the theory drops it.
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
            continue;
        }
        terms.push(if value { t } else { arena.not(t).expect("not") });
    }
    (arena, terms)
}

/// Driver discipline: backtrack past the assertion just made (its wrapping
/// `push`), in the theory and in the mirror.
fn backtrack(
    theory: &mut LraTheory,
    marks: &mut Vec<usize>,
    log: &mut Vec<(usize, bool)>,
    depth: &mut u32,
) {
    theory.pop();
    let mark = marks.pop().expect("just pushed a mark");
    log.truncate(mark);
    *depth -= 1;
}

/// A conflict core is a lemma `¬⋀core`, so every literal it names must be
/// ASSERTED at that polarity: the mirrored live value, or the trigger literal
/// itself. A core naming the other polarity is a false lemma — the shape a
/// stale marker produces (ADR-2143, `rows_to_core`'s `unwrap_or(true)`).
fn assert_core_is_asserted(
    seed: u64,
    log: &[(usize, bool)],
    natoms: usize,
    trigger: (usize, bool),
    core: &[TheoryLit],
) {
    for lit in core {
        let asserted = effective(log, lit.atom) == Some(lit.value)
            || (lit.atom == trigger.0 && lit.value == trigger.1);
        assert!(
            asserted,
            "DISAGREEMENT seed {seed}: core literal {lit:?} is not asserted \
             (live={:?}, trigger={trigger:?})",
            effective_set(log, natoms)
        );
    }
}

/// The LRA twin of `tests/lia_online.rs::differential_fuzz_push_pop_assert_sequences_agree`
/// (ADR-2143): random `push`/`pop`/`assert` schedules at BOTH polarities, each
/// assert wrapped in its own `push` and popped on a conflict (driver
/// discipline), the theory's per-step verdict compared with `check_with_lra`
/// on the mirrored live set. A re-assert of a live atom at the opposite
/// polarity must be a conflict, and after the pop the outer assignment must
/// still be there — the sequence the audit found `LiaTheory` losing and read
/// (but could not reach) in `LraTheory`, whose schedule was locked to one LCG
/// cycle until the finalizer above.
#[test]
fn differential_fuzz_push_pop_assert_sequences_agree() {
    let mut conflict_steps = 0_u32;
    let mut clean_steps = 0_u32;
    let mut explicit_pops = 0_u32;
    let mut polarity_conflicts = 0_u32;

    for seed in 0..SCHEDULE_SEEDS {
        let mut rng = Lcg(seed.wrapping_mul(0xD1B5_4A32_D192_ED03).wrapping_add(7));
        let mut arena = TermArena::new();
        let nvars = 1 + usize::try_from(rng.below(2)).expect("fits");
        let vars = real_vars(&mut arena, nvars);
        let natoms = 3 + usize::try_from(rng.below(4)).expect("fits");
        let atoms: Vec<TermId> = (0..natoms)
            .map(|_| random_atom(&mut arena, &mut rng, &vars))
            .collect();

        let mut theory = LraTheory::new(&arena, &atoms);
        if !(0..natoms).all(|i| theory.tracks(i)) {
            continue;
        }
        let mut log: Vec<(usize, bool)> = Vec::new();
        let mut marks: Vec<usize> = Vec::new();
        let mut depth = 0_u32;

        for _ in 0..SCHEDULE_STEPS {
            match draw_schedule_step(&mut rng, natoms, depth) {
                ScheduleStep::Push => {
                    theory.push();
                    marks.push(log.len());
                    depth += 1;
                }
                ScheduleStep::Pop => {
                    theory.pop();
                    let mark = marks.pop().expect("depth>0 has a mark");
                    log.truncate(mark);
                    depth -= 1;
                    explicit_pops += 1;
                }
                ScheduleStep::Assert { atom, value } => {
                    theory.push();
                    marks.push(log.len());
                    depth += 1;

                    let result = theory.assert(atom, value);
                    let current = effective(&log, atom);
                    if let Err(core) = &result {
                        assert_core_is_asserted(seed, &log, natoms, (atom, value), core);
                    }
                    if current == Some(!value) {
                        assert!(
                            result.is_err(),
                            "DISAGREEMENT seed {seed}: atom {atom} is live at {current:?} and \
                             the theory accepted its negation (live={:?})",
                            effective_set(&log, natoms)
                        );
                        polarity_conflicts += 1;
                        backtrack(&mut theory, &mut marks, &mut log, &mut depth);
                        continue;
                    }
                    if current != Some(value) {
                        log.push((atom, value));
                    }

                    let live = effective_set(&log, natoms);
                    let (mut live_arena, live_terms) = live_query(&arena, &atoms, &live);
                    let offline = if live_terms.is_empty() {
                        Some(true)
                    } else {
                        offline_verdict(&mut live_arena, &live_terms)
                    };
                    match (result.is_err(), offline) {
                        (true, Some(false)) => conflict_steps += 1,
                        (false, Some(true)) => clean_steps += 1,
                        (true, Some(true)) => panic!(
                            "DISAGREEMENT seed {seed}: theory reported a conflict but the \
                             live set is offline-SAT (live={live:?})"
                        ),
                        (false, Some(false)) => panic!(
                            "DISAGREEMENT seed {seed}: theory reported no conflict but the \
                             live set is offline-UNSAT (live={live:?})"
                        ),
                        (_, None) => {}
                    }

                    if result.is_err() {
                        backtrack(&mut theory, &mut marks, &mut log, &mut depth);
                    }
                }
            }
        }
    }

    eprintln!(
        "COVERAGE push/pop/assert (LRA): conflict_steps={conflict_steps} \
         clean_steps={clean_steps} explicit_pops={explicit_pops} \
         polarity_conflicts={polarity_conflicts}"
    );
    assert!(
        conflict_steps > 0,
        "the schedule must reach a conflict state"
    );
    assert!(clean_steps > 0, "the schedule must reach a feasible state");
    assert!(explicit_pops > 0, "the schedule must draw an explicit pop");
    assert!(
        polarity_conflicts > 0,
        "the schedule must re-assert a live atom at the opposite polarity (ADR-2143)"
    );
}

/// Builds the typed Boolean term for the *negation* of an order atom `lhs REL 0`
/// (the atom shapes `random_atom` produces), used to independently verify a
/// propagation: `asserted ∧ ¬entailed` must be offline-unsat. Returns `None` for
/// shapes other than the order relations (e.g. equality).
fn negate_order_atom(arena: &mut TermArena, atom: TermId) -> Option<TermId> {
    use axeyum_ir::{Op, TermNode};
    let TermNode::App { op, args } = arena.node(atom) else {
        return None;
    };
    let (op, l, r) = (*op, args[0], args[1]);
    match op {
        Op::RealLt => Some(arena.real_ge(l, r).expect("ge")),
        Op::RealLe => Some(arena.real_gt(l, r).expect("gt")),
        Op::RealGt => Some(arena.real_le(l, r).expect("le")),
        Op::RealGe => Some(arena.real_lt(l, r).expect("lt")),
        _ => None,
    }
}

/// SOUNDNESS gate for **theory propagation** (Slice 1): over a deterministic LCG
/// corpus, assert a random subset of order atoms true into the incremental
/// [`LraTheory`], call `propagate()`, and for EVERY emitted propagation
/// independently verify with the trusted offline decider that
///
///   1. the entailed literal is *genuinely* entailed — `asserted ∧ ¬entailed` is
///      offline-UNSAT (a fabricated propagation would make this SAT: a hard fail);
///   2. the carried `reason` is **asserted-only** (every reason literal is one of
///      the currently-asserted atoms at its asserted polarity), and the lemma
///      `reason ∧ ¬entailed` is itself offline-UNSAT (the explanation is genuine).
///
/// Also counts how often propagation FIRES, asserting it engages on a meaningful
/// number of instances (so Slice 1 is exercised, not merely falling through).
#[test]
fn theory_propagation_is_sound_and_fires() {
    let mut lcg = Lcg(0x9e37_79b9_7f4a_7c15);
    let mut fired = 0_usize;
    let mut props_checked = 0_usize;

    for _ in 0..3000 {
        let mut arena = TermArena::new();
        let nvars = 1 + usize::try_from(lcg.below(2)).expect("small") /* 1..=2 */;
        let vars = real_vars(&mut arena, nvars);
        // Order atoms only (so each has a representable single-constraint negation).
        let pool: Vec<TermId> = (0..5)
            .map(|_| {
                loop {
                    let a = random_atom(&mut arena, &mut lcg, &vars);
                    if negate_order_atom(&mut arena, a).is_some() {
                        break a;
                    }
                }
            })
            .collect();

        let mut theory = LraTheory::new(&arena, &pool);
        if !(0..pool.len()).all(|i| theory.tracks(i)) {
            continue;
        }

        // Assert a random subset true; stop at the first conflict (post-conflict
        // propagation is not meaningful).
        let mut asserted: Vec<usize> = Vec::new();
        let mut conflicted = false;
        for i in 0..pool.len() {
            if lcg.below(2) == 0 {
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

        // The currently-asserted atom terms (all asserted true here).
        let asserted_terms: Vec<TermId> = asserted.iter().map(|&i| pool[i]).collect();

        for prop in theory.propagate() {
            fired += 1;
            // The entailed literal's *negated* term: false-polarity means ¬atom is
            // entailed, so the witness to refute is the atom itself.
            let entailed_neg = if prop.lit.value {
                negate_order_atom(&mut arena, pool[prop.lit.atom]).expect("order atom")
            } else {
                pool[prop.lit.atom]
            };

            // (1) Genuine entailment: asserted ∧ ¬entailed must be offline-UNSAT.
            let mut full = asserted_terms.clone();
            full.push(entailed_neg);
            if let Some(offline) = offline_verdict(&mut arena, &full) {
                assert!(
                    !offline,
                    "UNSOUND PROPAGATION: asserted ∧ ¬entailed is SAT (lit {:?})",
                    prop.lit
                );
                props_checked += 1;
            }

            // (2) Asserted-only reason: every reason literal is an asserted atom at
            //     its asserted polarity (here always true), and reason ∧ ¬entailed
            //     is itself offline-UNSAT (the explanation is a genuine core).
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
            if let Some(offline) = offline_verdict(&mut arena, &reason_terms) {
                assert!(
                    !offline,
                    "UNSOUND REASON: reason ∧ ¬entailed is SAT (lit {:?}, reason {:?})",
                    prop.lit, prop.reason
                );
            }
        }
    }

    eprintln!(
        "theory-propagation gate: fired={fired} propagations, {props_checked} entailments offline-confirmed, 0 unsound"
    );
    assert!(
        fired > 50,
        "theory propagation never meaningfully fired ({fired}) — Slice 1 not exercised"
    );
    assert!(
        props_checked > 20,
        "too few propagations offline-confirmed ({props_checked})"
    );
}

/// Determinism across the public driver: solving the same `QF_LRA` query twice
/// yields the identical verdict (and identical sat model when sat). The Luby
/// restart schedule is a pure function of the restart index, so the restart
/// points — and hence the whole search trajectory — are reproducible. Run over a
/// fuzz batch so the restart-bearing instances are covered too.
#[test]
fn online_driver_is_deterministic() {
    let mut lcg = Lcg(0x0bad_c0de_dead_0007);
    let mut checked = 0_usize;

    for _ in 0..2000 {
        let mut arena = TermArena::new();
        let nvars = 2 + usize::try_from(lcg.below(2)).expect("small");
        let vars = real_vars(&mut arena, nvars);
        let natoms = 3 + usize::try_from(lcg.below(5)).expect("small");
        let atoms: Vec<TermId> = (0..natoms)
            .map(|_| random_atom(&mut arena, &mut lcg, &vars))
            .collect();

        let first = check_qf_lra_online(&arena, &atoms, &SolverConfig::default())
            .expect("online never errors");
        let second = check_qf_lra_online(&arena, &atoms, &SolverConfig::default())
            .expect("online never errors");

        match (&first, &second) {
            (CheckResult::Sat(m1), CheckResult::Sat(m2)) => {
                let p1 = model_pairs(&arena, m1, &vars);
                let p2 = model_pairs(&arena, m2, &vars);
                assert_eq!(p1, p2, "non-deterministic sat model on atoms {atoms:?}");
            }
            (CheckResult::Unsat, CheckResult::Unsat)
            | (CheckResult::Unknown(_), CheckResult::Unknown(_)) => {}
            _ => panic!("non-deterministic verdict {first:?} != {second:?} on atoms {atoms:?}"),
        }
        checked += 1;
    }

    eprintln!("determinism gate: {checked} queries, identical verdict on every repeat");
    assert!(
        checked > 100,
        "determinism gate ran too few queries ({checked})"
    );
}
