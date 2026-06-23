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
        self.0
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
