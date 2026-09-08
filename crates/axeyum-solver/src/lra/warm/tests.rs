//! Tests for the warm offline `QF_LIA` decider.
//!
//! The load-bearing one is [`warm_assembles_the_same_system_the_cold_path_builds`].
//! Verdict agreement between the warm and cold paths is a weak check here,
//! because the Gomory round and branch-and-bound are sound on **any** input: a
//! warm path that assembled a permuted, padded or subtly reordered system would
//! still never return a wrong `sat`/`unsat`, so a verdict-only differential
//! passes while the decider quietly decides a different set of cases. These tests
//! therefore compare the assembled **system** — constraints, order, column
//! numbering, `origin` tags and all — against `super::cold_int_system`, and only
//! then the verdicts.

use axeyum_ir::{Sort, TermArena, TermId};

use super::{AssemblyReason, LiaWarmPolicy, WarmLiaDecider, last_lia_warm_stats};
use crate::backend::CheckResult;
use crate::lra::{check_with_lia_simplex, cold_int_system, lia_bnb_node_cap};

// --- fixtures ---------------------------------------------------------------

fn ivar(arena: &mut TermArena, name: &str) -> TermId {
    let symbol = arena.declare(name, Sort::Int).expect("declare int");
    arena.var(symbol)
}

fn iconst(arena: &mut TermArena, value: i128) -> TermId {
    arena.int_const(value)
}

/// A deterministic `xorshift64` stream. Explicit seeds are a public API promise
/// in this tree, so a fuzz that cannot be replayed is not a fuzz.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, bound: u64) -> usize {
        usize::try_from(self.next() % bound).expect("bound fits usize")
    }
}

/// A random atom set over `vars` variables, plus the polarity table a decider
/// takes: key `2*i + 1` is atom `i` true, key `2*i` is atom `i` false.
struct Fixture {
    arena: TermArena,
    atoms: Vec<TermId>,
    /// Whether atom `i` is an integer equality. A false equality is a
    /// disequality, which the conjunctive decider declines outright, so
    /// `LiaTheory::live_lits` never offers one — and neither does this fixture.
    is_equality: Vec<bool>,
    lit_terms: Vec<Option<TermId>>,
}

impl Fixture {
    fn random(rng: &mut Rng, vars: usize, atom_count: usize) -> Option<Self> {
        let mut arena = TermArena::new();
        let columns: Vec<TermId> = (0..vars)
            .map(|i| ivar(&mut arena, &format!("v{i}")))
            .collect();
        let mut atoms = Vec::new();
        let mut is_equality = Vec::new();
        for _ in 0..atom_count {
            let a = columns[rng.below(vars as u64)];
            let b = columns[rng.below(vars as u64)];
            let scale = 1 + i128::try_from(rng.below(3)).expect("small");
            let offset = i128::try_from(rng.below(11)).expect("small") - 5;
            let scale_term = iconst(&mut arena, scale);
            let offset_term = iconst(&mut arena, offset);
            let Ok(scaled) = arena.int_mul(scale_term, a) else {
                continue;
            };
            let Ok(lhs) = arena.int_add(scaled, offset_term) else {
                continue;
            };
            let kind = rng.below(5);
            let built = match kind {
                0 => arena.int_lt(lhs, b),
                1 => arena.int_le(lhs, b),
                2 => arena.int_gt(lhs, b),
                3 => arena.int_ge(lhs, b),
                _ => arena.eq(lhs, b),
            };
            if let Ok(atom) = built {
                atoms.push(atom);
                is_equality.push(kind == 4);
            }
        }
        if atoms.is_empty() {
            return None;
        }
        let mut lit_terms = vec![None; atoms.len() * 2];
        for (index, &atom) in atoms.iter().enumerate() {
            lit_terms[index * 2 + 1] = Some(atom);
            if !is_equality[index] {
                lit_terms[index * 2] = Some(arena.not(atom).expect("negation"));
            }
        }
        Some(Self {
            arena,
            atoms,
            is_equality,
            lit_terms,
        })
    }

    fn decider(&self, policy: LiaWarmPolicy) -> WarmLiaDecider {
        WarmLiaDecider::new(policy, false, self.lit_terms.clone())
    }

    /// The polarity-applied terms for a live key list — what the cold path is
    /// handed for the same conjunction.
    fn terms(&self, keys: &[usize]) -> Vec<TermId> {
        keys.iter()
            .map(|&key| self.lit_terms[key].expect("registered key"))
            .collect()
    }
}

/// A random live key list: each atom either unasserted, asserted true, or
/// asserted false. Equality atoms are only ever asserted true, matching what
/// `LiaTheory::live_lits` hands the decider.
fn random_live(rng: &mut Rng, fixture: &Fixture) -> Vec<usize> {
    let mut keys = Vec::new();
    for index in 0..fixture.atoms.len() {
        match rng.below(3) {
            0 => {}
            1 => keys.push(index * 2 + 1),
            _ if fixture.is_equality[index] => keys.push(index * 2 + 1),
            _ => keys.push(index * 2),
        }
    }
    keys
}

// --- the load-bearing differential ------------------------------------------

/// The warm decider's assembled system must be the **same system** the cold path
/// builds for the same conjunction: same constraints, same order, same column
/// numbering, same `origin` tags, same `nvars`.
///
/// This is the check that the module's central claim is true. A weaker
/// verdict-only differential cannot see a permuted or padded system, because
/// both engines are sound on any input — it would only ever show up as a
/// coverage difference nobody attributed.
#[test]
fn warm_assembles_the_same_system_the_cold_path_builds() {
    let mut rng = Rng(0x7a5e_1a17_2026_0908);
    let mut compared = 0usize;
    let mut nonempty_systems = 0usize;

    for _ in 0..300 {
        let Some(fixture) = Fixture::random(&mut rng, 3, 4) else {
            continue;
        };
        let mut decider = fixture.decider(LiaWarmPolicy::WARM);
        // Several live sets in a row on ONE decider, so the comparison covers
        // extended, shortened and diverged assemblies rather than only cold
        // starts — a warm cache is only interesting after the first call.
        for _ in 0..6 {
            let keys = random_live(&mut rng, &fixture);
            if keys.is_empty() {
                continue;
            }
            let terms = fixture.terms(&keys);
            let cold = cold_int_system(&fixture.arena, &terms, false).expect("cold collects");
            // Assemble without deciding: the engines mutate the system as a
            // backtracking stack and restore it, but the point here is the
            // system as handed over.
            let _ = decider.check(&fixture.arena, &keys, lia_bnb_node_cap(None), None);
            let warm = decider.assembled_system();
            assert_eq!(
                warm, cold,
                "warm and cold systems differ on live keys {keys:?}"
            );
            compared += 1;
            if !cold.constraints.is_empty() {
                nonempty_systems += 1;
            }
        }
    }

    // A comparison that never ran, or only ever compared empty systems, is the
    // inert-gate failure mode this repository keeps finding.
    assert!(
        compared >= 200,
        "the differential compared only {compared} systems"
    );
    assert!(
        nonempty_systems >= 200,
        "the differential compared only {nonempty_systems} NON-EMPTY systems"
    );
}

/// The warm and cold verdicts must agree, over the same random live sets. Weaker
/// than the system comparison above and kept as the end-to-end statement of it:
/// this is the property a caller actually depends on.
#[test]
fn warm_verdicts_agree_with_the_cold_offline_decider() {
    let mut rng = Rng(0x1a17_c01d_2026_0908);
    let mut unsat = 0usize;
    let mut sat = 0usize;

    for _ in 0..250 {
        let Some(fixture) = Fixture::random(&mut rng, 3, 4) else {
            continue;
        };
        let mut decider = fixture.decider(LiaWarmPolicy::WARM);
        for _ in 0..5 {
            let keys = random_live(&mut rng, &fixture);
            if keys.is_empty() {
                continue;
            }
            let terms = fixture.terms(&keys);
            let cold = check_with_lia_simplex(&fixture.arena, &terms);
            let warm = decider.check(&fixture.arena, &keys, lia_bnb_node_cap(None), None);
            match (&warm, &cold) {
                (Ok(CheckResult::Unsat), Ok(CheckResult::Unsat)) => unsat += 1,
                (Ok(CheckResult::Sat(_)), Ok(CheckResult::Sat(_))) => sat += 1,
                (Ok(CheckResult::Unknown(_)), Ok(CheckResult::Unknown(_))) => {}
                (Err(_), Err(_)) => {}
                _ => panic!("warm {warm:?} disagrees with cold {cold:?} on {keys:?}"),
            }
        }
    }

    // Both decided classes have to be reached, or the agreement is vacuous.
    assert!(unsat >= 20, "the fuzz reached only {unsat} unsat verdicts");
    assert!(sat >= 20, "the fuzz reached only {sat} sat verdicts");
}

// --- staleness --------------------------------------------------------------

/// The adversarial staleness case, stated directly: assert a literal, retract it,
/// assert a **different** one, and require the verdict to equal a cold solve of
/// the resulting set.
///
/// This is the shape that makes a warm cache return a *wrong* verdict rather than
/// a slow one — the retracted literal's constraints staying in the system, or its
/// columns staying allocated and shifting the numbering of everything after them.
/// The fixture is chosen so the two literals disagree: `x >= 5` alone is
/// satisfiable, `x <= 0` alone is satisfiable, and the two together are not — so
/// a system that kept the retracted literal answers `unsat` where the truth is
/// `sat`.
#[test]
fn a_retracted_literal_leaves_no_trace_in_the_next_verdict() {
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let five = iconst(&mut arena, 5);
    let zero = iconst(&mut arena, 0);
    let ge_five = arena.int_ge(x, five).expect("x>=5");
    let le_zero = arena.int_le(x, zero).expect("x<=0");
    let atoms = [ge_five, le_zero];
    let mut lit_terms = vec![None; 4];
    for (index, &atom) in atoms.iter().enumerate() {
        lit_terms[index * 2 + 1] = Some(atom);
        lit_terms[index * 2] = Some(arena.not(atom).expect("negation"));
    }
    let mut decider = WarmLiaDecider::new(LiaWarmPolicy::WARM, false, lit_terms);
    let cap = lia_bnb_node_cap(None);

    // 1. `x >= 5` alone: satisfiable.
    let first = decider.check(&arena, &[1], cap, None).expect("decidable");
    assert!(
        matches!(first, CheckResult::Sat(_)),
        "x>=5 alone: {first:?}"
    );

    // 2. Both: unsatisfiable. This is what puts `x >= 5` into the system in a
    //    position a later check must not inherit.
    let both = decider
        .check(&arena, &[1, 3], cap, None)
        .expect("decidable");
    assert_eq!(both, CheckResult::Unsat, "x>=5 and x<=0 together");

    // 3. Retract `x >= 5` — and, critically, retract it from the FRONT, so the
    //    surviving literal moves to a different position and a different column
    //    numbering. `x <= 0` alone is satisfiable.
    let after = decider.check(&arena, &[3], cap, None).expect("decidable");
    assert!(
        matches!(after, CheckResult::Sat(_)),
        "x<=0 alone after retracting x>=5 must be sat, got {after:?}"
    );

    // 4. And it equals a cold solve of exactly that set, taken from a decider
    //    that never saw `x >= 5`.
    let cold = check_with_lia_simplex(&arena, &[le_zero]).expect("decidable");
    assert!(
        matches!(cold, CheckResult::Sat(_)),
        "control: x<=0 alone is sat"
    );

    // 5. Re-asserting the retracted literal must bring the refutation back, so
    //    the retraction did not damage the cache either.
    let again = decider
        .check(&arena, &[1, 3], cap, None)
        .expect("decidable");
    assert_eq!(again, CheckResult::Unsat, "re-asserting must refute again");
}

/// The same staleness question over random push/retract sequences, against the
/// cold decider on every step — the fuzz behind the single fixture above.
///
/// Retractions here are from arbitrary positions, not just the end, because the
/// trail's suffix discipline is what makes the common-prefix reuse correct and a
/// test that only ever pops suffixes cannot see a prefix bug.
#[test]
fn warm_verdicts_survive_arbitrary_retraction_sequences() {
    let mut rng = Rng(0x5741_e202_2026_0908);
    let mut checks = 0usize;
    let mut retractions = 0usize;

    for _ in 0..200 {
        let Some(fixture) = Fixture::random(&mut rng, 3, 5) else {
            continue;
        };
        let mut decider = fixture.decider(LiaWarmPolicy::WARM);
        let mut live: Vec<usize> = Vec::new();
        for _ in 0..10 {
            if !live.is_empty() && rng.below(3) == 0 {
                // Retract from an arbitrary position, not only the end.
                let at = rng.below(live.len() as u64);
                live.remove(at);
                retractions += 1;
            } else {
                let atom = rng.below(fixture.atoms.len() as u64);
                let positive = fixture.is_equality[atom] || rng.below(2) == 0;
                let key = atom * 2 + usize::from(positive);
                if live.contains(&key) || live.contains(&(key ^ 1)) {
                    continue;
                }
                live.push(key);
            }
            if live.is_empty() {
                continue;
            }
            let terms = fixture.terms(&live);
            let cold = check_with_lia_simplex(&fixture.arena, &terms);
            let warm = decider.check(&fixture.arena, &live, lia_bnb_node_cap(None), None);
            let same = matches!(
                (&warm, &cold),
                (Ok(CheckResult::Unsat), Ok(CheckResult::Unsat))
                    | (Ok(CheckResult::Sat(_)), Ok(CheckResult::Sat(_)))
                    | (Ok(CheckResult::Unknown(_)), Ok(CheckResult::Unknown(_)))
                    | (Err(_), Err(_))
            );
            assert!(same, "warm {warm:?} vs cold {cold:?} on live {live:?}");
            // The system, too — a verdict match can hide a system that differs.
            assert_eq!(
                decider.assembled_system(),
                cold_int_system(&fixture.arena, &terms, false).expect("cold collects"),
                "warm system diverged after a retraction on {live:?}"
            );
            checks += 1;
        }
    }

    assert!(checks >= 500, "the fuzz ran only {checks} checks");
    assert!(
        retractions >= 100,
        "the fuzz performed only {retractions} retractions — the case it exists for"
    );
}

// --- policy -----------------------------------------------------------------

/// `LiaWarmPolicy::OFF` must genuinely disable warming: every check rebuilds,
/// and the verdicts are the cold ones.
#[test]
fn policy_off_rebuilds_every_check() {
    let mut rng = Rng(0x0ff0_1a17_2026_0908);
    let fixture = Fixture::random(&mut rng, 3, 4).expect("fixture");
    let mut decider = fixture.decider(LiaWarmPolicy::OFF);
    let guard = super::LiaWarmStatsGuard::enable();
    let mut expected = 0u64;
    for _ in 0..8 {
        let keys = random_live(&mut rng, &fixture);
        if keys.is_empty() {
            continue;
        }
        let _ = decider.check(&fixture.arena, &keys, lia_bnb_node_cap(None), None);
        expected += 1;
    }
    let stats = last_lia_warm_stats().expect("armed");
    drop(guard);
    assert!(expected > 0, "the test made no checks");
    assert_eq!(stats.checks, expected);
    assert_eq!(
        stats.rebuilds, expected,
        "policy OFF must rebuild on every check"
    );
    assert_eq!(
        stats.warm_updates, 0,
        "policy OFF must never report a warm update"
    );
    assert_eq!(
        stats.assembly_reason(AssemblyReason::PolicyCold),
        expected,
        "every rebuild under policy OFF must be attributed to the policy"
    );
}

/// Warming on, the counters must show the assembly actually being reused, and the
/// reasons must add up to the check count.
#[test]
fn warm_counters_attribute_every_check() {
    let mut rng = Rng(0xc017_1a17_2026_0908);
    let fixture = Fixture::random(&mut rng, 3, 5).expect("fixture");
    let mut decider = fixture.decider(LiaWarmPolicy::WARM);
    let guard = super::LiaWarmStatsGuard::enable();
    let mut live: Vec<usize> = Vec::new();
    let mut checks = 0u64;
    for atom in 0..fixture.atoms.len() {
        live.push(atom * 2 + 1);
        let _ = decider.check(&fixture.arena, &live, lia_bnb_node_cap(None), None);
        checks += 1;
    }
    while live.len() > 1 {
        live.pop();
        let _ = decider.check(&fixture.arena, &live, lia_bnb_node_cap(None), None);
        checks += 1;
    }
    // Re-push everything: every literal is now a cache hit, which is the whole
    // point of the per-literal cache and the only way this counter can move.
    for atom in 1..fixture.atoms.len() {
        live.push(atom * 2 + 1);
        let _ = decider.check(&fixture.arena, &live, lia_bnb_node_cap(None), None);
        checks += 1;
    }
    let stats = last_lia_warm_stats().expect("armed");
    drop(guard);

    assert_eq!(stats.checks, checks);
    let attributed: u64 = AssemblyReason::all()
        .iter()
        .map(|&r| stats.assembly_reason(r))
        .sum();
    assert_eq!(
        attributed, checks,
        "every check must be attributed to exactly one assembly reason"
    );
    assert_eq!(stats.rebuilds + stats.warm_updates, checks);
    assert!(
        stats.assembly_reason(AssemblyReason::Extended) > 0,
        "a monotone push sequence must produce extended assemblies"
    );
    assert!(
        stats.assembly_reason(AssemblyReason::Shortened) > 0,
        "a pop sequence must produce shortened assemblies"
    );
    // The literal cache is the point: each literal is collected once, and every
    // later appearance is a hit.
    assert_eq!(
        stats.literal_collections,
        fixture.atoms.len() as u64,
        "each literal must be collected exactly once"
    );
    assert!(
        stats.literal_cache_hits > 0,
        "a repeated live set must hit the literal cache"
    );
    // And the work really is delta-proportional: a system reused across N checks
    // copies far fewer constraints than it holds.
    assert!(
        stats.assembled_constraints_copied < stats.assembled_constraints_live,
        "copied {} constraints for {} live — the assembly is not being reused",
        stats.assembled_constraints_copied,
        stats.assembled_constraints_live
    );
}

/// `last_lia_warm_stats` must distinguish "never armed" from "measured zero".
/// Run on its own thread, because the flag is thread-local and every other test
/// in this file arms it.
#[test]
fn unarmed_counters_read_none_not_zero() {
    std::thread::spawn(|| {
        assert!(
            last_lia_warm_stats().is_none(),
            "an unarmed thread must read None, never a zeroed snapshot"
        );
        let guard = super::LiaWarmStatsGuard::enable();
        drop(guard);
        assert_eq!(
            last_lia_warm_stats().map(|s| s.checks),
            Some(0),
            "an armed thread that ran nothing must read a measured zero"
        );
    })
    .join()
    .expect("thread");
}

/// A key the decider has no term for is a contract violation, and it must fail
/// closed. Silently treating it as contributing nothing would drop a live
/// literal from the conjunction — a weaker system, which is how a warm path
/// turns an `unsat` into a `sat`.
#[test]
fn an_unregistered_literal_key_is_an_error_not_an_omission() {
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let five = iconst(&mut arena, 5);
    let zero = iconst(&mut arena, 0);
    let ge_five = arena.int_ge(x, five).expect("x>=5");
    let le_zero = arena.int_le(x, zero).expect("x<=0");
    // Register only `x <= 0`; key 3 (`x >= 5` true) is deliberately absent.
    let lit_terms = vec![None, Some(le_zero), None, None];
    let mut decider = WarmLiaDecider::new(LiaWarmPolicy::WARM, false, lit_terms);
    let cap = lia_bnb_node_cap(None);
    // Control: the registered key alone decides.
    assert!(matches!(
        decider.check(&arena, &[1], cap, None),
        Ok(CheckResult::Sat(_))
    ));
    // The unregistered key must be refused, NOT silently dropped — dropping it
    // would answer `sat` for the same conjunction the cold path refutes.
    assert!(
        decider.check(&arena, &[1, 3], cap, None).is_err(),
        "an unregistered literal key must be an error"
    );
    let _ = ge_five;
}
