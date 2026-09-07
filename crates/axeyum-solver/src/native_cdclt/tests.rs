//! The adapter is checked against the driver it replaces, not against itself.
//!
//! Two engines now decide the same CDCL(T) problem. The only thing that makes
//! swapping one for the other safe is that they are made to disagree on
//! thousands of random instances and do not — and, separately, that a
//! third-party brute force agrees with both, so "they agree" cannot mean "they
//! are wrong in the same way".
//!
//! The theory is a set of forbidden cubes, and it is deliberately **incomplete
//! on partial assignments**: `assert` reports only a violated cube that names
//! the literal it was just handed, so a cube that became violated through some
//! earlier assignment is MISSED and surfaces later, at `final_check`. That is
//! not fastidiousness — a core with no current-decision-level literal
//! underflows 1-UIP's path counter in BOTH drivers (`c9d332c1`), so a fixture
//! that reported any violated cube would be testing a contract violation rather
//! than the adapter.
//!
//! It propagates: any cube one literal short of complete entails the negation of
//! that literal, with the rest of the cube as its reason. Both the eager and the
//! deferred explanation channel are exercised, because the second is where the
//! two drivers' translation of a reason differs and where both defects were.

use std::collections::BTreeSet;

use super::{NativeSolveOutcome, solve_native};
use crate::cdclt::{CdclT, Lit, Outcome};
use crate::euf_egraph::{
    ExplanationId, FinalCheckOutcome, PropagationQueue, TheoryExplanation, TheoryLit, TheoryProp,
    TheorySolver,
};

/// A deterministic linear-congruential PRNG (MMIX constants) — the house
/// convention; no clock, no entropy, fully reproducible per seed.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 11
    }

    fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next_u64() % n as u64).expect("modulus fits usize")
    }

    fn coin(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
}

/// A theory whose truth is "none of these cubes may all hold at once".
///
/// `assert` reports a conflict only for a violated cube that NAMES the literal
/// it was just handed, so the core always contains a current-decision-level
/// literal (see the module header). `propagate` emits the last literal of any
/// cube that is one short of complete, negated, with the rest of the cube as
/// its reason: a genuinely entailed literal, so both drivers may assign it
/// without a decision. `final_check` catches whatever `assert` missed.
#[derive(Clone)]
struct CubeTheory {
    forbidden: Vec<Vec<(usize, bool)>>,
    values: Vec<Option<bool>>,
    trail: Vec<usize>,
    marks: Vec<usize>,
    /// Emit reasons as deferred handles rather than materialised literals, so
    /// the lazy channel and `explain` are exercised too.
    lazy: bool,
    /// The handles issued, so `explain` can resolve one. Index is the handle.
    issued: Vec<Vec<TheoryLit>>,
}

impl CubeTheory {
    fn new(atoms: usize, forbidden: Vec<Vec<(usize, bool)>>, lazy: bool) -> Self {
        Self {
            forbidden,
            values: vec![None; atoms],
            trail: Vec::new(),
            marks: Vec::new(),
            lazy,
            issued: Vec::new(),
        }
    }

    /// A forbidden cube every one of whose literals is currently asserted.
    fn violated(&self) -> Option<&Vec<(usize, bool)>> {
        self.forbidden
            .iter()
            .find(|cube| cube.iter().all(|&(a, v)| self.values[a] == Some(v)))
    }

    /// A violated cube that NAMES `atom`.
    ///
    /// Both drivers' 1-UIP analysis requires a conflict core to contain a
    /// literal of the current decision level (`c9d332c1`), and the only literal
    /// `assert` can be sure is at the current level is the one it was just
    /// handed. Reporting any violated cube — including one that became violated
    /// earlier and was missed — hands the driver a core with no current-level
    /// literal and its path counter underflows. Every in-tree `TheorySolver`
    /// respects this; so must a fixture, or it is testing a contract violation
    /// rather than the adapter.
    fn violated_naming(&self, atom: usize) -> Option<&Vec<(usize, bool)>> {
        self.forbidden.iter().find(|cube| {
            cube.iter().any(|&(a, _)| a == atom)
                && cube.iter().all(|&(a, v)| self.values[a] == Some(v))
        })
    }
}

impl TheorySolver for CubeTheory {
    fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        self.values[atom] = Some(value);
        self.trail.push(atom);
        if let Some(cube) = self.violated_naming(atom) {
            return Err(cube
                .iter()
                .map(|&(a, v)| TheoryLit { atom: a, value: v })
                .collect());
        }
        Ok(())
    }

    fn push(&mut self) {
        self.marks.push(self.trail.len());
    }

    fn pop(&mut self) {
        let mark = self.marks.pop().unwrap_or(0);
        while self.trail.len() > mark {
            let atom = self.trail.pop().expect("trail above mark");
            self.values[atom] = None;
        }
    }

    fn propagate(&self) -> Vec<TheoryProp> {
        let mut out = Vec::new();
        for cube in &self.forbidden {
            let mut unassigned = None;
            let mut ok = true;
            for &(atom, value) in cube {
                match self.values[atom] {
                    Some(v) if v == value => {}
                    Some(_) => {
                        ok = false;
                        break;
                    }
                    None => {
                        if unassigned.is_some() {
                            ok = false;
                            break;
                        }
                        unassigned = Some((atom, value));
                    }
                }
            }
            if !ok {
                continue;
            }
            let Some((atom, value)) = unassigned else {
                continue;
            };
            // Every other literal of the cube holds, so the cube forbids this
            // one: `¬value` is entailed. The reason is the rest of the cube.
            let reason = cube
                .iter()
                .filter(|&&(a, _)| a != atom)
                .map(|&(a, v)| TheoryLit { atom: a, value: v })
                .collect();
            out.push(TheoryProp {
                lit: TheoryLit {
                    atom,
                    value: !value,
                },
                reason,
            });
        }
        out
    }

    fn propagate_into(&mut self, queue: &mut PropagationQueue) {
        for prop in self.propagate() {
            if self.lazy {
                let handle = ExplanationId(self.issued.len() as u64);
                self.issued.push(prop.reason);
                queue.push_lazy(prop.lit, handle);
            } else {
                queue.push_eager(prop.lit, prop.reason);
            }
        }
    }

    fn explain(&mut self, handle: ExplanationId) -> Option<Vec<TheoryLit>> {
        self.issued.get(usize::try_from(handle.0).ok()?).cloned()
    }

    fn final_check(&mut self) -> FinalCheckOutcome {
        match self.violated() {
            None => FinalCheckOutcome::Sat,
            Some(cube) => FinalCheckOutcome::Conflict(TheoryExplanation::Eager(
                cube.iter()
                    .map(|&(a, v)| TheoryLit { atom: a, value: v })
                    .collect(),
            )),
        }
    }
}

struct Instance {
    var_count: usize,
    atom_count: usize,
    clauses: Vec<Vec<Lit>>,
    forbidden: Vec<Vec<(usize, bool)>>,
}

fn gen_instance(rng: &mut Lcg) -> Instance {
    let atom_count = 3 + rng.below(4); // 3..=6 atoms
    let var_count = atom_count + rng.below(3); // plus 0..=2 Tseitin variables
    let clause_count = 2 + rng.below(8);
    let mut clauses = Vec::with_capacity(clause_count);
    for _ in 0..clause_count {
        let width = 1 + rng.below(3);
        let mut seen = BTreeSet::new();
        let mut clause = Vec::new();
        for _ in 0..width {
            let var = rng.below(var_count);
            if seen.insert(var) {
                clause.push(Lit {
                    var,
                    positive: rng.coin(),
                });
            }
        }
        if !clause.is_empty() {
            clauses.push(clause);
        }
    }
    let cube_count = rng.below(4);
    let mut forbidden = Vec::with_capacity(cube_count);
    for _ in 0..cube_count {
        let width = 1 + rng.below(3);
        let mut seen = BTreeSet::new();
        let mut cube = Vec::new();
        for _ in 0..width {
            let atom = rng.below(atom_count);
            if seen.insert(atom) {
                cube.push((atom, rng.coin()));
            }
        }
        if !cube.is_empty() {
            forbidden.push(cube);
        }
    }
    Instance {
        var_count,
        atom_count,
        clauses,
        forbidden,
    }
}

/// The independent answer: enumerate every total assignment of the skeleton and
/// ask whether one satisfies the clauses and violates no forbidden cube. This is
/// what makes "the two engines agree" mean something.
fn brute_force_sat(inst: &Instance) -> bool {
    (0u32..(1u32 << inst.var_count)).any(|bits| {
        let value = |var: usize| bits >> var & 1 == 1;
        let clauses_ok = inst
            .clauses
            .iter()
            .all(|c| c.iter().any(|l| value(l.var) == l.positive));
        let theory_ok = !inst
            .forbidden
            .iter()
            .any(|cube| cube.iter().all(|&(a, v)| value(a) == v));
        clauses_ok && theory_ok
    })
}

fn run_both(inst: &Instance, lazy: bool) -> (Outcome, Outcome) {
    let mut cdclt_theory = CubeTheory::new(inst.atom_count, inst.forbidden.clone(), lazy);
    let mut solver = CdclT::new(inst.var_count, inst.atom_count, inst.clauses.clone(), None);
    let legacy = solver.solve(&mut cdclt_theory);

    let mut native_theory = CubeTheory::new(inst.atom_count, inst.forbidden.clone(), lazy);
    let native = match solve_native(
        inst.var_count,
        inst.atom_count,
        &inst.clauses,
        None,
        &mut native_theory,
    ) {
        NativeSolveOutcome::Sat(_) => Outcome::Sat,
        NativeSolveOutcome::Unsat => Outcome::Unsat,
        NativeSolveOutcome::Unknown => Outcome::Unknown,
    };
    (legacy, native)
}

/// The gate. Two independent engines and one brute force over thousands of
/// random instances, in both the eager and the deferred explanation channel.
/// A single disagreement is a hard failure: this is the check that decides
/// whether a shipping route may be moved.
#[test]
fn the_two_engines_and_a_brute_force_agree_on_random_instances() {
    let mut rng = Lcg::new(0x5eed_5eed);
    let mut disagreements = 0usize;
    let mut unsat_seen = 0usize;
    let mut sat_seen = 0usize;
    for case in 0..4_000u64 {
        let inst = gen_instance(&mut rng);
        let expected = brute_force_sat(&inst);
        for lazy in [false, true] {
            let (legacy, native) = run_both(&inst, lazy);
            // `Unknown` is a permitted verdict for both and there is no deadline
            // here, so it should not appear; it is not a *wrong* answer though,
            // so only a contradiction counts.
            for (name, outcome) in [("cdclt", legacy), ("native", native)] {
                let wrong = match outcome {
                    Outcome::Sat => !expected,
                    Outcome::Unsat => expected,
                    Outcome::Unknown => false,
                };
                assert!(
                    !wrong,
                    "case {case} lazy={lazy}: {name} said {outcome:?}, brute force says \
                     sat={expected}; clauses={:?} forbidden={:?}",
                    inst.clauses, inst.forbidden
                );
            }
            if legacy != native {
                disagreements += 1;
            }
            match legacy {
                Outcome::Sat => sat_seen += 1,
                Outcome::Unsat => unsat_seen += 1,
                Outcome::Unknown => {}
            }
        }
    }
    assert_eq!(disagreements, 0, "the two engines must decide alike");
    // The population must contain both verdicts, or "they agree" is a statement
    // about one of them.
    assert!(sat_seen > 100, "sat instances seen: {sat_seen}");
    assert!(unsat_seen > 100, "unsat instances seen: {unsat_seen}");
}

/// A native refutation carries the ADR-1704 artifact, and the artifact's lemma
/// count is a subtraction on it rather than something the adapter asserts. This
/// is the capability `CdclT` structurally cannot provide, so it is checked
/// directly rather than inferred from the verdict agreement above.
#[test]
fn a_native_refutation_carries_a_checkable_two_stream_artifact() {
    // Skeleton `(x0) & (x1)` is Boolean-satisfiable; the theory forbids
    // `x0 & x1`, so the refutation is entirely the theory's.
    let clauses = vec![
        vec![Lit {
            var: 0,
            positive: true,
        }],
        vec![Lit {
            var: 1,
            positive: true,
        }],
    ];
    let mut theory = CubeTheory::new(2, vec![vec![(0, true), (1, true)]], false);
    // Recording is OFF by default -- the dispatcher pays nothing for a proof it
    // does not read -- so a test about the artifact has to ask for it exactly
    // the way the evidence layer does.
    let outcome =
        super::with_artifact_recording(|| solve_native(2, 2, &clauses, None, &mut theory));
    assert!(
        matches!(outcome, NativeSolveOutcome::Unsat),
        "the theory refutes the only Boolean model: {outcome:?}"
    );
    // Through the published slot, which is the channel the evidence layer
    // reads: a test that took the artifact from a return value would not
    // exercise the path a shipping route actually uses.
    let artifact =
        super::take_last_theory_refutation().expect("a native refutation publishes its artifact");
    assert_eq!(
        artifact.theory_lemma_count(),
        1,
        "one lemma was assumed, and the count is |extended| - |cnf|"
    );
    assert_eq!(
        artifact.check(),
        axeyum_cnf::TheoryRefutationCheck::CheckedModuloLemmas { lemmas: 1 },
        "the Boolean stream checks over cnf ++ lemmas, and the lemma is undischarged"
    );
    let step = crate::trust::theory_refutation_trust_step(&artifact);
    assert_eq!(step.id, crate::trust::TrustId::SatRefutationModuloTheory);
    assert!(!step.certified, "ADR-1704 prohibition 2");
}

/// The adapter negates once and in one direction. A conflict core the theory
/// reports as *asserted* literals must reach the core as a clause whose every
/// literal is FALSE — get the direction wrong and the search learns the
/// negation of what the theory meant. The check is behavioural: the fixture is
/// Boolean-satisfiable and only the theory refutes it, so an inverted
/// translation cannot produce this `unsat`.
#[test]
fn the_asserted_to_clause_translation_runs_in_the_right_direction() {
    // `(x0 | x1)` — satisfiable four ways propositionally. The theory forbids
    // all four combinations of `x0`, `x1`, so it is unsat only under the theory,
    // and each forbidden cube is a *different* pair of polarities: a translation
    // that dropped or flipped a negation would refute a different cube set and
    // could not close every branch.
    let clauses = vec![vec![
        Lit {
            var: 0,
            positive: true,
        },
        Lit {
            var: 1,
            positive: true,
        },
    ]];
    let forbidden = vec![
        vec![(0, true), (1, true)],
        vec![(0, true), (1, false)],
        vec![(0, false), (1, true)],
        vec![(0, false), (1, false)],
    ];
    let mut theory = CubeTheory::new(2, forbidden.clone(), false);
    assert!(matches!(
        solve_native(2, 2, &clauses, None, &mut theory),
        NativeSolveOutcome::Unsat
    ));
    // Dropping the `x0 & x1` cube leaves exactly one model that satisfies both
    // the clause and the theory, and the engine must FIND it. Without this the
    // assertion above would pass for a translation that refuses everything.
    let mut theory = CubeTheory::new(2, forbidden[1..].to_vec(), false);
    let outcome = solve_native(2, 2, &clauses, None, &mut theory);
    let NativeSolveOutcome::Sat(model) = outcome else {
        panic!("x0 = x1 = true satisfies the clause and violates no remaining cube: {outcome:?}");
    };
    assert_eq!(model.value(0), Some(true));
    assert_eq!(model.value(1), Some(true));
}

/// Recording is off by default, and a refutation reached that way publishes
/// NOTHING.
///
/// The distinction is the whole reason `TheorySolveOutcome::Unsat` carries an
/// `Option`: an absent artifact means "not recorded", while a present artifact
/// with `theory_lemma_count() == 0` means "nothing was assumed" and is a much
/// stronger claim. A route that read an absent artifact as the second would
/// report an unaudited refutation as an audited one.
#[test]
fn an_unrecorded_refutation_publishes_no_artifact() {
    let clauses = vec![
        vec![Lit {
            var: 0,
            positive: true,
        }],
        vec![Lit {
            var: 1,
            positive: true,
        }],
    ];
    let mut theory = CubeTheory::new(2, vec![vec![(0, true), (1, true)]], false);
    let outcome = solve_native(2, 2, &clauses, None, &mut theory);
    assert!(
        matches!(outcome, NativeSolveOutcome::Unsat),
        "the verdict is unaffected by whether a proof was recorded: {outcome:?}"
    );
    assert!(
        super::take_last_theory_refutation().is_none(),
        "no recording was asked for, so no artifact may appear"
    );
    // And the same query WITH recording does publish one, so the assertion
    // above is about the flag and not about this fixture never producing an
    // artifact at all.
    let mut theory = CubeTheory::new(2, vec![vec![(0, true), (1, true)]], false);
    let _ = super::with_artifact_recording(|| solve_native(2, 2, &clauses, None, &mut theory));
    assert!(
        super::take_last_theory_refutation().is_some(),
        "recording on must publish the artifact"
    );
}

/// An already-exhausted deadline must be `Unknown` **before** anything is
/// propagated, exactly as `CdclT::solve_inner`'s top-of-loop `timed_out()` check
/// makes it.
///
/// This is not a stylistic parity. Measured while moving `lia_theory` onto this
/// core: without the eager check the core propagated the two units of
/// `x > 0 & x < 1`, ran a `final_check` the zero-budget theory could not answer,
/// and returned `Sat`. `lia_theory` then failed to build a model and reported
/// `Unknown { kind: Incomplete }` where `CdclT` reported
/// `Unknown { kind: Timeout }` — and `dpll_lia::check_with_arith_dpll` BRANCHES
/// on that kind, so the give-up reason moved even though no verdict did. The
/// engine swap is only a swap if neither moves.
///
/// The fixture is Boolean-satisfiable and theory-refuted, so every other outcome
/// is reachable: without the check this returns `Unsat`, which is what makes the
/// assertion discriminating rather than vacuous.
#[test]
fn an_exhausted_deadline_is_unknown_before_any_propagation() {
    let clauses = vec![
        vec![Lit {
            var: 0,
            positive: true,
        }],
        vec![Lit {
            var: 1,
            positive: true,
        }],
    ];
    let mut theory = CubeTheory::new(2, vec![vec![(0, true), (1, true)]], false);
    let past = std::time::Instant::now() - std::time::Duration::from_secs(1);
    let outcome = solve_native(2, 2, &clauses, Some(past), &mut theory);
    assert!(
        matches!(outcome, NativeSolveOutcome::Unknown),
        "an exhausted budget must not reach the search: {outcome:?}"
    );
    assert!(
        super::take_last_theory_refutation().is_none(),
        "nothing ran, so nothing may be published as this query's refutation"
    );

    // The control: the SAME fixture with no deadline is refuted, so the
    // assertion above is about the deadline and not about a theory that cannot
    // decide anything.
    let mut theory = CubeTheory::new(2, vec![vec![(0, true), (1, true)]], false);
    assert!(
        matches!(
            solve_native(2, 2, &clauses, None, &mut theory),
            NativeSolveOutcome::Unsat
        ),
        "control: without a deadline this fixture is refuted"
    );
}
