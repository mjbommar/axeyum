//! Disjunctive (CNF) Craig interpolation over `QF_LRA` (Track 3, the
//! interpolating-SMT companion of the conjunctive Farkas interpolator).
//!
//! Each test refutes a partition `A ∧ B` whose members may carry Boolean
//! structure over linear-real atoms, asks [`lra_interpolant_cnf`] for a Craig
//! interpolant `I`, and *independently* re-checks the three defining conditions
//! (`A ⇒ I`, `I ∧ B ⇒ ⊥`, shared vocabulary) with the disjunctive decider
//! [`check_auto`] — so the assurance never leans on the function's own internal
//! verification.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use std::collections::BTreeSet;

use axeyum_ir::{Rational, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_solver::{CheckResult, SolverConfig, check_auto, lra_interpolant_cnf};

/// `name` as a fresh real symbol + its variable term.
fn real_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Real).unwrap();
    arena.var(sym)
}

fn rconst(arena: &mut TermArena, n: i128) -> TermId {
    arena.real_const(Rational::integer(n))
}

/// `A ∧ B` (as one assertion slice) is unsat under the disjunctive decider.
fn is_unsat(arena: &mut TermArena, assertions: &[TermId]) -> bool {
    matches!(
        check_auto(arena, assertions, &SolverConfig::default()).expect("QF_LRA decides"),
        CheckResult::Unsat
    )
}

fn symbols_of(arena: &TermArena, term: TermId, out: &mut BTreeSet<SymbolId>) {
    match arena.node(term) {
        TermNode::Symbol(s) => {
            out.insert(*s);
        }
        TermNode::App { args, .. } => {
            for &arg in args {
                symbols_of(arena, arg, out);
            }
        }
        _ => {}
    }
}

/// Independently verifies that `interpolant` is a genuine Craig interpolant for
/// the partition `(a, b)`: `A ⇒ I`, `I ∧ B ⇒ ⊥`, and `I`'s symbols are shared.
fn assert_is_interpolant(arena: &mut TermArena, a: &[TermId], b: &[TermId], interpolant: TermId) {
    // (1) A ⇒ I  ≡  A ∧ ¬I unsat.
    let not_i = arena.not(interpolant).unwrap();
    let mut a_not_i = a.to_vec();
    a_not_i.push(not_i);
    assert!(is_unsat(arena, &a_not_i), "A ∧ ¬I must be unsat (A ⇒ I)");

    // (2) I ∧ B unsat.
    let mut i_b = vec![interpolant];
    i_b.extend_from_slice(b);
    assert!(is_unsat(arena, &i_b), "I ∧ B must be unsat");

    // (3) Vocabulary: I's symbols ⊆ symbols(A) ∩ symbols(B).
    let mut a_syms = BTreeSet::new();
    for &t in a {
        symbols_of(arena, t, &mut a_syms);
    }
    let mut b_syms = BTreeSet::new();
    for &t in b {
        symbols_of(arena, t, &mut b_syms);
    }
    let mut i_syms = BTreeSet::new();
    symbols_of(arena, interpolant, &mut i_syms);
    for s in &i_syms {
        assert!(
            a_syms.contains(s) && b_syms.contains(s),
            "interpolant uses a non-shared symbol"
        );
    }
}

/// A genuinely **disjunctive** A that the conjunctive `lra_interpolant`
/// declines, but the CNF construction handles:
///
/// A: `(x ≤ 1 ∨ x ≥ 3) ∧ x ≤ 3 ∧ x ≥ 1`  (so `x ∈ {1} ∪ {3}` within `[1, 3]`),
/// B: `x = 2`. `A ∧ B` is unsat, and the contradiction lives entirely within
/// the shared variable `x`.
#[test]
fn disjunctive_a_with_equality_b() {
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let one = rconst(&mut arena, 1);
    let three = rconst(&mut arena, 3);
    let two = rconst(&mut arena, 2);

    let x_le_1 = arena.real_le(x, one).unwrap();
    let x_ge_3 = arena.real_ge(x, three).unwrap();
    let split = arena.or(x_le_1, x_ge_3).unwrap();
    let x_le_3 = arena.real_le(x, three).unwrap();
    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let a = [split, x_le_3, x_ge_1];

    let x_eq_2 = arena.eq(x, two).unwrap();
    let b = [x_eq_2];

    // Sanity: A ∧ B is unsat.
    let mut both = a.to_vec();
    both.extend_from_slice(&b);
    assert!(is_unsat(&mut arena, &both), "A ∧ B should be unsat");

    let interp = lra_interpolant_cnf(&mut arena, &a, &b)
        .expect("interpolation does not error")
        .expect("a disjunctive interpolant exists");
    assert_is_interpolant(&mut arena, &a, &b, interp);
}

/// A second disjunctive shape: the case-split sits in `A` and the bounds in
/// `B`. A: `(x ≤ 0 ∨ x ≥ 4)`, B: `x ≥ 1 ∧ x ≤ 3`. `A ∧ B` is unsat (B pins `x`
/// strictly between the two disjuncts).
#[test]
fn disjunctive_a_conjunctive_b() {
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = rconst(&mut arena, 0);
    let four = rconst(&mut arena, 4);
    let one = rconst(&mut arena, 1);
    let three = rconst(&mut arena, 3);

    let x_le_0 = arena.real_le(x, zero).unwrap();
    let x_ge_4 = arena.real_ge(x, four).unwrap();
    let split = arena.or(x_le_0, x_ge_4).unwrap();
    let a = [split];

    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let x_le_3 = arena.real_le(x, three).unwrap();
    let b = [x_ge_1, x_le_3];

    let mut both = a.to_vec();
    both.extend_from_slice(&b);
    assert!(is_unsat(&mut arena, &both), "A ∧ B should be unsat");

    let interp = lra_interpolant_cnf(&mut arena, &a, &b)
        .expect("interpolation does not error")
        .expect("a disjunctive interpolant exists");
    assert_is_interpolant(&mut arena, &a, &b, interp);
}

/// Regression: a purely **conjunctive** partition still interpolates. A: `x ≤ 0`
/// over a shared `x`; B: `x ≥ 1`. The refuting theory lemma here is *mixed*
/// (couples the A-only atom `x ≤ 0` with the B-only atom `x ≥ 1`), so this also
/// exercises the Farkas purification path.
#[test]
fn conjunctive_regression() {
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = rconst(&mut arena, 0);
    let one = rconst(&mut arena, 1);

    let x_le_0 = arena.real_le(x, zero).unwrap();
    let a = [x_le_0];
    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let b = [x_ge_1];

    let interp = lra_interpolant_cnf(&mut arena, &a, &b)
        .expect("interpolation does not error")
        .expect("a conjunctive interpolant exists");
    assert_is_interpolant(&mut arena, &a, &b, interp);
}

/// A **satisfiable** partition yields `None` (no interpolant exists).
#[test]
fn satisfiable_partition_declines() {
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = rconst(&mut arena, 0);
    let ten = rconst(&mut arena, 10);

    let x_le_0 = arena.real_le(x, zero).unwrap();
    let x_ge_10 = arena.real_ge(x, ten).unwrap();
    let split = arena.or(x_le_0, x_ge_10).unwrap();
    let a = [split];

    let five = rconst(&mut arena, 5);
    let x_le_5 = arena.real_le(x, five).unwrap();
    let b = [x_le_5]; // x = -1 (say) satisfies A ∧ B.

    let mut both = a.to_vec();
    both.extend_from_slice(&b);
    assert!(!is_unsat(&mut arena, &both), "A ∧ B should be sat");

    assert!(
        lra_interpolant_cnf(&mut arena, &a, &b)
            .expect("interpolation does not error")
            .is_none(),
        "a satisfiable partition must yield None"
    );
}

/// A partition whose refutation needs a **mixed** theory lemma (a Farkas
/// combination spanning an A-side and a B-side atom over distinct variables).
/// The construction must either return a verified interpolant or a clean `None`
/// — never a wrong answer. A: `x + y ≤ 0`; B: `y ≥ 0 ∧ x ≥ 1`. `A ∧ B` is unsat
/// (`x ≥ 1`, `y ≥ 0` force `x + y ≥ 1 > 0`), and the refutation couples the
/// shared `x`/`y` through a Farkas combination.
#[test]
fn mixed_lemma_is_sound_or_none() {
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let y = real_var(&mut arena, "y");
    let zero = rconst(&mut arena, 0);
    let one = rconst(&mut arena, 1);

    let x_plus_y = arena.real_add(x, y).unwrap();
    let a_atom = arena.real_le(x_plus_y, zero).unwrap(); // x + y ≤ 0
    let a = [a_atom];

    let y_ge_0 = arena.real_ge(y, zero).unwrap();
    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let b = [y_ge_0, x_ge_1];

    let mut both = a.to_vec();
    both.extend_from_slice(&b);
    assert!(is_unsat(&mut arena, &both), "A ∧ B should be unsat");

    let result = lra_interpolant_cnf(&mut arena, &a, &b).expect("interpolation does not error");
    if let Some(interp) = result {
        assert_is_interpolant(&mut arena, &a, &b, interp);
    }
    // `None` is an acceptable (sound) outcome for the mixed-lemma boundary.
}

/// Deterministic LCG fuzz: random small CNF-over-LRA-atom partitions. When the
/// partition is `check_auto`-unsat and an interpolant is returned, independently
/// re-verify the three Craig conditions. Never unsound; nonzero coverage.
#[test]
fn lcg_fuzz_disjunctive_interpolants() {
    // A reproducible linear-congruential generator (no rand/clock).
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            // Numerical Recipes LCG constants.
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            self.0
        }
        fn below(&mut self, bound: u64) -> u64 {
            self.next() % bound
        }
    }

    // A random linear-real order atom over a chosen variable: `v ⋈ c`, with a
    // small constant so a pair of partitions conflicts often.
    fn random_atom(arena: &mut TermArena, rng: &mut Lcg, vars: &[TermId]) -> TermId {
        // Bias toward `vars[0]` (the shared variable) so partitions conflict
        // often; the remaining variables (side-private) appear less frequently.
        let pick = if vars.len() <= 1 || rng.below(3) != 0 {
            0
        } else {
            let bound = u64::try_from(vars.len() - 1).expect("var count fits in u64");
            usize::try_from(1 + rng.below(bound)).expect("index fits in usize")
        };
        let v = vars[pick];
        let c = i128::from(rng.below(5)) - 2; // constant in [-2, 2].
        let cst = rconst(arena, c);
        match rng.below(4) {
            0 => arena.real_le(v, cst).unwrap(),
            1 => arena.real_ge(v, cst).unwrap(),
            2 => arena.real_lt(v, cst).unwrap(),
            _ => arena.real_gt(v, cst).unwrap(),
        }
    }

    // A small CNF-ish assertion: a single clause `atom ∨ atom` or a bare atom.
    fn random_assertion(arena: &mut TermArena, rng: &mut Lcg, vars: &[TermId]) -> TermId {
        if rng.below(3) == 0 {
            let l = random_atom(arena, rng, vars);
            let r = random_atom(arena, rng, vars);
            arena.or(l, r).unwrap()
        } else {
            random_atom(arena, rng, vars)
        }
    }

    let mut rng = Lcg(0x1234_5678_9abc_def0);
    let mut interpolants_found = 0usize;
    let mut unsat_cases = 0usize;

    for _ in 0..600 {
        let mut arena = TermArena::new();
        // `x` is shared (forces conflicts); `p` is A-private, `q` is B-private
        // (so interpolants are non-trivial and mixed theory lemmas arise).
        let x = real_var(&mut arena, "x");
        let p = real_var(&mut arena, "p");
        let q = real_var(&mut arena, "q");
        let a_vars = [x, p];
        let b_vars = [x, q];

        let a: Vec<TermId> = (0..2 + rng.below(2))
            .map(|_| random_assertion(&mut arena, &mut rng, &a_vars))
            .collect();
        let b: Vec<TermId> = (0..2 + rng.below(2))
            .map(|_| random_assertion(&mut arena, &mut rng, &b_vars))
            .collect();

        // Only interpolate genuine refutations.
        let mut both = a.clone();
        both.extend_from_slice(&b);
        if !is_unsat(&mut arena, &both) {
            continue;
        }
        unsat_cases += 1;

        if let Some(interp) =
            lra_interpolant_cnf(&mut arena, &a, &b).expect("interpolation does not error")
        {
            // Independent re-verification — this is the soundness gate.
            assert_is_interpolant(&mut arena, &a, &b, interp);
            interpolants_found += 1;
        }
    }

    assert!(unsat_cases > 0, "fuzz produced no unsat partitions");
    assert!(
        interpolants_found > 0,
        "fuzz produced no verified interpolants (coverage check)"
    );
}
