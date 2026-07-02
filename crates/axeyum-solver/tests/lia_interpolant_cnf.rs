//! Disjunctive (CNF) Craig interpolation over `QF_LIA` (Track 3, the integer
//! mirror of the disjunctive real interpolator).
//!
//! Each test refutes an integer partition `A ∧ B` whose members may carry
//! Boolean structure over linear-integer atoms, asks [`lia_interpolant_cnf`]
//! for a Craig interpolant `I`, and *independently* re-checks the three
//! defining conditions (`A ⇒ I`, `I ∧ B ⇒ ⊥`, shared vocabulary) over ℤ with
//! the disjunctive integer decider [`check_with_lia_dpll`] — so the assurance
//! never leans on the function's own internal verification.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use std::collections::BTreeSet;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_solver::{CheckResult, SolverConfig, check_with_lia_dpll, lia_interpolant_cnf};

/// `name` as a fresh integer symbol + its variable term.
fn int_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Int).unwrap();
    arena.var(sym)
}

fn iconst(arena: &mut TermArena, n: i128) -> TermId {
    arena.int_const(n)
}

/// `A ∧ B` (as one assertion slice) is unsat under the disjunctive integer
/// decider.
fn is_unsat(arena: &mut TermArena, assertions: &[TermId]) -> bool {
    matches!(
        check_with_lia_dpll(arena, assertions, &SolverConfig::default()).expect("QF_LIA decides"),
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
/// the integer partition `(a, b)`: `A ⇒ I`, `I ∧ B ⇒ ⊥`, and `I`'s symbols are
/// shared. Every re-check is over ℤ via [`check_with_lia_dpll`].
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

    // (3) Shared vocabulary: every symbol of I occurs in both A and B.
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
        assert!(a_syms.contains(s), "interpolant symbol must be in A");
        assert!(b_syms.contains(s), "interpolant symbol must be in B");
    }
}

/// A genuinely **disjunctive** integer unsat: `A = (x ≤ 0 ∨ x ≥ 10)`,
/// `B = (x = 5)`. The conjunctive `lia_interpolant` cannot handle the
/// `∨`-structure of `A`; the CNF construction can.
#[test]
fn disjunctive_integer_interpolant() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let ten = iconst(&mut arena, 10);
    let five = iconst(&mut arena, 5);

    // A = (x ≤ 0 ∨ x ≥ 10).
    let x_le_0 = arena.int_le(x, zero).unwrap();
    let x_ge_10 = arena.int_ge(x, ten).unwrap();
    let a0 = arena.or(x_le_0, x_ge_10).unwrap();
    let a = vec![a0];

    // B = (x = 5).
    let b0 = arena.eq(x, five).unwrap();
    let b = vec![b0];

    // Sanity: A ∧ B is unsat over ℤ.
    let mut both = a.clone();
    both.extend_from_slice(&b);
    assert!(is_unsat(&mut arena, &both), "A ∧ B must be unsat");

    let interpolant = lia_interpolant_cnf(&mut arena, &a, &b)
        .expect("no solver error")
        .expect("a disjunctive integer interpolant exists");
    assert_is_interpolant(&mut arena, &a, &b, interpolant);
}

/// A two-atom Boolean combination forcing a contradiction, over a shared `x`
/// with an `A`-local `y`: `A = (x ≥ 3 ∧ (y ≤ 0 ∨ y ≥ 0))`, `B = (x ≤ 1)`.
#[test]
fn shared_and_a_local_vocabulary() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y"); // A-local only.
    let zero = iconst(&mut arena, 0);
    let one = iconst(&mut arena, 1);
    let three = iconst(&mut arena, 3);

    // A = (x ≥ 3) ∧ (y ≤ 0 ∨ y ≥ 0).  The y-disjunction is a tautology, so A
    // collapses to x ≥ 3, but the structure exercises the abstraction.
    let x_ge_3 = arena.int_ge(x, three).unwrap();
    let y_le_0 = arena.int_le(y, zero).unwrap();
    let y_ge_0 = arena.int_ge(y, zero).unwrap();
    let y_taut = arena.or(y_le_0, y_ge_0).unwrap();
    let a0 = arena.and(x_ge_3, y_taut).unwrap();
    let a = vec![a0];

    // B = (x ≤ 1).
    let b0 = arena.int_le(x, one).unwrap();
    let b = vec![b0];

    let mut both = a.clone();
    both.extend_from_slice(&b);
    assert!(is_unsat(&mut arena, &both), "A ∧ B must be unsat");

    let interpolant = lia_interpolant_cnf(&mut arena, &a, &b)
        .expect("no solver error")
        .expect("an integer interpolant exists");
    assert_is_interpolant(&mut arena, &a, &b, interpolant);

    // The A-local symbol `y` must NOT appear in the interpolant.
    let y_sym = match arena.node(y) {
        TermNode::Symbol(s) => *s,
        _ => unreachable!(),
    };
    let mut i_syms = BTreeSet::new();
    symbols_of(&arena, interpolant, &mut i_syms);
    assert!(
        !i_syms.contains(&y_sym),
        "A-local symbol y must not appear in the interpolant"
    );
}

/// An `ite`-structured integer case: `A = ite(c, x ≤ 0, x ≥ 10)` with `c` a
/// fresh Boolean shared with `B`, and `B = (x = 5 ∧ c) ... ` — kept simple by
/// using a Boolean control that both sides constrain. We use
/// `A = ite(x ≥ 5, x ≤ 0, x ≥ 100)` (a real-atom condition) so the structure is
/// purely arithmetic and shared over `x`. `B = (x = 5)`.
#[test]
fn ite_structured_integer_interpolant() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let five = iconst(&mut arena, 5);
    let hundred = iconst(&mut arena, 100);

    // A = ite(x ≥ 5, x ≤ 0, x ≥ 100).  Either way x ∉ {anything near 5}.
    let cond = arena.int_ge(x, five).unwrap();
    let then_b = arena.int_le(x, zero).unwrap();
    let else_b = arena.int_ge(x, hundred).unwrap();
    let a0 = arena.ite(cond, then_b, else_b).unwrap();
    let a = vec![a0];

    // B = (x = 5).
    let b0 = arena.eq(x, five).unwrap();
    let b = vec![b0];

    let mut both = a.clone();
    both.extend_from_slice(&b);
    assert!(is_unsat(&mut arena, &both), "A ∧ B must be unsat");

    let interpolant = lia_interpolant_cnf(&mut arena, &a, &b)
        .expect("no solver error")
        .expect("an ite-structured integer interpolant exists");
    assert_is_interpolant(&mut arena, &a, &b, interpolant);
}

/// A **satisfiable** `A ∧ B` has no interpolant ⇒ `Ok(None)`.
#[test]
fn satisfiable_declines() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let ten = iconst(&mut arena, 10);

    // A = (x ≤ 0 ∨ x ≥ 10), B = (x ≥ 0).  x = 0 satisfies both.
    let x_le_0 = arena.int_le(x, zero).unwrap();
    let x_ge_10 = arena.int_ge(x, ten).unwrap();
    let a0 = arena.or(x_le_0, x_ge_10).unwrap();
    let a = vec![a0];
    let b0 = arena.int_ge(x, zero).unwrap();
    let b = vec![b0];

    assert!(
        lia_interpolant_cnf(&mut arena, &a, &b)
            .expect("no solver error")
            .is_none(),
        "satisfiable A ∧ B has no interpolant"
    );
}

/// A **cuts-needed** integer unsat whose rational relaxation is *satisfiable*:
/// `A = (2x ≥ 1 ∧ 2x ≤ 1)`, `B = (true)`. Over ℤ the only solution would need
/// `2x = 1`, impossible; over ℚ, `x = 1/2` satisfies it, so the relaxation is
/// sat and the construction declines (`Ok(None)`) — sound partial coverage,
/// NOT a wrong interpolant.
#[test]
fn cuts_needed_declines() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let two = iconst(&mut arena, 2);
    let one = iconst(&mut arena, 1);
    let two_x = arena.int_mul(two, x).unwrap();

    // A = (2x ≥ 1) ∧ (2x ≤ 1).  Integer-unsat (needs the cut 2x = 1).
    let lo = arena.int_ge(two_x, one).unwrap();
    let hi = arena.int_le(two_x, one).unwrap();
    let a0 = arena.and(lo, hi).unwrap();
    let a = vec![a0];

    // B over the shared x so vocabulary is non-trivial: x ≥ 0 (sat-compatible).
    let zero = iconst(&mut arena, 0);
    let b0 = arena.int_ge(x, zero).unwrap();
    let b = vec![b0];

    // Sanity: A ∧ B is genuinely integer-unsat.
    let mut both = a.clone();
    both.extend_from_slice(&b);
    assert!(is_unsat(&mut arena, &both), "A ∧ B is integer-unsat");

    // The relaxation is sat ⇒ the disjunctive construction declines soundly.
    assert!(
        lia_interpolant_cnf(&mut arena, &a, &b)
            .expect("no solver error")
            .is_none(),
        "cuts-needed integer unsat declines (sound partial coverage)"
    );
}

/// A tiny linear-congruential generator (no `rand` / no clock) for a
/// deterministic fuzz.
struct Lcg {
    state: u64,
}

impl Lcg {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u32(&mut self) -> u32 {
        self.state = self
            .state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        u32::try_from(self.state >> 33).unwrap_or(0)
    }
}

/// A random linear-integer order atom comparing `var` against a small constant
/// in `[-5, 5]`, so a contradiction over a shared variable is reachable.
fn fuzz_atom(arena: &mut TermArena, var: TermId, rng: &mut Lcg) -> TermId {
    let c = iconst(arena, i128::from(rng.next_u32() % 11) - 5);
    match rng.next_u32() % 4 {
        0 => arena.int_le(var, c).unwrap(),
        1 => arena.int_ge(var, c).unwrap(),
        2 => arena.int_lt(var, c).unwrap(),
        _ => arena.int_gt(var, c).unwrap(),
    }
}

/// A random Boolean tree of bounded `depth` over a side's `shared`/`local`
/// integer variables.
fn fuzz_tree(
    arena: &mut TermArena,
    shared: TermId,
    local: TermId,
    depth: u32,
    rng: &mut Lcg,
) -> TermId {
    if depth == 0 || rng.next_u32().is_multiple_of(3) {
        let var = if rng.next_u32().is_multiple_of(2) {
            shared
        } else {
            local
        };
        return fuzz_atom(arena, var, rng);
    }
    let lhs = fuzz_tree(arena, shared, local, depth - 1, rng);
    let rhs = fuzz_tree(arena, shared, local, depth - 1, rng);
    match rng.next_u32() % 3 {
        0 => arena.and(lhs, rhs).unwrap(),
        1 => arena.or(lhs, rhs).unwrap(),
        _ => {
            let n = arena.not(lhs).unwrap();
            arena.or(n, rhs).unwrap()
        }
    }
}

/// Deterministic LCG soundness fuzz: random Boolean trees over a small pool of
/// LIA atoms partitioned into `A`/`B`. Whenever a `Some(I)` is returned,
/// independently re-check all three Craig conditions over ℤ. ZERO unsound
/// interpolants; `None` is always acceptable; assert non-zero `Some` coverage.
#[test]
fn soundness_fuzz() {
    let mut rng = Lcg::new(0x9E37_79B9_7F4A_7C15);

    let mut some_count = 0usize;
    let mut none_count = 0usize;
    let mut checked = 0usize;

    for _ in 0..400 {
        let mut arena = TermArena::new();
        // Shared variable `x`; A-local `a`, B-local `b`.
        let x = int_var(&mut arena, "x");
        let av = int_var(&mut arena, "a");
        let bv = int_var(&mut arena, "b");

        let a0 = fuzz_tree(&mut arena, x, av, 2, &mut rng);
        let b0 = fuzz_tree(&mut arena, x, bv, 2, &mut rng);
        let a = vec![a0];
        let b = vec![b0];

        match lia_interpolant_cnf(&mut arena, &a, &b) {
            Ok(Some(interpolant)) => {
                some_count += 1;
                // Independent re-check of all three Craig conditions over ℤ.
                let not_i = arena.not(interpolant).unwrap();
                let mut a_not_i = a.clone();
                a_not_i.push(not_i);
                assert!(
                    is_unsat(&mut arena, &a_not_i),
                    "FUZZ: A ∧ ¬I must be unsat (A ⇒ I)"
                );
                let mut i_b = vec![interpolant];
                i_b.extend_from_slice(&b);
                assert!(is_unsat(&mut arena, &i_b), "FUZZ: I ∧ B must be unsat");

                let mut a_syms = BTreeSet::new();
                symbols_of(&arena, a0, &mut a_syms);
                let mut b_syms = BTreeSet::new();
                symbols_of(&arena, b0, &mut b_syms);
                let mut i_syms = BTreeSet::new();
                symbols_of(&arena, interpolant, &mut i_syms);
                for s in &i_syms {
                    assert!(a_syms.contains(s), "FUZZ: interpolant symbol must be in A");
                    assert!(b_syms.contains(s), "FUZZ: interpolant symbol must be in B");
                }
                checked += 1;
            }
            Ok(None) => none_count += 1,
            Err(e) => panic!("FUZZ: unexpected solver error: {e}"),
        }
    }

    println!("fuzz: some={some_count} none={none_count} verified={checked}");
    assert!(
        some_count > 0,
        "fuzz produced no Some interpolants (coverage check): some={some_count} none={none_count}"
    );
    assert_eq!(
        checked, some_count,
        "every Some interpolant must have been independently verified"
    );
}
