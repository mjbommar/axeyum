//! Craig interpolation over `QF_BV` Boolean partitions (Track 3, the bit-vector
//! analogue of the `QF_LRA` Farkas and `QF_UF` congruence interpolators).
//!
//! Each test refutes `A ∧ B`, asks [`qf_bv_interpolant`] for a Craig interpolant
//! `I`, and *independently* re-checks the three defining conditions
//! (`A ⇒ I`, `I ∧ B ⇒ ⊥`, shared vocabulary) with the `QF_BV` decider — so the
//! assurance never leans on the function's own internal verification.

use std::collections::BTreeSet;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_solver::{CheckResult, SolverConfig, check_auto, qf_bv_interpolant};

/// Declares an 8-bit bit-vector symbol and returns its variable term.
fn bv8(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::BitVec(8)).unwrap();
    arena.var(sym)
}

/// Declares a 4-bit bit-vector symbol and returns its variable term.
fn bv4(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::BitVec(4)).unwrap();
    arena.var(sym)
}

fn const8(arena: &mut TermArena, value: u128) -> TermId {
    arena.bv_const(8, value).unwrap()
}

fn eq(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    arena.eq(a, b).unwrap()
}

fn neq(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    let e = arena.eq(a, b).unwrap();
    arena.not(e).unwrap()
}

fn is_unsat(arena: &mut TermArena, assertions: &[TermId]) -> bool {
    matches!(
        check_auto(arena, assertions, &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    )
}

fn collect_symbols(arena: &TermArena, term: TermId, out: &mut BTreeSet<SymbolId>) {
    match arena.node(term) {
        TermNode::Symbol(s) => {
            out.insert(*s);
        }
        TermNode::App { args, .. } => {
            for &arg in args {
                collect_symbols(arena, arg, out);
            }
        }
        _ => {}
    }
}

fn symbols_of(arena: &TermArena, terms: &[TermId]) -> BTreeSet<SymbolId> {
    let mut out = BTreeSet::new();
    for &t in terms {
        collect_symbols(arena, t, &mut out);
    }
    out
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
    let a_syms = symbols_of(arena, a);
    let b_syms = symbols_of(arena, b);
    let i_syms = symbols_of(arena, std::slice::from_ref(&interpolant));
    for s in &i_syms {
        assert!(
            a_syms.contains(s) && b_syms.contains(s),
            "interpolant symbol must be shared between A and B"
        );
    }
}

/// A: `x = 0`, B: `x = 1` over `BitVec(8)` — a shared-variable direct
/// contradiction. The interpolant must constrain the shared `x`.
#[test]
fn shared_variable_direct_contradiction() {
    let mut arena = TermArena::new();
    let x = bv8(&mut arena, "x");
    let zero = const8(&mut arena, 0);
    let one = const8(&mut arena, 1);
    let a = vec![eq(&mut arena, x, zero)];
    let b = vec![eq(&mut arena, x, one)];

    assert!(is_unsat(&mut arena, &[a[0], b[0]]), "A ∧ B is unsat");
    let interp = qf_bv_interpolant(&mut arena, &a, &b).expect("interpolant exists");
    assert_is_interpolant(&mut arena, &a, &b, interp);
}

/// A has a *local* variable `y` that must not leak into the interpolant.
/// A: `x = 0 ∧ y = 5`, B: `x = 1`. Only `x` is shared.
#[test]
fn a_local_variable_excluded() {
    let mut arena = TermArena::new();
    let x = bv8(&mut arena, "x");
    let y = bv8(&mut arena, "y");
    let zero = const8(&mut arena, 0);
    let one = const8(&mut arena, 1);
    let five = const8(&mut arena, 5);
    let a = vec![eq(&mut arena, x, zero), eq(&mut arena, y, five)];
    let b = vec![eq(&mut arena, x, one)];

    let y_sym = arena.find_symbol("y").unwrap();
    let interp = qf_bv_interpolant(&mut arena, &a, &b).expect("interpolant exists");
    assert_is_interpolant(&mut arena, &a, &b, interp);

    let i_syms = symbols_of(&arena, std::slice::from_ref(&interp));
    assert!(
        !i_syms.contains(&y_sym),
        "A-local variable y must not appear in the interpolant"
    );
}

/// Multi-constraint case: A: `x = y`, B: `x ≠ y` over `BitVec(8)`.
/// Both `x` and `y` are shared.
#[test]
fn multi_constraint_eq_vs_neq() {
    let mut arena = TermArena::new();
    let x = bv8(&mut arena, "x");
    let y = bv8(&mut arena, "y");
    let a = vec![eq(&mut arena, x, y)];
    let b = vec![neq(&mut arena, x, y)];

    assert!(is_unsat(&mut arena, &[a[0], b[0]]), "A ∧ B is unsat");
    let interp = qf_bv_interpolant(&mut arena, &a, &b).expect("interpolant exists");
    assert_is_interpolant(&mut arena, &a, &b, interp);
}

/// A chained constraint: A: `x = 3 ∧ x = z`, B: `z = 7`. Shared vars `x`, `z`.
#[test]
fn chained_shared_constraint() {
    let mut arena = TermArena::new();
    let x = bv8(&mut arena, "x");
    let z = bv8(&mut arena, "z");
    let three = const8(&mut arena, 3);
    let seven = const8(&mut arena, 7);
    let a = vec![eq(&mut arena, x, three), eq(&mut arena, x, z)];
    let b = vec![eq(&mut arena, z, seven)];

    let interp = qf_bv_interpolant(&mut arena, &a, &b).expect("interpolant exists");
    assert_is_interpolant(&mut arena, &a, &b, interp);
}

/// A satisfiable pair must yield `None` (no interpolant for a sat conjunction).
#[test]
fn satisfiable_pair_declines() {
    let mut arena = TermArena::new();
    let x = bv8(&mut arena, "x");
    let zero = const8(&mut arena, 0);
    let zero2 = const8(&mut arena, 0);
    let a = vec![eq(&mut arena, x, zero)];
    let b = vec![eq(&mut arena, x, zero2)];

    assert!(!is_unsat(&mut arena, &[a[0], b[0]]), "A ∧ B is sat");
    assert!(
        qf_bv_interpolant(&mut arena, &a, &b).is_none(),
        "a satisfiable conjunction has no interpolant"
    );
}

/// Empty sides decline cleanly (never panic).
#[test]
fn empty_sides_decline() {
    let mut arena = TermArena::new();
    let x = bv8(&mut arena, "x");
    let zero = const8(&mut arena, 0);
    let a = vec![eq(&mut arena, x, zero)];
    assert!(qf_bv_interpolant(&mut arena, &a, &[]).is_none());
    assert!(qf_bv_interpolant(&mut arena, &[], &a).is_none());
}

/// Deterministic randomized soundness fuzz over a few `BitVec(4)` variables.
///
/// A fixed LCG (no `rand`, no clock) generates small equality/disequality
/// partitions. Whenever the combined query is unsat and an interpolant is
/// returned, all three Craig conditions are independently re-verified. We assert
/// non-zero coverage and never accept an `I` failing a condition.
#[test]
fn randomized_soundness_fuzz() {
    // 32-bit LCG (Numerical Recipes constants); fully deterministic seed.
    let mut state: u32 = 0x1234_5678;
    let mut next = |modulus: u32| -> u32 {
        state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        (state >> 8) % modulus
    };

    let mut produced = 0usize;
    for _ in 0..400 {
        let mut arena = TermArena::new();
        // Three shared 4-bit variables plus per-side locals.
        let var_x = bv4(&mut arena, "x");
        let var_y = bv4(&mut arena, "y");
        let var_w = bv4(&mut arena, "w");
        let a_local = bv4(&mut arena, "al");
        let b_local = bv4(&mut arena, "bl");
        let vars = [var_x, var_y, var_w, a_local, b_local];

        // Build a small number of equality atoms per side.
        let build_side = |arena: &mut TermArena, count: u32, next: &mut dyn FnMut(u32) -> u32| {
            let mut side = Vec::new();
            for _ in 0..count {
                let lhs = vars[next(5) as usize];
                // Either equate to another var or to a constant.
                let rhs = if next(2) == 0 {
                    vars[next(5) as usize]
                } else {
                    arena.bv_const(4, u128::from(next(16))).unwrap()
                };
                let atom = arena.eq(lhs, rhs).unwrap();
                if next(3) == 0 {
                    side.push(arena.not(atom).unwrap());
                } else {
                    side.push(atom);
                }
            }
            side
        };

        let a_count = 1 + next(3);
        let b_count = 1 + next(3);
        let side_a = build_side(&mut arena, a_count, &mut next);
        let side_b = build_side(&mut arena, b_count, &mut next);

        let mut combined = side_a.clone();
        combined.extend_from_slice(&side_b);
        if !is_unsat(&mut arena, &combined) {
            continue;
        }

        if let Some(interp) = qf_bv_interpolant(&mut arena, &side_a, &side_b) {
            // Independently re-verify all three conditions (do not trust the fn).
            let not_i = arena.not(interp).unwrap();
            let mut a_not_i = side_a.clone();
            a_not_i.push(not_i);
            assert!(is_unsat(&mut arena, &a_not_i), "fuzz: A ∧ ¬I must be unsat");

            let mut i_b = vec![interp];
            i_b.extend_from_slice(&side_b);
            assert!(is_unsat(&mut arena, &i_b), "fuzz: I ∧ B must be unsat");

            let a_syms = symbols_of(&arena, &side_a);
            let b_syms = symbols_of(&arena, &side_b);
            let i_syms = symbols_of(&arena, std::slice::from_ref(&interp));
            for s in &i_syms {
                assert!(
                    a_syms.contains(s) && b_syms.contains(s),
                    "fuzz: interpolant symbol must be shared"
                );
            }
            produced += 1;
        }
    }

    assert!(
        produced > 0,
        "fuzz must produce at least one verified interpolant"
    );
}

// --- Certified single-predicate QF_BV Craig interpolant (qf_bv_interpolant_certified) ---
//
// The certificate carries the *same* verified interpolant plus two bit-blast
// refutations (of `A ∧ ¬I` and `I ∧ B`) for an external Carcara cross-check. These
// unit tests cover the parts that do not need the Carcara binary: the cert's
// interpolant is byte-identical to the plain path's, the three Craig conditions still
// hold, and a compound (tree) interpolant declines to the `Validated` path.

/// A single-predicate interpolant (`A: x=y`, `B: x≠y` ⟹ `I = (x=y)`) certifies: the
/// certificate exists, its interpolant equals the plain `qf_bv_interpolant` output,
/// and the carried `A ∧ ¬I` / `I ∧ B` conjunctions are independently unsat.
#[test]
fn certified_single_predicate_interpolant_matches_and_refutes() {
    use axeyum_solver::qf_bv_interpolant_certified;
    let mut arena = TermArena::new();
    let x = bv8(&mut arena, "x");
    let y = bv8(&mut arena, "y");
    let a = vec![eq(&mut arena, x, y)];
    let b = vec![neq(&mut arena, x, y)];

    let plain = qf_bv_interpolant(&mut arena, &a, &b).expect("plain interpolant exists");
    let cert = qf_bv_interpolant_certified(&mut arena, &a, &b)
        .expect("decides")
        .expect("a certified interpolant exists");

    // Byte-identical interpolant term: the cert reuses the shared builder.
    assert_eq!(
        cert.interpolant, plain,
        "certified interpolant must equal the plain qf_bv_interpolant output"
    );
    // The carried interpolant is still a genuine Craig interpolant (all 3 conditions).
    assert_is_interpolant(&mut arena, &a, &b, cert.interpolant);
    // The carried conjunctions the refutations witness are independently unsat.
    assert!(
        is_unsat(&mut arena, &cert.a_and_not_i),
        "A ∧ ¬I must be unsat"
    );
    assert!(is_unsat(&mut arena, &cert.i_and_b), "I ∧ B must be unsat");
    assert!(
        !cert.a_refutation.is_empty() && !cert.b_refutation.is_empty(),
        "both refutations must carry steps"
    );
}

/// A compound (Boolean-tree) interpolant — here `A: x=0`, `B: x=1`, whose lifted
/// interpolant is an `and` of `extract`-predicates — is outside the Carcara-checked
/// emitter's flat-predicate fragment, so the certified path declines (`Ok(None)`)
/// while the plain `Validated` path still returns an interpolant.
#[test]
fn compound_interpolant_declines_certification() {
    use axeyum_solver::qf_bv_interpolant_certified;
    let mut arena = TermArena::new();
    let x = bv8(&mut arena, "x");
    let zero = const8(&mut arena, 0);
    let one = const8(&mut arena, 1);
    let a = vec![eq(&mut arena, x, zero)];
    let b = vec![eq(&mut arena, x, one)];

    // The Validated path still produces a (compound) interpolant.
    let plain = qf_bv_interpolant(&mut arena, &a, &b).expect("plain interpolant exists");
    assert!(
        matches!(arena.node(plain), TermNode::App { .. }),
        "this instance's interpolant is a compound Boolean term"
    );
    // The certified path declines it (out of the emittable single-predicate slice).
    assert!(
        qf_bv_interpolant_certified(&mut arena, &a, &b)
            .expect("decides")
            .is_none(),
        "a compound (tree) interpolant must decline certification"
    );
}

/// A satisfiable conjunction has no interpolant, so the certified path declines too.
#[test]
fn satisfiable_pair_declines_certification() {
    use axeyum_solver::qf_bv_interpolant_certified;
    let mut arena = TermArena::new();
    let x = bv8(&mut arena, "x");
    let zero = const8(&mut arena, 0);
    let a = vec![eq(&mut arena, x, zero)];
    let b = vec![eq(&mut arena, x, zero)];
    assert!(!is_unsat(&mut arena, &[a[0], b[0]]), "A ∧ B is sat");
    assert!(
        qf_bv_interpolant_certified(&mut arena, &a, &b)
            .expect("decides")
            .is_none(),
        "a satisfiable conjunction certifies no interpolant"
    );
}
