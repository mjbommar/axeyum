//! `MaxSAT` and weighted-`MaxSAT` over Boolean soft constraints.

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{OptOutcome, max_satisfiable, max_satisfiable_weighted};

fn bool_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Bool).unwrap();
    arena.var(sym)
}

#[test]
fn unweighted_maxsat_finds_the_best_count() {
    // hard: a OR b OR c (at least one true). soft: ¬a, ¬b, ¬c (prefer false).
    // At least one must be true, so at most two negations hold -> max 2.
    let mut arena = TermArena::new();
    let a = bool_var(&mut arena, "a");
    let b = bool_var(&mut arena, "b");
    let c = bool_var(&mut arena, "c");
    let bc = arena.or(b, c).unwrap();
    let hard = arena.or(a, bc).unwrap();
    let na = arena.not(a).unwrap();
    let nb = arena.not(b).unwrap();
    let nc = arena.not(c).unwrap();

    assert_eq!(
        max_satisfiable(&mut arena, &[hard], &[na, nb, nc]).unwrap(),
        OptOutcome::Optimal(2)
    );
}

#[test]
fn weighted_maxsat_prefers_heavy_soft_constraints() {
    // Same shape, but ¬a is worth 5 and ¬b, ¬c worth 1 each. Best: keep a false
    // (weight 5) and one of b/c false -> 5 + 1 = 6.
    let mut arena = TermArena::new();
    let a = bool_var(&mut arena, "a");
    let b = bool_var(&mut arena, "b");
    let c = bool_var(&mut arena, "c");
    let bc = arena.or(b, c).unwrap();
    let hard = arena.or(a, bc).unwrap();
    let na = arena.not(a).unwrap();
    let nb = arena.not(b).unwrap();
    let nc = arena.not(c).unwrap();

    assert_eq!(
        max_satisfiable_weighted(&mut arena, &[hard], &[(na, 5), (nb, 1), (nc, 1)]).unwrap(),
        OptOutcome::Optimal(6)
    );
}

#[test]
fn all_soft_satisfiable_gives_full_count() {
    // No hard constraint conflicts with the soft ones -> all 3 hold.
    let mut arena = TermArena::new();
    let a = bool_var(&mut arena, "a");
    let b = bool_var(&mut arena, "b");
    let c = bool_var(&mut arena, "c");
    let na = arena.not(a).unwrap();
    let nb = arena.not(b).unwrap();
    let nc = arena.not(c).unwrap();
    assert_eq!(
        max_satisfiable(&mut arena, &[], &[na, nb, nc]).unwrap(),
        OptOutcome::Optimal(3)
    );
}

#[test]
fn infeasible_hard_constraints_have_no_maxsat() {
    let mut arena = TermArena::new();
    let a = bool_var(&mut arena, "a");
    let b = bool_var(&mut arena, "b");
    let na = arena.not(a).unwrap();
    let nb = arena.not(b).unwrap();
    // hard: a AND ¬a -> unsat.
    assert_eq!(
        max_satisfiable(&mut arena, &[a, na], &[nb]).unwrap(),
        OptOutcome::Infeasible
    );
}
