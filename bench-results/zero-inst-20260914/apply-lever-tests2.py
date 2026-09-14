#!/usr/bin/env python3
"""ZERO-INST -- the two tests that make the surviving guards load-bearing.

Both were written because `mutation_controls.py` said, in its own output, that
nothing depended on the guard.
"""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
AUTO = ROOT / 'crates/axeyum-solver/src/auto.rs'

ANCHOR = '''    #[test]
    fn mbqi_free_int_symbol_policy_uses_exact_source_and_excludes_binders() {'''

TESTS = r'''    /// The liveness floor, reached through the ARMED body so the OFF lever
    /// cannot make the test vacuous.
    ///
    /// A query with no quantifiers abstracts nothing, so this rung must decline
    /// it even though it is unsatisfiable. Without the floor the rung would
    /// report `unsat` on a query the ordinary quantifier-free dispatch decided,
    /// and every row it "won" would be a route-attribution error rather than a
    /// new verdict.
    #[test]
    fn bool_skeleton_declines_a_query_it_abstracted_nothing_in() {
        let mut arena = TermArena::new();
        let x = arena.int_var("skel_floor_x").unwrap();
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let x_is_zero = arena.eq(x, zero).unwrap();
        let x_is_one = arena.eq(x, one).unwrap();
        let assertions = vec![x_is_zero, x_is_one];
        let config = SolverConfig::new().with_timeout(Duration::from_secs(5));

        // The query really is refutable, so declining it is a decision and not
        // an accident of the query being satisfiable.
        assert!(
            matches!(
                check_auto(&mut arena, &assertions, &config).unwrap(),
                CheckResult::Unsat
            ),
            "control: this ground query IS unsat"
        );
        assert!(
            !skeleton_refutes_quantified_query_armed(&mut arena, &assertions, &config).unwrap(),
            "a query with no quantifier to abstract is not this rung's to claim"
        );
    }

    /// Maximality — the property the abstraction's soundness rests on.
    ///
    /// `forall x. exists y. y >= x` contains two quantifiers, one nested inside
    /// the other. Exactly ONE subterm may be abstracted: the outermost. The
    /// inner `exists y. y >= x` varies with the bound `x`, so replacing it with
    /// a constant is not a weakening and could manufacture a wrong `unsat`.
    #[test]
    fn bool_skeleton_abstracts_only_the_outermost_quantifier() {
        let mut arena = TermArena::new();
        let outer = arena.declare("skel_max_outer", Sort::Int).unwrap();
        let inner = arena.declare("skel_max_inner", Sort::Int).unwrap();
        let outer_variable = arena.var(outer);
        let inner_variable = arena.var(inner);
        let body = arena.int_ge(inner_variable, outer_variable).unwrap();
        let existential = arena.exists(inner, body).unwrap();
        let universal = arena.forall(outer, existential).unwrap();

        let (skeleton, abstracted) =
            quantifier_boolean_skeleton(&mut arena, &[universal], None).expect("skeleton builds");
        assert_eq!(
            abstracted, 1,
            "only the OUTERMOST quantifier may be abstracted; the nested one \
             varies with the bound variable and a constant cannot track it"
        );
        assert_eq!(
            contains_quantifier_within(&arena, &skeleton, None),
            Some(false),
            "replacing the outermost quantifier removes the nested one with it"
        );
    }

'''


def main():
    s = AUTO.read_text()
    if 'fn bool_skeleton_abstracts_only_the_outermost_quantifier' in s:
        print('already applied; nothing to do')
        return
    if s.count(ANCHOR) != 1:
        sys.exit(f'ABORT: anchor matched {s.count(ANCHOR)} times, expected 1')
    AUTO.write_text(s.replace(ANCHOR, TESTS + ANCHOR, 1))
    print(f'patched {AUTO}')


main()
