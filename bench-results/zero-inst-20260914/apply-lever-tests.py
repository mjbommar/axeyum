#!/usr/bin/env python3
"""ZERO-INST -- add the Boolean-skeleton rung's tests to auto.rs.

Four tests, each aimed at one way this lever could be wrong:

  1. polarity / fail-closed              -- the mutation target
  2. the DISTINCTION from its sibling    -- ground conjuncts sat, skeleton unsat
  3. soundness-negative                  -- a sat skeleton is never refuted
  4. the abstraction's own liveness      -- it really replaces quantifiers
"""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
AUTO = ROOT / 'crates/axeyum-solver/src/auto.rs'

ANCHOR = '''    #[test]
    fn mbqi_free_int_symbol_policy_uses_exact_source_and_excludes_binders() {'''

TESTS = r'''    /// The lever's polarity, checked without touching process environment.
    ///
    /// Every spelling other than exactly `1` must be OFF. A lever that failed
    /// OPEN would run the armed arm in both halves of an A/B and report the
    /// resulting zero as a null result, which is the one outcome no later
    /// reader could distinguish from an honest negative.
    #[test]
    fn the_bool_skeleton_lever_is_off_unless_spelled_exactly() {
        assert!(parse_bool_skeleton_lever(Some("1")), "the armed spelling");
        for off in [
            None,
            Some(""),
            Some("0"),
            Some(" 1"),
            Some("1 "),
            Some("true"),
            Some("TRUE"),
            Some("yes"),
            Some("on"),
            Some("11"),
            Some("1,1"),
        ] {
            assert!(
                !parse_bool_skeleton_lever(off),
                "{off:?} must fail CLOSED to the shipped arm"
            );
        }
    }

    /// The whole reason this rung exists, as a query rather than as prose.
    ///
    /// One assertion, whose top-level conjuncts are `(=> Q R)`, `Q` and
    /// `(not R)` with `Q` quantified. Two of the three conjuncts contain a
    /// quantifier, so [`ground_subset_refutes_quantified_query`] DROPS them and
    /// is left with the satisfiable `(not R)`. The Boolean skeleton keeps the
    /// propositional structure and replaces only `Q`, giving
    /// `(A => R) and A and (not R)` — unsat.
    ///
    /// This is the adversarial fixture for the distinction the producer makes:
    /// if the two rungs could not be told apart on some query, the second one
    /// would be dead weight and this test would be measuring nothing.
    #[test]
    fn bool_skeleton_refutes_where_dropping_quantified_conjuncts_cannot() {
        let mut arena = TermArena::new();
        let r = arena.declare("skel_r", Sort::Bool).unwrap();
        let r_var = arena.var(r);
        let binder = arena.declare("skel_binder", Sort::Int).unwrap();
        let binder_variable = arena.var(binder);
        let zero = arena.int_const(0);
        let body = arena.int_ge(binder_variable, zero).unwrap();
        let quantified = arena.forall(binder, body).unwrap();

        let implication = arena.implies(quantified, r_var).unwrap();
        let not_r = arena.not(r_var).unwrap();
        let conjunction = arena.and(&[implication, quantified, not_r]).unwrap();
        let assertions = vec![conjunction];
        let config = SolverConfig::new().with_timeout(Duration::from_secs(5));

        let (skeleton, abstracted) =
            quantifier_boolean_skeleton(&mut arena, &assertions, None).expect("skeleton builds");
        assert!(
            abstracted >= 2,
            "both occurrences of the universal must be abstracted, got {abstracted}"
        );
        assert_eq!(
            contains_quantifier_within(&arena, &skeleton, None),
            Some(false),
            "the skeleton must be quantifier-free"
        );
        assert!(
            matches!(
                check_auto(&mut arena, &skeleton, &config).unwrap(),
                CheckResult::Unsat
            ),
            "the Boolean skeleton of this query is unsatisfiable"
        );

        // And the sibling, on the very same query, cannot see it.
        assert!(
            !ground_subset_refutes_quantified_query(&mut arena, &assertions, &config).unwrap(),
            "dropping every conjunct that CONTAINS a quantifier discards the refutation"
        );
    }

    /// Soundness-negative. The abstraction is a weakening, so its only possible
    /// error is a wrong `unsat`, and the query that would expose one is a
    /// SATISFIABLE skeleton. The two occurrences here are distinct universals,
    /// so nothing forces them equal and the skeleton has a model.
    #[test]
    fn bool_skeleton_does_not_refute_a_satisfiable_skeleton() {
        let mut arena = TermArena::new();
        let first_binder = arena.declare("skel_sat_a", Sort::Int).unwrap();
        let second_binder = arena.declare("skel_sat_b", Sort::Int).unwrap();
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let first_variable = arena.var(first_binder);
        let second_variable = arena.var(second_binder);
        let first_body = arena.int_ge(first_variable, zero).unwrap();
        let second_body = arena.int_ge(second_variable, one).unwrap();
        let first = arena.forall(first_binder, first_body).unwrap();
        let second = arena.forall(second_binder, second_body).unwrap();
        let not_second = arena.not(second).unwrap();
        let assertions = vec![first, not_second];

        let (skeleton, abstracted) =
            quantifier_boolean_skeleton(&mut arena, &assertions, None).expect("skeleton builds");
        assert_eq!(abstracted, 2, "two distinct universals, two atoms");
        let config = SolverConfig::new().with_timeout(Duration::from_secs(5));
        assert!(
            !matches!(
                check_auto(&mut arena, &skeleton, &config).unwrap(),
                CheckResult::Unsat
            ),
            "two unrelated opaque atoms are satisfiable; refuting them would be a wrong unsat"
        );
    }

    /// Liveness of the abstraction itself, and of the sharing rule it relies
    /// on. A quantifier-free query must abstract ZERO occurrences — if it
    /// abstracted something, the rung's `unsat` would be the ordinary
    /// quantifier-free route wearing this rung's name. And two occurrences of
    /// the SAME subterm must share one atom, because that sharing is what makes
    /// the fixture above refutable at all.
    #[test]
    fn bool_skeleton_abstracts_nothing_without_quantifiers_and_shares_by_identity() {
        let mut arena = TermArena::new();
        let x = arena.int_var("skel_live_x").unwrap();
        let zero = arena.int_const(0);
        let ground = arena.eq(x, zero).unwrap();
        let (unchanged, abstracted) =
            quantifier_boolean_skeleton(&mut arena, &[ground], None).expect("skeleton builds");
        assert_eq!(abstracted, 0, "nothing to abstract in a ground query");
        assert_eq!(unchanged, vec![ground], "a ground query is returned as-is");

        let binder = arena.declare("skel_live_binder", Sort::Int).unwrap();
        let binder_variable = arena.var(binder);
        let body = arena.int_ge(binder_variable, zero).unwrap();
        let quantified = arena.forall(binder, body).unwrap();
        let (shared, count) =
            quantifier_boolean_skeleton(&mut arena, &[quantified, quantified], None)
                .expect("skeleton builds");
        assert_eq!(count, 1, "one interned subterm is abstracted once");
        assert_eq!(
            shared[0], shared[1],
            "identical subterms must map to the SAME atom"
        );
    }

'''


def main():
    s = AUTO.read_text()
    if 'fn the_bool_skeleton_lever_is_off_unless_spelled_exactly' in s:
        print('already applied; nothing to do')
        return
    if s.count(ANCHOR) != 1:
        sys.exit(f'ABORT: anchor matched {s.count(ANCHOR)} times, expected exactly 1')
    AUTO.write_text(s.replace(ANCHOR, TESTS + ANCHOR, 1))
    print(f'patched {AUTO}')


main()
