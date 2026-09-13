//! ADR-1942: a CONSTRUCTOR TERM as an uninterpreted function's datatype
//! argument.
//!
//! ADR-1935 Ackermannised `f(o)` for a datatype VARIABLE `o` and refused
//! `f(mk(a, b))` by name, because its congruence antecedent would have been a
//! plain `Op::Eq` over a constructor term and the tag/field expansion has no
//! rewrite for one. This lane builds the antecedent instead, from the two
//! axioms that make datatypes freely generated:
//!
//! * **distinctness** — `c(…) = d(…)` is `false` for `c ≠ d`;
//! * **injectivity** — `c(x₁…xₙ) = c(y₁…yₙ)` is `⋀ᵢ xᵢ = yᵢ`;
//!
//! plus the mixed case `c(x₁…xₙ) = o`, which is
//! `is_c(o) ∧ ⋀ᵢ xᵢ = sel_{c,i}(o)` — `is`/`select` over a free variable, which
//! is exactly the fragment `scan_fragment` already handles.
//!
//! # What each test here would print if the change were broken
//!
//! * `congruence_*` — `Unsupported` or `unknown` instead of `unsat`: the
//!   decomposition stopped firing, or its clauses stopped constraining
//!   anything. These are the positive controls, and without them a route that
//!   refused everything would satisfy every `sound_*` test below.
//! * `sound_*` — a decided verdict that contradicts the mathematics, in every
//!   case an `unsat` of a satisfiable query. The fragment is always entitled to
//!   refuse; it is never entitled to be wrong. Each of these was checked
//!   against `z3` and `cvc5` before it was written down.
//! * `refusal_*` — a refusal that stopped naming its own missing capability.
//!   By ADR-1920 decision 2 the message IS the product, because the DT blocker
//!   census is read off exactly these strings.
//!
//! # What the mutation run found, rather than what this file first claimed
//!
//! Two results are recorded here because they were measured and contradicted a
//! draft of this very comment (`scripts/tests/mutation_controls.py`, suite
//! `dt-constructor-arg-1942`):
//!
//! * **`sound_the_mixed_case_needs_the_tester` SURVIVED its mutation at first.**
//!   Its original query was `is-none(o) /\ p(o) /\ not p(some(1))`; with the
//!   tester deleted the antecedent is `1 = v(o)` over a field variable nothing
//!   constrains, so the search simply chose `v(o) != 1` and the query stayed
//!   `sat`. A soundness-negative test must make the wrong answer FORCED, not
//!   merely available — the `v(o) = 1` assertion is what does that, and it is
//!   the difference between a guard that is tested and one that reads as tested.
//! * **The exactness precondition is NOT what stands between this path and a
//!   wrong `unsat` today**, and
//!   `sound_a_constructor_over_an_inexact_datatype_is_not_merged_at_depth_two`
//!   does not die when it is deleted — only the refusal message test does. The
//!   reason is ADR-1930's: the relaxed equality encoding is a FREE Boolean
//!   carrying only necessary conditions, so a search looking for a model sets it
//!   FALSE (a true antecedent would force the witnesses together and contradict
//!   `p` / `not p`). The antecedent is never *forced* true, so the clause
//!   degenerates to vacuous rather than to a wrong answer. This repeats
//!   ADR-1935's finding on the variable path verbatim. What the precondition
//!   buys is that every antecedent we emit provably IS real equality — which is
//!   what makes the ADR's equisatisfiability argument reviewable — plus the
//!   census-readable message, and insurance against a change to that encoding.
//!   The `sound_*` test stays because it is the thing that would fail if the
//!   encoding ever stopped being a free Boolean.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{ConstructorId, DatatypeId, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, SolverError, solve};

fn cfg() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(10))
}

fn var_of(arena: &mut TermArena, name: &str, sort: Sort) -> TermId {
    let sym = arena.declare(name, sort).expect("declare");
    arena.var(sym)
}

/// `Color = red | green` — a field-free enum, so a constructor argument carries
/// no fields at all and only DISTINCTNESS decides the antecedent.
fn color(arena: &mut TermArena) -> (DatatypeId, ConstructorId, ConstructorId) {
    let dt = arena.declare_datatype("Color1942");
    let red = arena.add_constructor(dt, "red", &[]);
    let green = arena.add_constructor(dt, "green", &[]);
    (dt, red, green)
}

/// `Pair = mk(fst : Int, snd : Int)` — one constructor, two scalar fields, so
/// INJECTIVITY is the whole antecedent.
fn pair(arena: &mut TermArena) -> (DatatypeId, ConstructorId) {
    let dt = arena.declare_datatype("Pair1942");
    let mk = arena.add_constructor(
        dt,
        "mk",
        &[("fst".to_owned(), Sort::Int), ("snd".to_owned(), Sort::Int)],
    );
    (dt, mk)
}

/// `Opt = none | some(v : Int)` — two constructors AND a field, so the mixed
/// case needs both the tester and the field comparison.
fn opt(arena: &mut TermArena) -> (DatatypeId, ConstructorId, ConstructorId) {
    let dt = arena.declare_datatype("Opt1942");
    let none = arena.add_constructor(dt, "none", &[]);
    let some = arena.add_constructor(dt, "some", &[("v".to_owned(), Sort::Int)]);
    (dt, none, some)
}

/// `Lst = nil | cons(hd : Int, tl : Lst)` — a datatype-typed field, so its
/// expansion is NOT exact. This is the shape the precondition refuses.
fn lst(arena: &mut TermArena) -> (DatatypeId, ConstructorId, ConstructorId) {
    let dt = arena.declare_datatype("Lst1942");
    let nil = arena.add_constructor(dt, "nil", &[]);
    let cons = arena.add_constructor(
        dt,
        "cons",
        &[
            ("hd".to_owned(), Sort::Int),
            ("tl".to_owned(), Sort::Datatype(dt)),
        ],
    );
    (dt, nil, cons)
}

fn pred(arena: &mut TermArena, name: &str, dt: DatatypeId) -> axeyum_ir::FuncId {
    arena
        .declare_fun(name, &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare predicate")
}

// ------------------------------------------------- positive controls: it works

#[test]
fn congruence_over_two_equal_constructor_terms_decides_unsat() {
    // `a = 1 /\ p(mk(a, 0)) /\ not p(mk(1, 0))`. INJECTIVITY: the antecedent is
    // `a = 1 /\ 0 = 0`, which holds, so the two witnesses must agree and the
    // query is UNSAT. Before ADR-1942 the whole query was refused.
    let mut arena = TermArena::new();
    let (dt, mk) = pair(&mut arena);
    let p = pred(&mut arena, "p1942a", dt);
    let a = var_of(&mut arena, "a1942a", Sort::Int);
    let one = arena.int_const(1);
    let zero = arena.int_const(0);
    let a_is_one = arena.eq(a, one).expect("eq");
    let left = arena.construct(mk, &[a, zero]).expect("mk");
    let right = arena.construct(mk, &[one, zero]).expect("mk");
    let p_left = arena.apply(p, &[left]).expect("apply");
    let p_right = arena.apply(p, &[right]).expect("apply");
    let not_right = arena.not(p_right).expect("not");

    let got = solve(&mut arena, &[a_is_one, p_left, not_right], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "injectivity must merge two constructor terms whose fields agree: {got:?}"
    );
}

#[test]
fn congruence_between_a_constructor_and_a_variable_decides_unsat() {
    // `is-some(o) /\ v(o) = 1 /\ p(o) /\ not p(some(1))`. The MIXED case:
    // `some(1) = o` is `is-some(o) /\ 1 = v(o)`, both asserted, so the witnesses
    // must agree. UNSAT.
    let mut arena = TermArena::new();
    let (dt, _none, some) = opt(&mut arena);
    let p = pred(&mut arena, "p1942b", dt);
    let o = var_of(&mut arena, "o1942b", Sort::Datatype(dt));
    let one = arena.int_const(1);
    let is_some = arena.dt_test(some, o).expect("test");
    let v_o = arena.dt_select(some, 0, o).expect("select");
    let v_is_one = arena.eq(v_o, one).expect("eq");
    let some_one = arena.construct(some, &[one]).expect("some");
    let p_o = arena.apply(p, &[o]).expect("apply");
    let p_some_one = arena.apply(p, &[some_one]).expect("apply");
    let not_some_one = arena.not(p_some_one).expect("not");

    let got = solve(&mut arena, &[is_some, v_is_one, p_o, not_some_one], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "the mixed constructor/variable antecedent must merge here: {got:?}"
    );
}

#[test]
fn congruence_over_a_field_free_enum_constructor_decides_unsat() {
    // `o = red` asserted structurally through the tester, then `p(o)` and
    // `not p(red)`. The antecedent `red = o` is just `is-red(o)`. UNSAT.
    let mut arena = TermArena::new();
    let (dt, red, _green) = color(&mut arena);
    let p = pred(&mut arena, "p1942c", dt);
    let o = var_of(&mut arena, "o1942c", Sort::Datatype(dt));
    let is_red = arena.dt_test(red, o).expect("test");
    let red_t = arena.construct(red, &[]).expect("red");
    let p_o = arena.apply(p, &[o]).expect("apply");
    let p_red = arena.apply(p, &[red_t]).expect("apply");
    let not_red = arena.not(p_red).expect("not");

    let got = solve(&mut arena, &[is_red, p_o, not_red], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "a field-free constructor argument must merge with a variable of that tag: {got:?}"
    );
}

#[test]
fn congruence_over_a_two_argument_function_decides_unsat() {
    // Both argument positions must agree, and one of them is a constructor:
    // `q(mk(a, 0), 7)` and `q(mk(1, 0), 7)` with `a = 1`.
    let mut arena = TermArena::new();
    let (dt, mk) = pair(&mut arena);
    let q = arena
        .declare_fun("q1942d", &[Sort::Datatype(dt), Sort::Int], Sort::Bool)
        .expect("declare q");
    let a = var_of(&mut arena, "a1942d", Sort::Int);
    let one = arena.int_const(1);
    let zero = arena.int_const(0);
    let seven = arena.int_const(7);
    let a_is_one = arena.eq(a, one).expect("eq");
    let left = arena.construct(mk, &[a, zero]).expect("mk");
    let right = arena.construct(mk, &[one, zero]).expect("mk");
    let q_left = arena.apply(q, &[left, seven]).expect("apply");
    let q_right = arena.apply(q, &[right, seven]).expect("apply");
    let not_right = arena.not(q_right).expect("not");

    let got = solve(&mut arena, &[a_is_one, q_left, not_right], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "congruence must hold across both argument positions: {got:?}"
    );
}

// ------------------------------------------------ soundness: it is never wrong

#[test]
fn sound_distinct_constructors_are_not_merged() {
    // `p(red) /\ not p(green)` is SATISFIABLE — `red` and `green` are different
    // values, so `p` is free to differ. z3: sat. cvc5: sat.
    //
    // This is the DISTINCTNESS arm's soundness test. Make `congruence_arg_eq`
    // return a conjunct that is not provably false here — drop the `ca != cb`
    // arm, or let the vacuous clause be emitted with a `true` antecedent — and
    // the two witnesses are forced equal: a wrong `unsat`.
    let mut arena = TermArena::new();
    let (dt, red, green) = color(&mut arena);
    let p = pred(&mut arena, "p1942e", dt);
    let red_t = arena.construct(red, &[]).expect("red");
    let green_t = arena.construct(green, &[]).expect("green");
    let p_red = arena.apply(p, &[red_t]).expect("apply");
    let p_green = arena.apply(p, &[green_t]).expect("apply");
    let not_green = arena.not(p_green).expect("not");

    let got = solve(&mut arena, &[p_red, not_green], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "`p(red) /\\ not p(green)` is SATISFIABLE (z3, cvc5); \
         merging two distinct constructors is a wrong `unsat`: {got:?}"
    );
}

#[test]
fn sound_injectivity_does_not_merge_differing_fields() {
    // `p(mk(1, 0)) /\ not p(mk(2, 0))` is SATISFIABLE. z3: sat. cvc5: sat.
    //
    // This is the INJECTIVITY arm's soundness test. Skip the field loop in
    // `congruence_arg_eq` — or compare only the first field — and the antecedent
    // becomes `true`, forcing `p` to agree on two different pairs.
    let mut arena = TermArena::new();
    let (dt, mk) = pair(&mut arena);
    let p = pred(&mut arena, "p1942f", dt);
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let zero = arena.int_const(0);
    let left = arena.construct(mk, &[one, zero]).expect("mk");
    let right = arena.construct(mk, &[two, zero]).expect("mk");
    let p_left = arena.apply(p, &[left]).expect("apply");
    let p_right = arena.apply(p, &[right]).expect("apply");
    let not_right = arena.not(p_right).expect("not");

    let got = solve(&mut arena, &[p_left, not_right], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "`p(mk(1,0)) /\\ not p(mk(2,0))` is SATISFIABLE (z3, cvc5): {got:?}"
    );
}

#[test]
fn sound_the_mixed_case_needs_the_tester() {
    // `is-none(o) /\ v(o) = 1 /\ p(o) /\ not p(some(1))` is SATISFIABLE — `o` is
    // `none`, so it is not `some(1)`, and `v(o)` off the wrong constructor is
    // UNSPECIFIED in SMT-LIB, so a model may give it 1. z3: sat. cvc5: sat.
    //
    // Drop the `is_c(other)` conjunct from `construct_eq_term` and the
    // antecedent becomes `1 = v(o)`, which the second assertion FORCES — so the
    // two witnesses are merged and the answer is a wrong `unsat`.
    //
    // **That second assertion is the whole test and was added after a mutation
    // run.** Without it the query is `is-none(o) /\ p(o) /\ not p(some(1))`, the
    // antecedent is `1 = v(o)` over a field variable nothing constrains, and the
    // search simply chooses `v(o) != 1` — so the mutation SURVIVED and the guard
    // read as untested. A soundness-negative test has to make the wrong answer
    // FORCED, not merely available.
    let mut arena = TermArena::new();
    let (dt, none, some) = opt(&mut arena);
    let p = pred(&mut arena, "p1942g", dt);
    let o = var_of(&mut arena, "o1942g", Sort::Datatype(dt));
    let is_none = arena.dt_test(none, o).expect("test");
    let one = arena.int_const(1);
    let v_o = arena.dt_select(some, 0, o).expect("select");
    let v_is_one = arena.eq(v_o, one).expect("eq");
    let some_one = arena.construct(some, &[one]).expect("some");
    let p_o = arena.apply(p, &[o]).expect("apply");
    let p_some_one = arena.apply(p, &[some_one]).expect("apply");
    let not_some_one = arena.not(p_some_one).expect("not");

    let got = solve(&mut arena, &[is_none, v_is_one, p_o, not_some_one], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "`is-none(o) /\\ v(o)=1 /\\ p(o) /\\ not p(some(1))` is SATISFIABLE \
         (z3, cvc5): `o` is `none`, so it is not `some(1)`: {got:?}"
    );
}

#[test]
fn sound_the_mixed_case_needs_every_field() {
    // `is-mk(o) /\ fst(o) = 1 /\ p(o) /\ not p(mk(1, 2))` is SATISFIABLE:
    // `snd(o)` is unconstrained and may differ from 2. z3: sat. cvc5: sat.
    //
    // Drop any field conjunct from `construct_eq_term`'s loop and the antecedent
    // is implied by what is asserted — a wrong `unsat`. The two-field datatype
    // is the point: with one field the loop cannot be partially wrong.
    let mut arena = TermArena::new();
    let (dt, mk) = pair(&mut arena);
    let p = pred(&mut arena, "p1942h", dt);
    let o = var_of(&mut arena, "o1942h", Sort::Datatype(dt));
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let is_mk = arena.dt_test(mk, o).expect("test");
    let fst_o = arena.dt_select(mk, 0, o).expect("select");
    let fst_is_one = arena.eq(fst_o, one).expect("eq");
    let mk_one_two = arena.construct(mk, &[one, two]).expect("mk");
    let p_o = arena.apply(p, &[o]).expect("apply");
    let p_mk = arena.apply(p, &[mk_one_two]).expect("apply");
    let not_mk = arena.not(p_mk).expect("not");

    let got = solve(&mut arena, &[is_mk, fst_is_one, p_o, not_mk], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "`is-mk(o) /\\ fst(o)=1 /\\ p(o) /\\ not p(mk(1,2))` is SATISFIABLE \
         (z3, cvc5) because `snd(o)` is free: {got:?}"
    );
}

#[test]
fn sound_a_constructor_over_an_inexact_datatype_is_not_merged_at_depth_two() {
    // THE SOUNDNESS-NEGATIVE TEST FOR THE EXACTNESS PRECONDITION, and unlike
    // ADR-1935's four surviving guards this one is load-bearing on the
    // constructor path. Query:
    //
    //   is-cons(x) /\ is-cons(y) /\ is-cons(tl x) /\ is-cons(tl y)
    //   /\ hd(x) = hd(y) /\ hd(tl x) = 1 /\ hd(tl y) = 2
    //   /\ p(cons(0, x)) /\ not p(cons(0, y))
    //
    // `x` and `y` agree at depth 1 and differ at depth 2, so `x != y`,
    // `cons(0,x) != cons(0,y)` and the query is SATISFIABLE. z3: sat. cvc5: sat.
    //
    // Delete the exactness check and the antecedent becomes `x = y` over a
    // datatype WITH a datatype field. `expand_datatype_equalities` opens it one
    // level, `unfold_traversals` turns the two tails into unconstrained child
    // variables, and the nested `child = child` is encoded by `build_dt_eq` as a
    // FREE Boolean — which the search sets true while the depth-2 heads differ.
    // The antecedent then holds of two values that are not equal, the witnesses
    // are forced together, and the answer is a wrong `unsat`.
    let mut arena = TermArena::new();
    let (dt, _nil, cons) = lst(&mut arena);
    let p = pred(&mut arena, "p1942i", dt);
    let x = var_of(&mut arena, "x1942i", Sort::Datatype(dt));
    let y = var_of(&mut arena, "y1942i", Sort::Datatype(dt));
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let two = arena.int_const(2);

    let is_cons_x = arena.dt_test(cons, x).expect("test");
    let is_cons_y = arena.dt_test(cons, y).expect("test");
    let tl_x = arena.dt_select(cons, 1, x).expect("select");
    let tl_y = arena.dt_select(cons, 1, y).expect("select");
    let first_tail_is_cons = arena.dt_test(cons, tl_x).expect("test");
    let second_tail_is_cons = arena.dt_test(cons, tl_y).expect("test");
    let hd_x = arena.dt_select(cons, 0, x).expect("select");
    let hd_y = arena.dt_select(cons, 0, y).expect("select");
    let heads_agree = arena.eq(hd_x, hd_y).expect("eq");
    let head_of_tail_x = arena.dt_select(cons, 0, tl_x).expect("select");
    let head_of_tail_y = arena.dt_select(cons, 0, tl_y).expect("select");
    let first_tail_head_is_one = arena.eq(head_of_tail_x, one).expect("eq");
    let second_tail_head_is_two = arena.eq(head_of_tail_y, two).expect("eq");

    let cons_x = arena.construct(cons, &[zero, x]).expect("cons");
    let cons_y = arena.construct(cons, &[zero, y]).expect("cons");
    let p_x = arena.apply(p, &[cons_x]).expect("apply");
    let p_y = arena.apply(p, &[cons_y]).expect("apply");
    let not_y = arena.not(p_y).expect("not");

    let got = solve(
        &mut arena,
        &[
            is_cons_x,
            is_cons_y,
            first_tail_is_cons,
            second_tail_is_cons,
            heads_agree,
            first_tail_head_is_one,
            second_tail_head_is_two,
            p_x,
            not_y,
        ],
        &cfg(),
    );
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "this query is SATISFIABLE (z3, cvc5): `x` and `y` differ at depth 2, so \
         `cons(0,x) != cons(0,y)` and `p` may differ. An `unsat` here is the \
         wrong-`unsat` the exactness precondition exists to prevent: {got:?}"
    );
}

// ------------------------------------------------ the refusals still say why

fn refusal_detail(got: Result<CheckResult, SolverError>) -> String {
    match got {
        Err(SolverError::Unsupported(detail)) => detail,
        other => panic!("expected an Unsupported refusal, got {other:?}"),
    }
}

#[test]
fn refusal_names_a_datatype_argument_that_is_neither_variable_nor_constructor() {
    // `p(tl(x))` — a datatype-sorted SELECT as the argument. Still refused, and
    // the message is what the blocker census reads, so it must name the shape
    // rather than repeat ADR-1935's "not a free variable".
    let mut arena = TermArena::new();
    let (dt, _nil, cons) = lst(&mut arena);
    let p = pred(&mut arena, "p1942j", dt);
    let x = var_of(&mut arena, "x1942j", Sort::Datatype(dt));
    let tl_x = arena.dt_select(cons, 1, x).expect("select");
    let p_tl = arena.apply(p, &[tl_x]).expect("apply");

    let detail = refusal_detail(solve(&mut arena, &[p_tl], &cfg()));
    assert!(
        detail.contains("neither") && detail.contains("constructor application"),
        "the refusal must name the admitted shapes, got: {detail}"
    );
}

#[test]
fn refusal_names_the_inexact_expansion_for_a_constructor_argument() {
    // A constructor argument over `Lst` reaches the EXACTNESS arm, not the shape
    // arm — which is what says the two preconditions are checked in the right
    // order and that a census can tell them apart.
    let mut arena = TermArena::new();
    let (dt, nil, cons) = lst(&mut arena);
    let p = pred(&mut arena, "p1942k", dt);
    let zero = arena.int_const(0);
    let nil_t = arena.construct(nil, &[]).expect("nil");
    let cons_t = arena.construct(cons, &[zero, nil_t]).expect("cons");
    let p_cons = arena.apply(p, &[cons_t]).expect("apply");

    let detail = refusal_detail(solve(&mut arena, &[p_cons], &cfg()));
    assert!(
        detail.contains("expansion is not exact"),
        "a constructor argument over an inexact datatype must reach the \
         exactness arm, got: {detail}"
    );
}
