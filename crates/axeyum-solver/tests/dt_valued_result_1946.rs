//! ADR-1946: an uninterpreted function whose RESULT is datatype-sorted, and an
//! `Op::Apply` term as another function's datatype ARGUMENT.
//!
//! ADR-1935 refused this rung by name — "its Ackermann witness would itself be
//! a datatype-sorted term, which the tag/field expansion would have to pick up
//! in a scan that has already run". It does not have to:
//! `ackermannize_datatype_applications` runs BEFORE `scan_fragment`, so a
//! witness declared there is an ordinary free datatype variable by the time the
//! scan walks the rewritten assertions. That is the whole of this change, plus
//! the consequence that makes it usable: with `f(x)` replaced by a variable, an
//! `Op::Apply` term is admissible wherever a datatype VARIABLE is — as another
//! function's argument, and as an `is`/`select` operand.
//!
//! # What each test here would print if the change were broken
//!
//! * `congruence_*` — `Unsupported` or `unknown` instead of `unsat`. These are
//!   the positive controls, and without them a route that refused everything
//!   would satisfy every `sound_*` test below. **Each one is a shape the arm
//!   before this change answered `unknown` on**, which is checked by the base
//!   arm in the A/B rather than asserted here; a positive control that the
//!   PREVIOUS arm also decided would be measuring the ladder, not this change,
//!   and two candidates were discarded for exactly that (see
//!   `a_uf_result_under_a_selector_is_decided_by_an_earlier_rung`).
//! * `sound_*` — a decided verdict that contradicts the mathematics, in every
//!   case an `unsat` of a satisfiable query. Each was checked against `z3` AND
//!   `cvc5` before it was written down, not after it passed.
//! * `refusal_*` — a refusal that stopped naming its own missing capability. By
//!   ADR-1920 decision 2 the message IS the product, because the DT blocker
//!   census is read off exactly these strings.
//!
//! # The rule ADR-1942 paid for, applied here
//!
//! A soundness-negative test has to make the wrong answer **forced**, not merely
//! available: an unconstrained variable in the congruence antecedent gives the
//! search a free escape and the mutant survives. Each `sound_*` below says in
//! its own comment which assertion does the forcing and what the mutated
//! antecedent collapses to.
//!
//! # What the mutation run found, rather than what this file first claimed
//!
//! See `scripts/tests/mutation_controls.py`, suite `dt-valued-result-1946`, and
//! the "What the mutation run found" section of ADR-1946. Two results are worth
//! repeating where they will be read:
//!
//! * **The result-sort EXACTNESS precondition kills no soundness test**, only
//!   its refusal-message test — the third time in this series that an exactness
//!   precondition has measured as not-today's-soundness-boundary. The reason is
//!   ADR-1930's and it is structural: an `unsat` is only ever returned from the
//!   `EqMode::Relaxation` arm, whose datatype equality is weaker-or-exact, so a
//!   consequent it cannot compare exactly makes the congruence clause WEAKER
//!   than the axiom rather than stronger. What the precondition buys is that the
//!   equisatisfiability argument in the ADR is reviewable and that a change to
//!   that encoding trips over a refusal. That is worth having and it is not
//!   coverage, so it is not counted as coverage.
//! * **The array-over-a-datatype result guard occurs in 0 of the 600 measured
//!   files.** It IS reachable and IS mutation-covered — unlike ADR-1942's
//!   `reject_datatype_constructor_argument`, which no query can reach — so it is
//!   in the suite. What is NOT claimed is that the shape is one anybody has: the
//!   guard is a fence against a future widening, and "a test reaches it" and
//!   "the corpus contains it" are different facts that are reported separately
//!   rather than one being quoted as the other.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{ArraySortKey, ConstructorId, DatatypeId, Sort, TermArena, TermId};
use axeyum_solver::theories::datatypes::check_with_datatype_native;
use axeyum_solver::{CheckResult, SolverConfig, SolverError, solve};

fn cfg() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(10))
}

fn var_of(arena: &mut TermArena, name: &str, sort: Sort) -> TermId {
    let sym = arena.declare(name, sort).expect("declare");
    arena.var(sym)
}

/// `Pair = mk(fst : Int, snd : Int)` — one constructor, two scalar fields, so
/// the expansion is EXACT and a `Pair`-valued result is admissible.
fn pair(arena: &mut TermArena) -> (DatatypeId, ConstructorId) {
    let dt = arena.declare_datatype("Pair1946");
    let mk = arena.add_constructor(
        dt,
        "mk",
        &[("fst".to_owned(), Sort::Int), ("snd".to_owned(), Sort::Int)],
    );
    (dt, mk)
}

/// `Opt = none | some(v : Int)` — two constructors and a scalar field, so a tag
/// and a field both take part.
fn opt(arena: &mut TermArena) -> (DatatypeId, ConstructorId, ConstructorId) {
    let dt = arena.declare_datatype("Opt1946");
    let none = arena.add_constructor(dt, "none", &[]);
    let some = arena.add_constructor(dt, "some", &[("v".to_owned(), Sort::Int)]);
    (dt, none, some)
}

/// `Lst = nil | cons(hd : Int, tl : Lst)` — a datatype-typed field, so its
/// expansion is NOT exact. This is the shape a datatype-valued RESULT is still
/// refused over.
fn lst(arena: &mut TermArena) -> (DatatypeId, ConstructorId, ConstructorId) {
    let dt = arena.declare_datatype("Lst1946");
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

/// `name : Int -> <dt>` — the function whose RESULT is the capability.
fn producer(arena: &mut TermArena, name: &str, dt: DatatypeId) -> axeyum_ir::FuncId {
    arena
        .declare_fun(name, &[Sort::Int], Sort::Datatype(dt))
        .expect("declare producer")
}

// ------------------------------------------------- positive controls: it works

#[test]
fn congruence_over_a_uf_result_as_an_argument_decides_unsat() {
    // `a = 0 /\ p(g(a)) /\ not p(g(0))`, with `g : Int -> Pair`.
    //
    // Two Ackermann layers, which is the shape this rung is about: `g(a)` and
    // `g(0)` become datatype VARIABLES `w_ga`, `w_g0` with `a = 0 -> w_ga =
    // w_g0`; `p(g(a))` and `p(g(0))` become Booleans with `w_ga = w_g0 ->
    // w_pa = w_p0`. Both antecedents hold, so `p` must agree and the query is
    // UNSAT. The arm before ADR-1946 refused the whole query at the result
    // sort. z3 `unsat`, cvc5 `unsat`.
    let mut arena = TermArena::new();
    let (dt, _mk) = pair(&mut arena);
    let g = producer(&mut arena, "g1946a", dt);
    let p = pred(&mut arena, "p1946a", dt);
    let a = var_of(&mut arena, "a1946a", Sort::Int);
    let zero = arena.int_const(0);
    let a_is_zero = arena.eq(a, zero).expect("eq");
    let g_a = arena.apply(g, &[a]).expect("apply g");
    let g_0 = arena.apply(g, &[zero]).expect("apply g");
    let p_ga = arena.apply(p, &[g_a]).expect("apply p");
    let p_at_zero = arena.apply(p, &[g_0]).expect("apply p");
    let not_at_zero = arena.not(p_at_zero).expect("not");

    let got = solve(&mut arena, &[a_is_zero, p_ga, not_at_zero], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "congruence must propagate through BOTH Ackermann layers: {got:?}"
    );
}

#[test]
fn congruence_between_a_uf_result_and_a_constructor_term_decides_unsat() {
    // `g(0) = mk(1, 2) /\ p(g(0)) /\ not p(mk(1, 2))`.
    //
    // The ADR-1942 mixed case with a UF RESULT on one side: the antecedent is
    // `mk(1,2) = w_g0`, which `construct_eq_term` builds as
    // `is_mk(w_g0) /\ 1 = fst(w_g0) /\ 2 = snd(w_g0)` — `is`/`select` over what
    // is, after the replacement, a free variable. The asserted equality forces
    // it, so `p` must agree. UNSAT under z3 and cvc5; `unknown` on the previous
    // arm.
    let mut arena = TermArena::new();
    let (dt, mk) = pair(&mut arena);
    let g = producer(&mut arena, "g1946b", dt);
    let p = pred(&mut arena, "p1946b", dt);
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let g_0 = arena.apply(g, &[zero]).expect("apply g");
    let mk_12 = arena.construct(mk, &[one, two]).expect("mk");
    let same = arena.eq(g_0, mk_12).expect("eq");
    let p_at_zero = arena.apply(p, &[g_0]).expect("apply p");
    let p_mk = arena.apply(p, &[mk_12]).expect("apply p");
    let not_mk = arena.not(p_mk).expect("not");

    let got = solve(&mut arena, &[same, p_at_zero, not_mk], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "a UF result and a constructor term forced equal must merge: {got:?}"
    );
}

#[test]
fn a_tester_and_a_selector_over_a_uf_result_decide_unsat() {
    // `is-some(f(a)) /\ v(f(a)) = 1 /\ p(f(a)) /\ not p(some(1))`.
    //
    // This is the SECOND half of the change and the one the sizing note singled
    // out: `is`/`select` over a non-variable datatype term was 48 files' first
    // refusal, and it fires in `scan_fragment`, downstream of the pre-pass. With
    // `f(a)` replaced by a witness variable those operands are variables and the
    // scan handles them. z3 `unsat`, cvc5 `unsat`; `unknown` on the previous arm.
    let mut arena = TermArena::new();
    let (dt, _none, some) = opt(&mut arena);
    let f = producer(&mut arena, "f1946c", dt);
    let p = pred(&mut arena, "p1946c", dt);
    let a = var_of(&mut arena, "a1946c", Sort::Int);
    let one = arena.int_const(1);
    let f_a = arena.apply(f, &[a]).expect("apply f");
    let is_some = arena.dt_test(some, f_a).expect("test");
    let v_fa = arena.dt_select(some, 0, f_a).expect("select");
    let v_is_one = arena.eq(v_fa, one).expect("eq");
    let some_one = arena.construct(some, &[one]).expect("some");
    let p_fa = arena.apply(p, &[f_a]).expect("apply p");
    let p_some = arena.apply(p, &[some_one]).expect("apply p");
    let not_some = arena.not(p_some).expect("not");

    let got = solve(&mut arena, &[is_some, v_is_one, p_fa, not_some], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "`is`/`select` over a UF result must reach the expansion as a variable: {got:?}"
    );
}

#[test]
fn a_uf_result_under_a_selector_is_decided_by_an_earlier_rung() {
    // NOT a test of this change, and it is here to say so.
    //
    // `is-some(f(0)) /\ v(f(0)) = 1 /\ v(f(0)) = 2` was a candidate positive
    // control and was DISCARDED: the previous arm already answers `unsat`,
    // because to the EUF route `v(f(0))` is just an uninterpreted term and
    // `t = 1 /\ t = 2` is refuted by congruence before the datatype route is
    // consulted. Asserting `unsat` here would have measured the ladder rather
    // than this rung — the mistake ADR-1927 names — so what is pinned instead is
    // the FACT that an earlier rung decides it, which is what makes the three
    // controls above discriminating and this one not.
    let mut arena = TermArena::new();
    let (dt, _none, some) = opt(&mut arena);
    let f = producer(&mut arena, "f1946d", dt);
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let f_0 = arena.apply(f, &[zero]).expect("apply f");
    let is_some = arena.dt_test(some, f_0).expect("test");
    let v_f0 = arena.dt_select(some, 0, f_0).expect("select");
    let is_one = arena.eq(v_f0, one).expect("eq");
    let is_two = arena.eq(v_f0, two).expect("eq");

    let got = solve(&mut arena, &[is_some, is_one, is_two], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "an earlier rung is expected to decide this; if it stops doing so, this \
         test's COMMENT is what needs revisiting, not the assertion: {got:?}"
    );
}

#[test]
fn a_nested_application_replays_its_model() {
    // `p(g(a)) /\ not p(g(b))` — SAT, and the point of this test is the word
    // SAT rather than "not unsat".
    //
    // `p(g(a))` collects BOTH `g(a)` and `p(g(a))`, and the replay rebuilds each
    // Ackermannised function from its witness values by EVALUATING that site's
    // arguments — so `g` has to be rebuilt before `p`'s argument list is
    // evaluated, or `p` is defined at the key `g`'s constant default gives,
    // the replay against the original assertions fails, and the candidate is
    // thrown away as `unknown`. `groups` is keyed by `FuncId`, which is
    // declaration order, so `ack_sites` is sorted by `TermId` — bottom-up in a
    // hash-consed arena — to put the nested site first.
    //
    // **`p` is declared BEFORE `g` here on purpose.** With the declaration order
    // reversed the `FuncId` order already happens to be the right one and the
    // sort is a no-op, so a test written the other way round would pass with the
    // sort removed. Getting this wrong costs a `sat`, never soundness, which is
    // why this is a positive control and not a `sound_*` test.
    let mut arena = TermArena::new();
    let (dt, _mk) = pair(&mut arena);
    let p = pred(&mut arena, "p1946n", dt);
    let g = producer(&mut arena, "g1946n", dt);
    let a = var_of(&mut arena, "a1946n", Sort::Int);
    let b = var_of(&mut arena, "b1946n", Sort::Int);
    let g_a = arena.apply(g, &[a]).expect("apply g");
    let g_b = arena.apply(g, &[b]).expect("apply g");
    let p_ga = arena.apply(p, &[g_a]).expect("apply p");
    let p_at_b = arena.apply(p, &[g_b]).expect("apply p");
    let not_at_b = arena.not(p_at_b).expect("not");

    let got = solve(&mut arena, &[p_ga, not_at_b], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Sat(_))),
        "the nested site must be rebuilt before the site that reads it, or this \
         `sat` candidate fails its replay and is thrown away: {got:?}"
    );
}

// -------------------------------------------------- soundness: no wrong `unsat`

#[test]
fn sound_two_results_at_different_arguments_are_not_merged() {
    // `is-some(f(1)) /\ is-none(f(2))` — SATISFIABLE (z3, cvc5): `f` may return
    // different values at 1 and 2.
    //
    // WHAT FORCES THE WRONG ANSWER. The congruence antecedent here is the
    // ground-false `1 = 2`. Any mutation that trivialises it to `true` yields
    // `w_f1 = w_f2` unconditionally, and then `is-some(w) /\ is-none(w)` is
    // `unsat` — no unconstrained variable is left for the search to escape
    // through, because the contradiction is between two TAGS of one witness.
    let mut arena = TermArena::new();
    let (dt, none, some) = opt(&mut arena);
    let f = producer(&mut arena, "f1946e", dt);
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let f_1 = arena.apply(f, &[one]).expect("apply f");
    let f_2 = arena.apply(f, &[two]).expect("apply f");
    let is_some = arena.dt_test(some, f_1).expect("test");
    let is_none = arena.dt_test(none, f_2).expect("test");

    let got = solve(&mut arena, &[is_some, is_none], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "this query is SATISFIABLE (z3, cvc5): `f` is free to differ at 1 and 2. \
         An `unsat` here is a congruence clause fired without its antecedent: {got:?}"
    );
}

#[test]
fn sound_a_uf_result_argument_needs_its_own_equality() {
    // `p(g(a)) /\ not p(g(b))` with `a`, `b` free — SATISFIABLE (z3, cvc5).
    //
    // WHAT FORCES THE WRONG ANSWER. `p`'s antecedent is the datatype equality
    // `w_ga = w_gb` over two free witness variables. The search satisfies the
    // query by making them differ, which it can. A mutation that admits the
    // `Op::Apply` argument WITHOUT its equality — or that trivialises the
    // antecedent — leaves `w_pa = w_pb` forced against `p /\ not p`, which is
    // `unsat` with no escape: `p`'s two witnesses are Booleans and the
    // assertions pin both.
    let mut arena = TermArena::new();
    let (dt, _mk) = pair(&mut arena);
    let g = producer(&mut arena, "g1946f", dt);
    let p = pred(&mut arena, "p1946f", dt);
    let a = var_of(&mut arena, "a1946f", Sort::Int);
    let b = var_of(&mut arena, "b1946f", Sort::Int);
    let g_a = arena.apply(g, &[a]).expect("apply g");
    let g_b = arena.apply(g, &[b]).expect("apply g");
    let p_ga = arena.apply(p, &[g_a]).expect("apply p");
    let p_at_b = arena.apply(p, &[g_b]).expect("apply p");
    let not_at_b = arena.not(p_at_b).expect("not");

    let got = solve(&mut arena, &[p_ga, not_at_b], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "this query is SATISFIABLE (z3, cvc5): nothing says `a = b`, so `g(a)` \
         and `g(b)` may differ and `p` may differ on them: {got:?}"
    );
}

#[test]
fn sound_the_mixed_case_over_a_uf_result_compares_every_field() {
    // `is-some(f(a)) /\ v(f(a)) = 2 /\ p(f(a)) /\ not p(some(1))` — SATISFIABLE
    // (z3, cvc5): `f(a)` is `some(2)`, which is not `some(1)`, so `p` may differ.
    //
    // WHAT FORCES THE WRONG ANSWER. The antecedent `some(1) = w_fa` is
    // `is-some(w_fa) /\ 1 = v(w_fa)`. The first conjunct is ASSERTED true and
    // the second is asserted FALSE (`v(f(a)) = 2`), so it is the FIELD
    // comparison alone that keeps the clause vacuous. Drop it — the
    // `construct_eq_term` field loop — and the antecedent is `is-some(w_fa)`,
    // which the query itself asserts, so `p` is forced to agree and the answer
    // is a wrong `unsat`. Both conjuncts are pinned by assertions rather than
    // left to the search, which is what ADR-1942's surviving mutant taught.
    //
    // This is `construct_eq_term` reached through a WITNESS operand rather than
    // a user variable — a path that did not exist before ADR-1946.
    let mut arena = TermArena::new();
    let (dt, _none, some) = opt(&mut arena);
    let f = producer(&mut arena, "f1946g", dt);
    let p = pred(&mut arena, "p1946g", dt);
    let a = var_of(&mut arena, "a1946g", Sort::Int);
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let f_a = arena.apply(f, &[a]).expect("apply f");
    let is_some = arena.dt_test(some, f_a).expect("test");
    let v_fa = arena.dt_select(some, 0, f_a).expect("select");
    let v_is_two = arena.eq(v_fa, two).expect("eq");
    let some_one = arena.construct(some, &[one]).expect("some");
    let p_fa = arena.apply(p, &[f_a]).expect("apply p");
    let p_some = arena.apply(p, &[some_one]).expect("apply p");
    let not_some = arena.not(p_some).expect("not");

    let got = solve(&mut arena, &[is_some, v_is_two, p_fa, not_some], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "this query is SATISFIABLE (z3, cvc5): `f(a)` is `some(2)`, not `some(1)`: {got:?}"
    );
}

#[test]
fn sound_an_inexact_result_datatype_is_not_merged_at_depth_two() {
    // `f : Int -> Lst`, with `f(a)` and `f(0)` agreeing at the head and the
    // top tag but DIFFERING at depth two, and `p(f(a)) /\ not p(f(0))` —
    // SATISFIABLE (z3, cvc5).
    //
    // This is the exactness precondition's soundness test, and ADR-1946 records
    // that it does NOT die when the precondition is deleted — the third time in
    // this series. The reason is structural rather than lucky: an `unsat` is
    // only returned from the `EqMode::Relaxation` arm, whose datatype equality
    // is a free Boolean carrying necessary conditions only, so a search looking
    // for a model sets the antecedent FALSE and the clause degenerates to
    // vacuous rather than to a wrong answer. The test stays because it is what
    // would fail if that encoding ever stopped being a relaxation.
    let mut arena = TermArena::new();
    let (dt, _nil, cons) = lst(&mut arena);
    let f = producer(&mut arena, "f1946h", dt);
    let p = pred(&mut arena, "p1946h", dt);
    let a = var_of(&mut arena, "a1946h", Sort::Int);
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let f_a = arena.apply(f, &[a]).expect("apply f");
    let f_0 = arena.apply(f, &[zero]).expect("apply f");
    let is_cons_a = arena.dt_test(cons, f_a).expect("test");
    let is_cons_0 = arena.dt_test(cons, f_0).expect("test");
    let hd_a = arena.dt_select(cons, 0, f_a).expect("select");
    let hd_0 = arena.dt_select(cons, 0, f_0).expect("select");
    let heads_agree = arena.eq(hd_a, hd_0).expect("eq");
    let tl_a = arena.dt_select(cons, 1, f_a).expect("select");
    let tl_0 = arena.dt_select(cons, 1, f_0).expect("select");
    let a_tail_is_cons = arena.dt_test(cons, tl_a).expect("test");
    let zero_tail_is_cons = arena.dt_test(cons, tl_0).expect("test");
    let hd_tl_a = arena.dt_select(cons, 0, tl_a).expect("select");
    let hd_tl_0 = arena.dt_select(cons, 0, tl_0).expect("select");
    let deep_a_is_one = arena.eq(hd_tl_a, one).expect("eq");
    let deep_0_is_two = arena.eq(hd_tl_0, two).expect("eq");
    let p_fa = arena.apply(p, &[f_a]).expect("apply p");
    let p_at_zero = arena.apply(p, &[f_0]).expect("apply p");
    let not_at_zero = arena.not(p_at_zero).expect("not");

    let got = solve(
        &mut arena,
        &[
            is_cons_a,
            is_cons_0,
            heads_agree,
            a_tail_is_cons,
            zero_tail_is_cons,
            deep_a_is_one,
            deep_0_is_two,
            p_fa,
            not_at_zero,
        ],
        &cfg(),
    );
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "this query is SATISFIABLE (z3, cvc5): the two lists differ at depth two, \
         so `p` may differ on them: {got:?}"
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
fn refusal_names_the_inexact_result_datatype() {
    // `f : Int -> Lst`. `Lst` has a datatype-typed field, so its expansion is
    // not exact and a `Lst`-valued RESULT is still refused — by a message that
    // names the RESULT rather than repeating the argument-side wording, because
    // the DT blocker census distinguishes the two.
    //
    // Called through `check_with_datatype_native` rather than `solve` for the
    // reason ADR-1935's version of this test records: the front door reaches
    // this guard only through queries an earlier rung decides.
    let mut arena = TermArena::new();
    let (dt, _nil, cons) = lst(&mut arena);
    let f = producer(&mut arena, "f1946i", dt);
    let zero = arena.int_const(0);
    let f_0 = arena.apply(f, &[zero]).expect("apply f");
    let is_cons = arena.dt_test(cons, f_0).expect("test");

    let detail = refusal_detail(check_with_datatype_native(&mut arena, &[is_cons], &cfg()));
    assert!(
        detail.contains("RESULT datatype's expansion is not exact"),
        "the refusal must name the RESULT datatype's expansion, got: {detail}"
    );
}

#[test]
fn refusal_names_the_array_over_a_datatype_result() {
    // `h : Pair -> (Array Int Pair)`. The result sort MENTIONS a datatype
    // without being one, so the witness would be array-sorted and the tag/field
    // expansion cannot reach into its elements.
    //
    // **This guard is a fence, not a tested path**, and the ADR says so: the
    // sizing census found 0 of 600 files with this shape. What this test pins is
    // that the refusal exists and names itself; it is deliberately NOT in the
    // mutation suite, because a mutation nothing can kill would report a
    // survivor forever and imply a coverage this has not got.
    let mut arena = TermArena::new();
    let (dt, _mk) = pair(&mut arena);
    let arr = Sort::Array {
        index: ArraySortKey::Int,
        element: ArraySortKey::Datatype(dt),
    };
    let h = arena
        .declare_fun("h1946j", &[Sort::Datatype(dt)], arr)
        .expect("declare h");
    let o = var_of(&mut arena, "o1946j", Sort::Datatype(dt));
    let o2 = var_of(&mut arena, "o21946j", Sort::Datatype(dt));
    let h_o = arena.apply(h, &[o]).expect("apply h");
    let h_o2 = arena.apply(h, &[o2]).expect("apply h");
    let same = arena.eq(h_o, h_o2).expect("eq");

    let detail = refusal_detail(check_with_datatype_native(&mut arena, &[same], &cfg()));
    assert!(
        detail.contains("MENTIONS a datatype without being one"),
        "the refusal must separate the array case from the datatype case, got: {detail}"
    );
}

#[test]
fn refusal_still_names_a_datatype_argument_that_is_none_of_the_three_shapes() {
    // `p(tl(x))` — a datatype-sorted SELECT as the argument, which is none of
    // variable / constructor / collected application. Still refused, and the
    // message now names all THREE admitted shapes because that is what the
    // census reads.
    let mut arena = TermArena::new();
    let (dt, _nil, cons) = lst(&mut arena);
    let p = pred(&mut arena, "p1946k", dt);
    let x = var_of(&mut arena, "x1946k", Sort::Datatype(dt));
    let tl_x = arena.dt_select(cons, 1, x).expect("select");
    let p_tl = arena.apply(p, &[tl_x]).expect("apply");

    let detail = refusal_detail(solve(&mut arena, &[p_tl], &cfg()));
    assert!(
        detail.contains("neither")
            && detail.contains("constructor application")
            && detail.contains("another uninterpreted"),
        "the refusal must name all three admitted shapes, got: {detail}"
    );
}
