#![cfg(feature = "full")]
// Guarded because this suite exercises `full`-only surface, so without the
// feature the crate does not compile `--all-targets` on DEFAULT features --
// which `cargo check --workspace` hides through Cargo's feature unification,
// so no gate here could see it.
//
// The guard has a cost worth naming: a `#![cfg]`-ed suite compiles to ZERO
// tests and exits 0 without the feature, which is how one gate here stayed
// inert for 15 days. The pre-push hook runs it WITH the feature, in the
// dispatch/reason block, and a run that prints `running 0 tests` is a failure
// of this file and not a pass.
//! ADR-2128: recursive NESTED DATATYPE FIELD expansion, behind a dated lever.
//!
//! A datatype-typed field gets no expansion variable, so `build_dt_eq` skips it
//! and the encoded `==` is one-directional -- which is why
//! `datatype_expansion_is_exact` is false for every nested record and why the
//! Ackermann congruence arms refuse. ADR-2114 §4 named the repair: give the
//! field its own child slot, recursively, reusing the `links` children
//! `unfold_traversals` already creates.
//!
//! The lever is `AXEYUM_DT_NESTED_FIELD_DEPTH` (and `NestedFieldExpansionGuard`
//! for a test, because a test passing only under an ambient env var is a gate on
//! one shell). **It is OFF by default** and this suite drives BOTH arms, because
//! the claim under measurement is a difference between them.
//!
//! What each test here would print if the change were broken:
//!
//! * `off_arm_*` -- a verdict that differs from the pre-ADR-2128 one. The OFF
//!   arm must be the shipped behaviour, or the A/B measures two changes.
//! * `on_arm_decides_*` -- `unknown`/`Unsupported` instead of the verdict: the
//!   child slots were not built, or `build_dt_eq` stopped comparing through
//!   them.
//! * `sound_*` -- a DECIDED verdict that contradicts the mathematics. This
//!   fragment is entitled to refuse and entitled to answer `unknown`; it is
//!   never entitled to be wrong. Both directions are covered: a spurious
//!   `unsat` on a satisfiable nested query, and a missed `unsat` that needs the
//!   nested selector's injectivity.
//! * `recursive_*` -- a decided verdict, or a materialised child, on a CYCLIC
//!   datatype. No finite unrolling of a cyclic closure is exact, and the
//!   materialiser must not spend a budget pretending otherwise.

use std::time::Duration;

use axeyum_ir::{ConstructorId, DatatypeId, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::theories::datatypes::{NestedFieldExpansionGuard, check_with_datatype_native};
use axeyum_solver::{CheckResult, SolverConfig, SolverError};

fn cfg() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(20))
}

fn var_of(arena: &mut TermArena, name: &str, sort: Sort) -> TermId {
    let sym = arena.declare(name, sort).expect("declare");
    arena.var(sym)
}

/// `Inner2128 = mk_inner(ic : Int)` -- exact on its own, every field scalar.
fn inner(arena: &mut TermArena) -> (DatatypeId, ConstructorId) {
    let dt = arena.declare_datatype("Inner2128");
    let mk = arena.add_constructor(dt, "mk_inner", &[("ic".to_owned(), Sort::Int)]);
    (dt, mk)
}

/// `Outer2128 = mk_outer(in_ : Inner2128, oc : Int)` -- ONE datatype-typed
/// field, depth 1, acyclic. This is ADR-2114's own `repro/ground.smt2` shape and
/// the whole `INEXACT` bucket in miniature.
fn outer(arena: &mut TermArena) -> (DatatypeId, ConstructorId, DatatypeId, ConstructorId) {
    let (idt, mk_inner) = inner(arena);
    let dt = arena.declare_datatype("Outer2128");
    let mk = arena.add_constructor(
        dt,
        "mk_outer",
        &[
            ("in_".to_owned(), Sort::Datatype(idt)),
            ("oc".to_owned(), Sort::Int),
        ],
    );
    (dt, mk, idt, mk_inner)
}

/// `Lst2128 = nil | cons(car : Int, cdr : Lst2128)` -- CYCLIC. The positive
/// control for the recursion guard: a detector nobody has shown to fire is
/// indistinguishable from a broken one.
fn recursive_list(arena: &mut TermArena) -> (DatatypeId, ConstructorId, ConstructorId) {
    let dt = arena.declare_datatype("Lst2128");
    let nil = arena.add_constructor(dt, "nil2128", &[]);
    let cons = arena.add_constructor(
        dt,
        "cons2128",
        &[
            ("car2128".to_owned(), Sort::Int),
            ("cdr2128".to_owned(), Sort::Datatype(dt)),
        ],
    );
    (dt, nil, cons)
}

fn int_const(arena: &mut TermArena, v: i64) -> TermId {
    arena.int_const(i128::from(v))
}

// ---------------------------------------------------------------- the OFF arm
//
// THE DISCRIMINATING SHAPE, and the two wrong guesses that came before it.
//
// 1. `a = mk_outer(mk_inner(1), 7)` is folded EXACTLY by `simplify_datatypes`
//    (read-over-construct) before the tag/field expansion runs at all, so a
//    query written with CONSTRUCTOR TERMS is decided with the lever OFF.
// 2. `a != b` over two free variables agreeing on every reachable scalar is
//    ALSO decided with the lever OFF, because `expand_datatype_equalities`
//    already rewrites a top-level `==` into the per-constructor field
//    comparison one level deep, and `unfold_traversals` turns the resulting
//    nested `select`s into child variables. The `==` encoding is not where the
//    gap is.
//
// The gap is the ACKERMANN EXACTNESS PRECONDITION. `datatype_expansion_is_exact`
// is a PREDICATE consulted before any of that machinery runs
// (`datatype_native.rs:904`, `:963`), and a datatype-typed field makes it false
// outright -- so an uninterpreted function applied to a nested record is
// REFUSED, whatever `expand_datatype_equalities` could have done with the
// equality. That refusal is ADR-2114's `INEXACT` bucket, its wording is
// "congruence over a datatype argument whose expansion is not exact", and this
// is the shape of ADR-2114's own `repro/ground.smt2`:
//
//     (declare-fun f (Outer) Int)   (assert (= a b))   (assert (not (= (f a) (f b))))
//
// UNSAT by congruence alone. The lever's whole claim is that a bounded nested
// expansion makes the precondition true without making the encoding weaker.

/// `f : Outer2128 -> Int`, `a = b`, `f(a) != f(b)`. UNSAT by congruence.
/// ADR-2114's `repro/ground.smt2`, built in the IR.
fn nested_congruence(arena: &mut TermArena, tag: &str) -> Vec<TermId> {
    let (odt, _mk_outer, _idt, _mk_inner) = outer(arena);
    let a = var_of(arena, &format!("a_{tag}"), Sort::Datatype(odt));
    let b = var_of(arena, &format!("b_{tag}"), Sort::Datatype(odt));
    let f = arena
        .declare_fun(&format!("f_{tag}"), &[Sort::Datatype(odt)], Sort::Int)
        .expect("declare f");
    let fa = arena.apply(f, &[a]).expect("apply");
    let fb = arena.apply(f, &[b]).expect("apply");
    let eab = arena.eq(a, b).expect("eq");
    let results_eq = arena.eq(fa, fb).expect("eq");
    let nef = arena.not(results_eq).expect("not");
    vec![eab, nef]
}

/// The shipped default REFUSES the discriminating query, and refuses it by name.
///
/// This is the non-vacuity control for the whole suite. An ON-arm test that
/// passes because the query was always decidable measures nothing, and this is
/// the only thing that can tell the two apart. The assertion is on the WORDING
/// as well as the outcome, because a refusal for some other reason would leave
/// the ON arm's success unexplained.
#[test]
fn off_arm_refuses_the_nested_congruence() {
    let _g = NestedFieldExpansionGuard::set(0);
    let mut arena = TermArena::new();
    let asserts = nested_congruence(&mut arena, "off");
    let out = check_with_datatype_native(&mut arena, &asserts, &cfg());
    match out {
        Err(SolverError::Unsupported(message)) => assert!(
            message.contains("expansion is not exact"),
            "the OFF arm refused, but not on the exactness precondition -- so \
             the ON arm's success below would be explained by something else: \
             {message}"
        ),
        other => panic!(
            "the OFF arm must refuse the nested-congruence query on the \
             exactness precondition. If it decides it, this suite is vacuous: \
             {other:?}"
        ),
    }
}

// ---------------------------------------------------------------- the ON arm

/// With the lever ON, the nested expansion makes the precondition true and the
/// congruence refutes the query.
#[test]
fn on_arm_decides_the_nested_congruence() {
    let _g = NestedFieldExpansionGuard::set(2);
    let mut arena = TermArena::new();
    let asserts = nested_congruence(&mut arena, "on");
    let out = check_with_datatype_native(&mut arena, &asserts, &cfg());
    assert!(
        matches!(out, Ok(CheckResult::Unsat)),
        "the ON arm must refute this: `a = b` and congruence force \
         `f(a) = f(b)`. Anything else means the exactness predicate did not \
         widen, or the child slots the widening promises were not built: \
         {out:?}"
    );
}

/// SOUNDNESS-NEGATIVE for the congruence arm. The SAME function and the SAME
/// nested record, but the two arguments are NOT asserted equal -- so `f(a)` and
/// `f(b)` may differ and the query is SATISFIABLE.
///
/// This is the pair the exactness precondition exists to protect: a weaker
/// encoded antecedent makes the congruence clause STRONGER than the true axiom
/// and produces a wrong `unsat` (ADR-1920). If the nested expansion ever
/// compared LESS than it claims, `a = b` would be satisfied by two records that
/// differ in the nested field and this would go `unsat`.
#[test]
fn sound_nested_congruence_does_not_force_equal_results() {
    for depth in [0u32, 1, 2, 5] {
        let _g = NestedFieldExpansionGuard::set(depth);
        let mut arena = TermArena::new();
        let (odt, mk_outer, _idt, mk_inner) = outer(&mut arena);
        let a = var_of(&mut arena, "a_sc", Sort::Datatype(odt));
        let b = var_of(&mut arena, "b_sc", Sort::Datatype(odt));
        let f = arena
            .declare_fun("f_sc", &[Sort::Datatype(odt)], Sort::Int)
            .expect("declare f");
        let fa = arena.apply(f, &[a]).expect("apply");
        let fb = arena.apply(f, &[b]).expect("apply");
        let results_eq = arena.eq(fa, fb).expect("eq");
        let nef = arena.not(results_eq).expect("not");
        // The records agree on `oc` but their nested `ic` values differ, so
        // `a != b` and `f(a) != f(b)` is perfectly satisfiable.
        let oca = arena.dt_select(mk_outer, 1, a).expect("select");
        let ocb = arena.dt_select(mk_outer, 1, b).expect("select");
        let oc_eq = arena.eq(oca, ocb).expect("eq");
        let ina = arena.dt_select(mk_outer, 0, a).expect("select");
        let inb = arena.dt_select(mk_outer, 0, b).expect("select");
        let ica = arena.dt_select(mk_inner, 0, ina).expect("select");
        let icb = arena.dt_select(mk_inner, 0, inb).expect("select");
        let one = int_const(&mut arena, 1);
        let two = int_const(&mut arena, 2);
        let left_inner_is_one = arena.eq(ica, one).expect("eq");
        let right_inner_is_two = arena.eq(icb, two).expect("eq");

        let out = check_with_datatype_native(
            &mut arena,
            &[nef, oc_eq, left_inner_is_one, right_inner_is_two],
            &cfg(),
        );
        assert!(
            !matches!(out, Ok(CheckResult::Unsat)),
            "WRONG UNSAT at depth {depth}: `a` and `b` differ in the nested \
             field, so congruence says nothing about `f(a)` and `f(b)`. An \
             `unsat` here is the ADR-1920 shape -- a congruence antecedent \
             weaker than real equality: {out:?}"
        );
    }
}

// ---------------------------------------------------- soundness, both sides

/// SOUNDNESS-NEGATIVE, `sat` side. Two distinct nested values whose expansion
/// shares slot coordinates must NOT collide into a spurious conflict.
///
/// `a` and `b` are both `mk_outer`, so their child slots are the SAME
/// `(constructor, field)` coordinate `(0, 0)` -- different symbols, same
/// coordinate. If the materialiser ever keyed a child on the coordinate rather
/// than on `(symbol, coordinate)`, `a`'s and `b`'s inner values would be ONE
/// variable and `a != b` would be refuted. It is satisfiable, so any `unsat`
/// here is that defect.
#[test]
fn sound_two_distinct_nested_values_do_not_collide() {
    for depth in [0u32, 1, 3] {
        let _g = NestedFieldExpansionGuard::set(depth);
        let mut arena = TermArena::new();
        let (odt, mk_outer, _idt, mk_inner) = outer(&mut arena);
        let a = var_of(&mut arena, "a_coll", Sort::Datatype(odt));
        let b = var_of(&mut arena, "b_coll", Sort::Datatype(odt));

        // oc(a) = oc(b), ic(in_(a)) = 1, ic(in_(b)) = 2, a != b.
        // SATISFIABLE: the two records differ precisely in the nested field.
        let oca = arena.dt_select(mk_outer, 1, a).expect("select");
        let ocb = arena.dt_select(mk_outer, 1, b).expect("select");
        let oc_eq = arena.eq(oca, ocb).expect("eq");
        let ina = arena.dt_select(mk_outer, 0, a).expect("select");
        let inb = arena.dt_select(mk_outer, 0, b).expect("select");
        let ica = arena.dt_select(mk_inner, 0, ina).expect("select");
        let icb = arena.dt_select(mk_inner, 0, inb).expect("select");
        let one = int_const(&mut arena, 1);
        let two = int_const(&mut arena, 2);
        let left_inner_is_one = arena.eq(ica, one).expect("eq");
        let right_inner_is_two = arena.eq(icb, two).expect("eq");
        let eab = arena.eq(a, b).expect("eq");
        let neq = arena.not(eab).expect("not");
        let asserts = [oc_eq, left_inner_is_one, right_inner_is_two, neq];

        let out = check_with_datatype_native(&mut arena, &asserts, &cfg());
        assert!(
            !matches!(out, Ok(CheckResult::Unsat)),
            "WRONG UNSAT at depth {depth}: `a` and `b` are both `mk_outer` and \
             their child slots share the coordinate `(0, 0)`, so a materialiser \
             that keyed a child on the COORDINATE rather than on \
             `(symbol, coordinate)` would make `ic = 1` and `ic = 2` the same \
             variable. The query is satisfiable: {out:?}"
        );
        if let Ok(CheckResult::Sat(model)) = out {
            let assignment = model.to_assignment();
            for &assertion in &asserts {
                assert!(
                    matches!(eval(&arena, assertion, &assignment), Ok(Value::Bool(true))),
                    "depth {depth}: the returned model does not satisfy the \
                     original assertions -- every `sat` must replay"
                );
            }
        }
    }
}

/// SOUNDNESS-NEGATIVE, `unsat` side. The refutation needs the NESTED selector's
/// injectivity, which is exactly what the child comparison supplies.
///
/// `a = mk_outer(x, 0)`, `b = mk_outer(y, 0)`, `a = b`, and `x`'s `ic` is 1
/// while `y`'s is 2. Refuting it requires pushing equality THROUGH `in_` and
/// then through `ic` -- two levels of injectivity. A `sat` here is a wrong
/// answer in the other direction, and `unknown` is allowed.
#[test]
fn sound_nested_selector_injectivity_is_never_contradicted() {
    for depth in [0u32, 1, 2, 4] {
        let _g = NestedFieldExpansionGuard::set(depth);
        let mut arena = TermArena::new();
        let (odt, mk_outer, idt, mk_inner) = outer(&mut arena);
        let a = var_of(&mut arena, "a_inj", Sort::Datatype(odt));
        let b = var_of(&mut arena, "b_inj", Sort::Datatype(odt));
        let x = var_of(&mut arena, "x_inj", Sort::Datatype(idt));
        let y = var_of(&mut arena, "y_inj", Sort::Datatype(idt));

        let zero = int_const(&mut arena, 0);
        let one = int_const(&mut arena, 1);
        let two = int_const(&mut arena, 2);
        let oa = arena.construct(mk_outer, &[x, zero]).expect("construct");
        let ob = arena.construct(mk_outer, &[y, zero]).expect("construct");
        let ix = arena.construct(mk_inner, &[one]).expect("construct");
        let iy = arena.construct(mk_inner, &[two]).expect("construct");
        let ea = arena.eq(a, oa).expect("eq");
        let eb = arena.eq(b, ob).expect("eq");
        let ex = arena.eq(x, ix).expect("eq");
        let ey = arena.eq(y, iy).expect("eq");
        let eab = arena.eq(a, b).expect("eq");

        let out = check_with_datatype_native(&mut arena, &[ea, eb, ex, ey, eab], &cfg());
        assert!(
            !matches!(out, Ok(CheckResult::Sat(_))),
            "WRONG SAT at depth {depth}: `a = b` forces `x = y` forces `1 = 2`. \
             `unknown` and a refusal are both allowed here; a model is not: \
             {out:?}"
        );
    }
}

// ------------------------------------------------- the recursion guard

/// A CYCLIC datatype is never decided by pretending a finite unrolling is
/// exact.
///
/// `cons(1, l) = cons(2, l)` is unsat by injectivity at the FIRST field, which
/// the scalar expansion already sees -- so this test does not assert `unknown`.
/// What it asserts is the other direction: no depth makes the answer WRONG.
#[test]
fn recursive_datatype_is_never_answered_wrongly() {
    for depth in [0u32, 1, 5, 8] {
        let _g = NestedFieldExpansionGuard::set(depth);
        let mut arena = TermArena::new();
        let (ldt, _nil, cons) = recursive_list(&mut arena);
        let l = var_of(&mut arena, "l_rec", Sort::Datatype(ldt));
        let p = var_of(&mut arena, "p_rec", Sort::Datatype(ldt));
        let q = var_of(&mut arena, "q_rec", Sort::Datatype(ldt));

        let one = int_const(&mut arena, 1);
        let two = int_const(&mut arena, 2);
        let cp = arena.construct(cons, &[one, l]).expect("construct");
        let cq = arena.construct(cons, &[two, l]).expect("construct");
        let ep = arena.eq(p, cp).expect("eq");
        let eq_ = arena.eq(q, cq).expect("eq");
        let epq = arena.eq(p, q).expect("eq");

        let out = check_with_datatype_native(&mut arena, &[ep, eq_, epq], &cfg());
        assert!(
            !matches!(out, Ok(CheckResult::Sat(_))),
            "WRONG SAT at depth {depth} on a recursive datatype: \
             `cons(1, l) = cons(2, l)` forces `1 = 2`: {out:?}"
        );
    }
}

/// A cyclic datatype stays SATISFIABLE where it should be, at every depth.
///
/// The failure this rejects is the one a depth-bounded unrolling invites: a
/// finite expansion that treats the bottom of the budget as a constraint rather
/// than as a free slot would refute a perfectly satisfiable list.
#[test]
fn sound_recursive_datatype_stays_satisfiable() {
    for depth in [0u32, 1, 5, 8] {
        let _g = NestedFieldExpansionGuard::set(depth);
        let mut arena = TermArena::new();
        let (ldt, _nil, cons) = recursive_list(&mut arena);
        let p = var_of(&mut arena, "p_sat", Sort::Datatype(ldt));
        let q = var_of(&mut arena, "q_sat", Sort::Datatype(ldt));
        let is_p = arena.dt_test(cons, p).expect("test");
        let is_q = arena.dt_test(cons, q).expect("test");
        let epq = arena.eq(p, q).expect("eq");
        let neq = arena.not(epq).expect("not");

        let out = check_with_datatype_native(&mut arena, &[is_p, is_q, neq], &cfg());
        assert!(
            !matches!(out, Ok(CheckResult::Unsat)),
            "WRONG UNSAT at depth {depth}: two distinct `cons` lists exist \
             (cvc5 and z3 both answer sat on this shape -- ADR-1930): {out:?}"
        );
    }
}

// ------------------------------------------------- the lever itself

/// The lever is OFF unless something turns it on, and a typo turns it OFF
/// rather than on to an arm nobody chose.
///
/// Read through the guard rather than the environment, because a test that
/// passes only under an ambient env var is a gate on one shell.
#[test]
fn the_lever_defaults_to_off_and_clamps() {
    // No guard set: the PROCESS default, read through the only thing that
    // observes it -- the discriminating query.
    let mut arena = TermArena::new();
    let asserts = nested_congruence(&mut arena, "lev");
    let out = check_with_datatype_native(&mut arena, &asserts, &cfg());
    assert!(
        matches!(out, Err(SolverError::Unsupported(_))),
        "the SHIPPED DEFAULT decided a query only the nested expansion reaches, \
         so the lever is ON without anyone turning it on: {out:?}"
    );

    // And an absurd depth is clamped rather than obeyed.
    let _g = NestedFieldExpansionGuard::set(u32::MAX);
    let mut arena2 = TermArena::new();
    let (ldt, _nil, cons) = recursive_list(&mut arena2);
    let l = var_of(&mut arena2, "l_clamp", Sort::Datatype(ldt));
    let is_l = arena2.dt_test(cons, l).expect("test");
    let out2 = check_with_datatype_native(&mut arena2, &[is_l], &cfg());
    assert!(
        !matches!(out2, Err(SolverError::Backend(_))),
        "a `u32::MAX` depth must be clamped to the registered maximum, not \
         obeyed into an explosion: {out2:?}"
    );
}
