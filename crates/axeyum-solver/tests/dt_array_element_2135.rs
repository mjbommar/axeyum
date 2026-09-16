#![cfg(feature = "full")]
// Guarded because this suite exercises `full`-only surface, so without the
// feature the crate does not compile `--all-targets` on DEFAULT features --
// which `cargo check --workspace` hides through Cargo's feature unification,
// so no gate here could see it.
//
// The guard has a cost worth naming: a `#![cfg]`-ed suite compiles to ZERO
// tests and exits 0 without the feature, which is how one gate here stayed
// inert for 15 days. Its count under `--features full` is pinned in the commit
// that added this line, and the pre-push hook runs it WITH the feature.
//! ADR-2135: an array whose ELEMENT SORT mentions a datatype, admitted as an
//! **opaque datatype FIELD**.
//!
//! `register_datatype` refuses the first non-expanding sort in a datatype's
//! field closure, and on every measured population that sort is
//! `(Array Int <datatype>)` — 142 of 142 across the ground probe's 83 files,
//! 112 of 112 across `AUFDTLIRA`'s undecided files
//! (`bench-results/dt-array-element-20260916/README.md`). ADR-1935 gave an
//! array field an expansion variable **only** when its component sorts mention
//! no datatype; this lever admits the rest as OPAQUE, on exactly the terms a
//! datatype-typed field has had since ADR-1930: recorded in the layout, no
//! expansion variable, never traversed, projected to a well-founded default.
//!
//! **What the lever does NOT do, and this suite pins it.** It does not let the
//! tag/field expansion reach into the array. A `select` of the opaque field is
//! a DECLINE, and `select_of_the_opaque_field_declines_it_does_not_error` is
//! the test that says so. Reaching into the elements needs the array's own
//! sort-abstraction route (ADR-2065's `OpaqueReals` shape), which this lane
//! measured at 2 of 800 competition rows and did not build.
//!
//! What each test here would print if the change were broken:
//!
//! * `opaque_*` with the lever ON — `Unsupported` instead of a verdict: the
//!   admission arm reverted, or `field_is_opaque` stopped matching the array.
//! * `off_*` — a verdict instead of `Unsupported`: the lever's default flipped,
//!   which would make every `AXEYUM_DT_ARRAY_ELEMENT`-unset run take the new
//!   arm silently.
//! * `sound_*` — a decided verdict that contradicts the mathematics. The
//!   fragment is entitled to refuse; it is never entitled to be wrong. These
//!   are the ADR-1930 wrong-`unsat` shape, transplanted onto the new field
//!   class: an opaque field is skipped by `build_dt_eq`, so an encoding that
//!   forgot to mark the query relaxed would answer `unsat` where two records
//!   can genuinely differ.
//! * `select_of_the_opaque_field_declines_it_does_not_error` — a `Backend`
//!   error, or a verdict: the `scan_fragment` refusal is what makes the
//!   admission sound, and without it the `None` field slot surfaces as an
//!   internal error the ladder cannot walk past.
//! * `nested_*` — a verdict that moves when ADR-2128's depth lever moves: the
//!   opaque container recursed into the array's element datatype after all,
//!   which is the expansion ADR-2128 measured as reaching none of this.

use std::time::Duration;

use axeyum_ir::{ArraySortKey, ConstructorId, DatatypeId, Sort, TermArena, TermId};
use axeyum_solver::theories::datatypes::{
    DatatypeArrayElementGuard, NestedFieldExpansionGuard, check_with_datatype_native,
};
use axeyum_solver::{CheckResult, SolverConfig, SolverError, solve};

fn cfg() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(10))
}

fn var_of(arena: &mut TermArena, name: &str, sort: Sort) -> TermId {
    let sym = arena.declare(name, sort).expect("declare");
    arena.var(sym)
}

/// `Inner = imk(k : Int)` — a scalar record, so its own expansion is exact.
fn inner(arena: &mut TermArena) -> (DatatypeId, ConstructorId) {
    let dt = arena.declare_datatype("Inner2135");
    let imk = arena.add_constructor(dt, "imk", &[("k".to_owned(), Sort::Int)]);
    (dt, imk)
}

/// `Rec = mk(a : (Array Int Inner), n : Int)` — the SPARK array-of-record
/// shape. `us_rep`'s `(Array Int us_rep1)` field is this, and it is the sort
/// `register_datatype` refuses on 142 of 142 measured occurrences.
fn array_of_datatype_record(arena: &mut TermArena) -> (DatatypeId, ConstructorId, DatatypeId) {
    let (idt, _) = inner(arena);
    let arr = Sort::Array {
        index: ArraySortKey::Int,
        element: ArraySortKey::Datatype(idt),
    };
    let dt = arena.declare_datatype("Rec2135");
    let mk = arena.add_constructor(
        dt,
        "mk",
        &[("a".to_owned(), arr), ("n".to_owned(), Sort::Int)],
    );
    (dt, mk, idt)
}

/// `is-mk(r) /\ (n r) = 5 /\ (n r) = <other>`. The array field is present in
/// the DECLARATION and untouched by the query — the shape the lever exists for.
fn scalar_field_query(arena: &mut TermArena, other: i128) -> Vec<TermId> {
    let (dt, mk, _) = array_of_datatype_record(arena);
    let rec = var_of(arena, "r", Sort::Datatype(dt));
    let is_mk = arena.dt_test(mk, rec).expect("test");
    let num = arena.dt_select(mk, 1, rec).expect("select");
    let five = arena.int_const(5);
    let other_const = arena.int_const(other);
    let first = arena.eq(num, five).expect("eq");
    let second = arena.eq(num, other_const).expect("eq");
    vec![is_mk, first, second]
}

// ==========================================================================
// The lever OFF — the shipped default. Every one of these is the pre-ADR-2135
// behaviour, and a verdict here means the default flipped.
// ==========================================================================

#[test]
fn off_the_array_of_datatype_field_is_still_refused() {
    let _g = DatatypeArrayElementGuard::set(false);
    let mut arena = TermArena::new();
    let q = scalar_field_query(&mut arena, 6);
    let got = check_with_datatype_native(&mut arena, &q, &cfg());
    let Err(SolverError::Unsupported(message)) = got else {
        panic!("expected the pre-ADR-2135 refusal with the lever OFF, got {got:?}");
    };
    assert!(
        message.contains("a datatype field sort with no expansion variable"),
        "expected the W1 refusal, got {message:?}"
    );
}

#[test]
fn off_is_the_shipped_default_with_no_guard_and_no_env() {
    // No `DatatypeArrayElementGuard` at all: this is what an unset
    // `AXEYUM_DT_ARRAY_ELEMENT` gives every other lane. CLAUDE.md's rule that a
    // test passing only under an ambient env var is a gate on one shell, run in
    // the direction that matters — the DEFAULT must not need a variable to be
    // the default.
    assert!(
        std::env::var("AXEYUM_DT_ARRAY_ELEMENT").is_err(),
        "this suite asserts the SHIPPED default; run it without \
         AXEYUM_DT_ARRAY_ELEMENT set"
    );
    let mut arena = TermArena::new();
    let q = scalar_field_query(&mut arena, 6);
    assert!(
        matches!(
            check_with_datatype_native(&mut arena, &q, &cfg()),
            Err(SolverError::Unsupported(_))
        ),
        "the shipped default must still refuse the array-of-datatype field"
    );
}

// ==========================================================================
// The lever ON — the capability.
// ==========================================================================

#[test]
fn opaque_scalar_field_over_an_array_of_datatype_record_decides_unsat() {
    // `(n r) = 5 /\ (n r) = 6` is UNSAT by functionality of the field, and the
    // array field never enters. With the lever OFF this is the W1 refusal;
    // with it ON the datatype route owns and decides the query.
    let _g = DatatypeArrayElementGuard::set(true);
    let mut arena = TermArena::new();
    let q = scalar_field_query(&mut arena, 6);
    let got = check_with_datatype_native(&mut arena, &q, &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "expected unsat over the scalar field of an array-of-datatype record, got {got:?}"
    );
}

#[test]
fn opaque_scalar_field_over_an_array_of_datatype_record_decides_sat() {
    // The same shape, DECIDABLE THE OTHER WAY: `(n r) = 5 /\ (n r) = 5`. A
    // lever that only ever produced `unsat` would pass the test above while
    // being a refutation-only relaxation; this is the half that says the
    // admission is a capability and not a one-directional artefact.
    let _g = DatatypeArrayElementGuard::set(true);
    let mut arena = TermArena::new();
    let q = scalar_field_query(&mut arena, 5);
    let got = check_with_datatype_native(&mut arena, &q, &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Sat(_))),
        "expected sat over the scalar field of an array-of-datatype record, got {got:?}"
    );
}

#[test]
fn opaque_front_door_decides_the_same_way() {
    // End to end through `solve`, not just the route: a route-level verdict the
    // dispatcher does not reach is not a capability.
    let _g = DatatypeArrayElementGuard::set(true);
    let mut arena = TermArena::new();
    let q = scalar_field_query(&mut arena, 6);
    let got = solve(&mut arena, &q, &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "expected unsat from the front door, got {got:?}"
    );
}

#[test]
fn opaque_admission_is_deterministic() {
    // Determinism is a public API promise. Two identical builds, one verdict.
    let _g = DatatypeArrayElementGuard::set(true);
    let mut first = TermArena::new();
    let qa = scalar_field_query(&mut first, 6);
    let a = check_with_datatype_native(&mut first, &qa, &cfg());
    let mut second = TermArena::new();
    let qb = scalar_field_query(&mut second, 6);
    let b = check_with_datatype_native(&mut second, &qb, &cfg());
    assert_eq!(
        format!("{a:?}"),
        format!("{b:?}"),
        "the opaque-field admission is not deterministic"
    );
}

// ==========================================================================
// The traversal guard — what makes the admission sound.
// ==========================================================================

#[test]
fn select_of_the_opaque_field_declines_it_does_not_error() {
    // `(a r) = b` reads the opaque field itself. The field has NO expansion
    // variable, so the `select_{mk,0}(r)` site has nothing to rewrite to. This
    // MUST be an `Unsupported` DECLINE the ladder can walk past, never a
    // `Backend` error (which leaves `solve` at `give-up kind=Error` and skips
    // every rung below) and never a verdict.
    //
    // This is the one test that exercises `scan_fragment`'s ADR-2135 arm
    // DIRECTLY: `r` is a variable, so nothing earlier in the scan refuses
    // first. Dropping that arm makes this test die and no other.
    let _g = DatatypeArrayElementGuard::set(true);
    let mut arena = TermArena::new();
    let (dt, mk, idt) = array_of_datatype_record(&mut arena);
    let arr = Sort::Array {
        index: ArraySortKey::Int,
        element: ArraySortKey::Datatype(idt),
    };
    let r = var_of(&mut arena, "r", Sort::Datatype(dt));
    let b = var_of(&mut arena, "b", arr);
    let is_mk = arena.dt_test(mk, r).expect("test");
    let field = arena.dt_select(mk, 0, r).expect("select");
    let eq = arena.eq(field, b).expect("eq");

    let got = check_with_datatype_native(&mut arena, &[is_mk, eq], &cfg());
    let Err(SolverError::Unsupported(message)) = got else {
        panic!("traversing the opaque field must DECLINE, got {got:?}");
    };
    assert!(
        message.contains("opaque container with no expansion variable"),
        "expected the ADR-2135 decline naming the opaque container, got {message:?}"
    );
}

#[test]
fn reading_through_the_opaque_field_declines_by_some_guard() {
    // The DEEPER traversal: `(k (select (a r) 0)) = 5`. This one is refused
    // before the ADR-2135 arm is reached (the inner `select` is not a variable,
    // so `expect_dt_symbol` refuses first), and the point of the test is that
    // the outcome is still a DECLINE and never a verdict -- the admission opens
    // a declaration, not a traversal, whichever guard happens to catch it.
    let _g = DatatypeArrayElementGuard::set(true);
    let mut arena = TermArena::new();
    let (dt, mk, idt) = array_of_datatype_record(&mut arena);
    let r = var_of(&mut arena, "r", Sort::Datatype(dt));
    let is_mk = arena.dt_test(mk, r).expect("test");
    let field = arena.dt_select(mk, 0, r).expect("select");
    let zero = arena.int_const(0);
    let read = arena.select(field, zero).expect("array select");
    let imk = arena.datatype_constructors(idt)[0];
    let k = arena.dt_select(imk, 0, read).expect("inner select");
    let five = arena.int_const(5);
    let eq = arena.eq(k, five).expect("eq");

    let got = check_with_datatype_native(&mut arena, &[is_mk, eq], &cfg());
    assert!(
        matches!(got, Err(SolverError::Unsupported(_))),
        "reading through the opaque field must DECLINE, got {got:?}"
    );
}

#[test]
fn sound_two_records_differing_only_in_the_opaque_field_are_not_unsat() {
    // THE ADR-1930 SHAPE, on the new field class. `is-mk(p) /\ is-mk(q) /\
    // (n p) = (n q) /\ p != q` is **SAT**: the two records agree on every field
    // the expansion can see and may still differ in the opaque array. An
    // encoding that compared only the expanded fields — or that compared them
    // in BOTH directions — would answer `unsat` here, which is a wrong verdict.
    // Refusing is allowed; `unsat` is not.
    let _g = DatatypeArrayElementGuard::set(true);
    let mut arena = TermArena::new();
    let (dt, mk, _) = array_of_datatype_record(&mut arena);
    let p = var_of(&mut arena, "p", Sort::Datatype(dt));
    let q = var_of(&mut arena, "q", Sort::Datatype(dt));
    let is_p = arena.dt_test(mk, p).expect("test");
    let is_q = arena.dt_test(mk, q).expect("test");
    let np = arena.dt_select(mk, 1, p).expect("select");
    let nq = arena.dt_select(mk, 1, q).expect("select");
    let same_n = arena.eq(np, nq).expect("eq");
    let pq = arena.eq(p, q).expect("eq");
    let differ = arena.not(pq).expect("not");

    let got = check_with_datatype_native(&mut arena, &[is_p, is_q, same_n, differ], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "WRONG UNSAT: two records agreeing on every expanded field may still \
         differ in the opaque array field; got {got:?}"
    );
}

#[test]
fn sound_a_contradiction_on_the_expanded_field_still_refutes() {
    // The paired positive for the test above, and the reason that one is not
    // vacuous: when the contradiction IS on a field the expansion can see, the
    // relaxation must still refute. A fragment that answered `unknown` to both
    // would pass the soundness test while having no capability at all.
    let _g = DatatypeArrayElementGuard::set(true);
    let mut arena = TermArena::new();
    let (dt, mk, _) = array_of_datatype_record(&mut arena);
    let p = var_of(&mut arena, "p", Sort::Datatype(dt));
    let q = var_of(&mut arena, "q", Sort::Datatype(dt));
    let is_p = arena.dt_test(mk, p).expect("test");
    let is_q = arena.dt_test(mk, q).expect("test");
    let np = arena.dt_select(mk, 1, p).expect("select");
    let nq = arena.dt_select(mk, 1, q).expect("select");
    let five = arena.int_const(5);
    let six = arena.int_const(6);
    let a = arena.eq(np, five).expect("eq");
    let b = arena.eq(nq, six).expect("eq");
    let pq = arena.eq(p, q).expect("eq");

    let got = check_with_datatype_native(&mut arena, &[is_p, is_q, a, b, pq], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "a contradiction on an EXPANDED field must still refute, got {got:?}"
    );
}

// ==========================================================================
// The opaque container does not recurse — ADR-2128's expansion is not
// reintroduced through the array.
// ==========================================================================

/// `Outer = omk(i : Inner)` and `Nest = nmk(a : (Array Int Outer), n : Int)`.
/// The element datatype is itself a record containing a record, so a lever that
/// recursed INTO the array would be doing ADR-2128's nested-field expansion —
/// which ADR-2128 measured as reaching none of this population.
fn nested_element_record(arena: &mut TermArena) -> (DatatypeId, ConstructorId) {
    let (idt, _) = inner(arena);
    let odt = arena.declare_datatype("Outer2135");
    arena.add_constructor(odt, "omk", &[("i".to_owned(), Sort::Datatype(idt))]);
    let arr = Sort::Array {
        index: ArraySortKey::Int,
        element: ArraySortKey::Datatype(odt),
    };
    let dt = arena.declare_datatype("Nest2135");
    let nmk = arena.add_constructor(
        dt,
        "nmk",
        &[("a".to_owned(), arr), ("n".to_owned(), Sort::Int)],
    );
    (dt, nmk)
}

fn nested_query(arena: &mut TermArena) -> Vec<TermId> {
    let (dt, nmk) = nested_element_record(arena);
    let r = var_of(arena, "r", Sort::Datatype(dt));
    let is_nmk = arena.dt_test(nmk, r).expect("test");
    let n = arena.dt_select(nmk, 1, r).expect("select");
    let five = arena.int_const(5);
    let six = arena.int_const(6);
    let a = arena.eq(n, five).expect("eq");
    let b = arena.eq(n, six).expect("eq");
    vec![is_nmk, a, b]
}

#[test]
fn nested_element_datatype_is_still_opaque() {
    let _g = DatatypeArrayElementGuard::set(true);
    let mut arena = TermArena::new();
    let q = nested_query(&mut arena);
    let got = check_with_datatype_native(&mut arena, &q, &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "expected unsat over the scalar field of a nested-element record, got {got:?}"
    );
}

#[test]
fn nested_element_verdict_does_not_move_with_the_adr_2128_depth_lever() {
    // If the opaque container recursed into the array's element datatype, the
    // ADR-2128 depth budget would be what decided how far — and the verdict, or
    // at least the refusal message, would move with it. It must not: the array
    // is not a field to expand, at any depth.
    let _g = DatatypeArrayElementGuard::set(true);
    let mut seen = Vec::new();
    for depth in [0u32, 1, 5] {
        let _d = NestedFieldExpansionGuard::set(depth);
        let mut arena = TermArena::new();
        let q = nested_query(&mut arena);
        seen.push(format!(
            "{:?}",
            check_with_datatype_native(&mut arena, &q, &cfg())
        ));
    }
    assert!(
        seen.windows(2).all(|w| w[0] == w[1]),
        "the nested-element verdict moved with the ADR-2128 depth lever: {seen:?}"
    );
}
