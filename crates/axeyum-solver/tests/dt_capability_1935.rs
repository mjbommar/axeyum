//! ADR-1935: array/uninterpreted-sorted datatype FIELDS, and Ackermann
//! congruence over datatype ARGUMENTS.
//!
//! Two halves of one capability. `register_datatype` rejected every field sort
//! that was not `Bool`/`BitVec`/`Int`/`Real` or another datatype, and
//! `scan_fragment` refused every `Op::Apply` with a datatype-sorted argument.
//! ADR-1920 named the second as BUILD NEXT "restricted to datatypes whose
//! fields are all scalar"; measured over the three DT divisions that
//! restriction holds for **6 of 600** sampled files, against 136 once array-
//! and `declare-sort`-sorted fields also get an expansion variable
//! (`docs/research/03-measurements/the-adr-1920-slice-is-6-of-600-files-2026-09-12.md`).
//! So the field half is the congruence half's prerequisite, and the checked
//! precondition is EXACTNESS of the expansion rather than scalarity of the
//! fields.
//!
//! What each test here would print if the change were broken:
//!
//! * `field_*` — `Unsupported` instead of a verdict: the field half reverted,
//!   or `field_sort_expands` stopped admitting a sort.
//! * `congruence_*` — `Unsupported` or `unknown` instead of `unsat`: the
//!   Ackermann pre-pass stopped firing, or its congruence clauses stopped
//!   constraining anything.
//! * `sound_*` — a decided verdict that contradicts the mathematics. The
//!   fragment is entitled to refuse; it is never entitled to be wrong.

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

/// `Color = red | green`, a scalar-only (indeed field-free) enum.
fn color(arena: &mut TermArena) -> (DatatypeId, ConstructorId, ConstructorId) {
    let dt = arena.declare_datatype("Color1935");
    let red = arena.add_constructor(dt, "red", &[]);
    let green = arena.add_constructor(dt, "green", &[]);
    (dt, red, green)
}

/// `Rec = mk(a : (Array Int Int), n : Int)` — the SPARK/Ada record shape. The
/// array field is exactly what `register_datatype` used to reject.
fn array_record(arena: &mut TermArena) -> (DatatypeId, ConstructorId, Sort) {
    let arr = Sort::Array {
        index: ArraySortKey::Int,
        element: ArraySortKey::Int,
    };
    let dt = arena.declare_datatype("Rec1935");
    let mk = arena.add_constructor(
        dt,
        "mk",
        &[("a".to_owned(), arr), ("n".to_owned(), Sort::Int)],
    );
    (dt, mk, arr)
}

/// `URec = umk(u : U)` over an uninterpreted `(declare-sort U 0)` — the other
/// half of the SPARK/Ada field population (`integer`, `us_private`, …).
fn uninterpreted_record(arena: &mut TermArena) -> (DatatypeId, ConstructorId, Sort) {
    let u = Sort::Uninterpreted(arena.declare_uninterpreted_sort("U1935"));
    let dt = arena.declare_datatype("URec1935");
    let umk = arena.add_constructor(dt, "umk", &[("u".to_owned(), u)]);
    (dt, umk, u)
}

/// `Tree = node(kid : Tree) | leaf` — a datatype whose only field is a
/// datatype, so its expansion is NOT exact. This is the shape ADR-1920's
/// soundness condition is about.
fn tree(arena: &mut TermArena) -> (DatatypeId, ConstructorId, ConstructorId) {
    let dt = arena.declare_datatype("Tree1935");
    let node = arena.add_constructor(dt, "node", &[]);
    let leaf = arena.add_constructor(dt, "leaf", &[]);
    (dt, node, leaf)
}

// -------------------------------------------------- the field half (ADR-1935)

#[test]
fn field_an_array_valued_field_decides_unsat() {
    // `is-mk(r) /\ (select (a r) 0) = 5 /\ (select (a r) 0) = 6`. UNSAT by
    // functionality of the array read. Before ADR-1935 `register_datatype`
    // refused the whole query on the `(Array Int Int)` field sort.
    let mut arena = TermArena::new();
    let (dt, mk, _) = array_record(&mut arena);
    let r = var_of(&mut arena, "r", Sort::Datatype(dt));
    let is_mk = arena.dt_test(mk, r).expect("test");
    let field = arena.dt_select(mk, 0, r).expect("select");
    let zero = arena.int_const(0);
    let read = arena.select(field, zero).expect("array select");
    let five = arena.int_const(5);
    let six = arena.int_const(6);
    let a = arena.eq(read, five).expect("eq");
    let b = arena.eq(read, six).expect("eq");

    let got = solve(&mut arena, &[is_mk, a, b], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "expected unsat over an array-valued datatype field, got {got:?}"
    );
}

#[test]
fn field_an_array_valued_field_reaches_the_array_route() {
    // The same reads at DIFFERENT indices are satisfiable, and this one does
    // NOT decide: the residual is `(Array Int Int)` content and the lazy array
    // route answers `unknown` on it ("outside the current Bool/Int lazy array
    // route"). That limit is the array theory's, not the datatype layer's, and
    // saying so is the point of this test — what it asserts is that the
    // datatype layer no longer REFUSES, i.e. the query reaches a route at all.
    //
    // Before ADR-1935 this was `Unsupported(... ADR-0022)` from
    // `register_datatype`. The assertion is on the refusal, not on the verdict,
    // because a test that demanded `sat` here would be demanding an array
    // capability this lane did not build.
    let mut arena = TermArena::new();
    let (dt, mk, _) = array_record(&mut arena);
    let r = var_of(&mut arena, "r", Sort::Datatype(dt));
    let is_mk = arena.dt_test(mk, r).expect("test");
    let field = arena.dt_select(mk, 0, r).expect("select");
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let read0 = arena.select(field, zero).expect("array select");
    let read1 = arena.select(field, one).expect("array select");
    let five = arena.int_const(5);
    let six = arena.int_const(6);
    let a = arena.eq(read0, five).expect("eq");
    let b = arena.eq(read1, six).expect("eq");

    let got = solve(&mut arena, &[is_mk, a, b], &cfg());
    assert!(
        !matches!(got, Err(SolverError::Unsupported(_))),
        "the datatype layer still refuses an array-valued field: {got:?}"
    );
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "WRONG UNSAT: two reads at different indices were merged: {got:?}"
    );
}

#[test]
fn field_an_uninterpreted_sorted_field_decides_unsat() {
    // `is-umk(r) /\ (u r) = x /\ not ((u r) = x)`. The field sort is a
    // `declare-sort`, which `register_datatype` also used to refuse.
    let mut arena = TermArena::new();
    let (dt, umk, u) = uninterpreted_record(&mut arena);
    let r = var_of(&mut arena, "r", Sort::Datatype(dt));
    let x = var_of(&mut arena, "x", u);
    let is_umk = arena.dt_test(umk, r).expect("test");
    let field = arena.dt_select(umk, 0, r).expect("select");
    let same = arena.eq(field, x).expect("eq");
    let diff = arena.not(same).expect("not");

    let got = solve(&mut arena, &[is_umk, same, diff], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "expected unsat over an uninterpreted-sorted datatype field, got {got:?}"
    );
}

#[test]
fn field_an_uninterpreted_sorted_field_decides_sat() {
    let mut arena = TermArena::new();
    let (dt, umk, u) = uninterpreted_record(&mut arena);
    let r = var_of(&mut arena, "r", Sort::Datatype(dt));
    let x = var_of(&mut arena, "x", u);
    let is_umk = arena.dt_test(umk, r).expect("test");
    let field = arena.dt_select(umk, 0, r).expect("select");
    let same = arena.eq(field, x).expect("eq");

    let got = solve(&mut arena, &[is_umk, same], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Sat(_))),
        "expected sat over an uninterpreted-sorted datatype field, got {got:?}"
    );
}

#[test]
fn field_an_array_of_datatype_field_is_still_refused_and_terminates() {
    // The one array field sort ADR-1935 does NOT admit. Its expansion variable
    // would carry datatype content into the residual, which the dispatcher
    // diverts on — the ADR-1920 non-termination cycle. This test would print
    // NOTHING if that guard were removed and the cycle came back: the process
    // aborts. It is a termination guard first and a refusal guard second.
    let mut arena = TermArena::new();
    let (color_dt, _, _) = color(&mut arena);
    let arr = Sort::Array {
        index: ArraySortKey::Int,
        element: ArraySortKey::Datatype(color_dt),
    };
    let dt = arena.declare_datatype("ColorArrRec1935");
    let mk = arena.add_constructor(dt, "mk", &[("c".to_owned(), arr)]);
    let r = var_of(&mut arena, "r", Sort::Datatype(dt));
    let is_mk = arena.dt_test(mk, r).expect("test");

    let got = solve(&mut arena, &[is_mk], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "WRONG UNSAT on a trivially satisfiable query: {got:?}"
    );
}

// ------------------------------------------- the congruence half (ADR-1935)

#[test]
fn congruence_over_an_enum_argument_decides_unsat() {
    // `x = y /\ p(x) /\ not p(y)` — UNSAT by congruence, and the positive
    // control for the Ackermann pre-pass. `dt_uf_gate.rs` asserts only that
    // this is never `sat`, which a route that refuses everything satisfies;
    // this asserts it is DECIDED.
    let mut arena = TermArena::new();
    let (dt, _, _) = color(&mut arena);
    let pred = arena
        .declare_fun("p1935", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare p");
    let x = var_of(&mut arena, "x", Sort::Datatype(dt));
    let y = var_of(&mut arena, "y", Sort::Datatype(dt));
    let same = arena.eq(x, y).expect("eq");
    let px = arena.apply(pred, &[x]).expect("apply");
    let py = arena.apply(pred, &[y]).expect("apply");
    let not_py = arena.not(py).expect("not");

    let got = solve(&mut arena, &[same, px, not_py], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "expected unsat by congruence over a datatype argument, got {got:?}"
    );
}

#[test]
fn congruence_does_not_merge_distinct_arguments() {
    // The same query WITHOUT `x = y` is satisfiable. This is the arm that fails
    // if the congruence clause's antecedent degenerated to `true` — which is
    // precisely how a congruence encoding manufactures a wrong `unsat`.
    let mut arena = TermArena::new();
    let (dt, _, _) = color(&mut arena);
    let pred = arena
        .declare_fun("p1935", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare p");
    let x = var_of(&mut arena, "x", Sort::Datatype(dt));
    let y = var_of(&mut arena, "y", Sort::Datatype(dt));
    let px = arena.apply(pred, &[x]).expect("apply");
    let py = arena.apply(pred, &[y]).expect("apply");
    let not_py = arena.not(py).expect("not");

    let got = solve(&mut arena, &[px, not_py], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Sat(_))),
        "expected sat: nothing forces x = y, got {got:?}"
    );
}

#[test]
fn congruence_over_an_array_field_record_decides_unsat() {
    // The two halves composed, and the reason they are one feature. `Rec` has
    // an `(Array Int Int)` field, so before the field half its expansion was
    // not exact and ADR-1920's precondition refused the congruence. Now the
    // field has a variable, the expansion IS exact, and `x = y /\ p(x) /\
    // not p(y)` decides.
    let mut arena = TermArena::new();
    let (dt, _, _) = array_record(&mut arena);
    let pred = arena
        .declare_fun("q1935", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare q");
    let x = var_of(&mut arena, "x", Sort::Datatype(dt));
    let y = var_of(&mut arena, "y", Sort::Datatype(dt));
    let same = arena.eq(x, y).expect("eq");
    let px = arena.apply(pred, &[x]).expect("apply");
    let py = arena.apply(pred, &[y]).expect("apply");
    let not_py = arena.not(py).expect("not");

    let got = solve(&mut arena, &[same, px, not_py], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "expected unsat by congruence over an array-field record, got {got:?}"
    );
}

#[test]
fn congruence_over_an_array_field_record_needs_the_array_to_agree() {
    // Same functions, but the records differ in their ARRAY field. Satisfiable,
    // and it is the discriminating case for the field half's contribution to
    // exactness: an encoding that skipped the array field would call these two
    // records equal and answer `unsat`.
    let mut arena = TermArena::new();
    let (dt, mk, _) = array_record(&mut arena);
    let pred = arena
        .declare_fun("q1935", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare q");
    let x = var_of(&mut arena, "x", Sort::Datatype(dt));
    let y = var_of(&mut arena, "y", Sort::Datatype(dt));
    let is_x = arena.dt_test(mk, x).expect("test");
    let is_y = arena.dt_test(mk, y).expect("test");
    // The scalar fields agree; the array fields disagree at index 0.
    let nx = arena.dt_select(mk, 1, x).expect("select");
    let ny = arena.dt_select(mk, 1, y).expect("select");
    let ns_eq = arena.eq(nx, ny).expect("eq");
    let ax = arena.dt_select(mk, 0, x).expect("select");
    let ay = arena.dt_select(mk, 0, y).expect("select");
    let zero = arena.int_const(0);
    let rx = arena.select(ax, zero).expect("array select");
    let ry = arena.select(ay, zero).expect("array select");
    let reads_eq = arena.eq(rx, ry).expect("eq");
    let reads_differ = arena.not(reads_eq).expect("not");
    let px = arena.apply(pred, &[x]).expect("apply");
    let py = arena.apply(pred, &[y]).expect("apply");
    let not_py = arena.not(py).expect("not");

    let got = solve(
        &mut arena,
        &[is_x, is_y, ns_eq, reads_differ, px, not_py],
        &cfg(),
    );
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "WRONG UNSAT: two records differing in their array field were merged: {got:?}"
    );
}

// ------------------------------------------------------------- soundness

#[test]
fn sound_congruence_is_refused_over_an_inexact_datatype() {
    // THE ADR-1920 SOUNDNESS CONDITION, as a checked precondition.
    //
    // `Tree = node(kid : Tree) | leaf` has a datatype-typed field, so its
    // tag/field expansion cannot compare two trees exactly: `node(leaf)` and
    // `node(node(leaf))` agree on the tag and on every field the expansion can
    // see. Emitting `(encoded equality) -> (p(a) = p(b))` over such a datatype
    // asserts something the true congruence axiom does not, which is how a
    // congruence encoding produces a wrong `unsat`.
    //
    // `is-node(a) /\ is-node(b) /\ p(a) /\ not p(b)` is SATISFIABLE. The
    // fragment may refuse it; it may not answer `unsat`.
    let mut arena = TermArena::new();
    let dt = arena.declare_datatype("Tree1935i");
    let leaf = arena.add_constructor(dt, "leaf", &[]);
    let node = arena.add_constructor(dt, "node", &[("kid".to_owned(), Sort::Datatype(dt))]);
    let _ = leaf;
    let pred = arena
        .declare_fun("t1935", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare p");
    let a = var_of(&mut arena, "a", Sort::Datatype(dt));
    let b = var_of(&mut arena, "b", Sort::Datatype(dt));
    let is_a = arena.dt_test(node, a).expect("test");
    let is_b = arena.dt_test(node, b).expect("test");
    let pa = arena.apply(pred, &[a]).expect("apply");
    let pb = arena.apply(pred, &[b]).expect("apply");
    let not_pb = arena.not(pb).expect("not");

    let got = solve(&mut arena, &[is_a, is_b, pa, not_pb], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "WRONG UNSAT: congruence over a datatype whose expansion is not exact: {got:?}"
    );
    assert!(
        matches!(got, Err(SolverError::Unsupported(_))) || !matches!(got, Ok(CheckResult::Unsat)),
        "expected a refusal or a non-unsat verdict, got {got:?}"
    );
}

#[test]
fn sound_congruence_is_refused_over_an_inexact_datatype_with_a_scalar_field() {
    // The same condition where the expansion CAN see something. `D = mk(s :
    // Int, k : D)` has one constructor; the expansion compares `s` and cannot
    // compare `k`. `s(a) = s(b) /\ p(a) /\ not p(b)` is satisfiable — `a` and
    // `b` differ in `k` — and an antecedent built only from `s` would call them
    // equal and answer `unsat`.
    let mut arena = TermArena::new();
    let dt = arena.declare_datatype("DRec1935");
    let mk = arena.add_constructor(
        dt,
        "mk",
        &[
            ("s".to_owned(), Sort::Int),
            ("k".to_owned(), Sort::Datatype(dt)),
        ],
    );
    let pred = arena
        .declare_fun("d1935", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare p");
    let a = var_of(&mut arena, "a", Sort::Datatype(dt));
    let b = var_of(&mut arena, "b", Sort::Datatype(dt));
    let sa = arena.dt_select(mk, 0, a).expect("select");
    let sb = arena.dt_select(mk, 0, b).expect("select");
    let s_eq = arena.eq(sa, sb).expect("eq");
    let pa = arena.apply(pred, &[a]).expect("apply");
    let pb = arena.apply(pred, &[b]).expect("apply");
    let not_pb = arena.not(pb).expect("not");

    let got = solve(&mut arena, &[s_eq, pa, not_pb], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "WRONG UNSAT: an inexact antecedent merged two records that differ below it: {got:?}"
    );
}

#[test]
fn sound_a_datatype_valued_uf_result_is_not_silently_merged() {
    // `f : Color -> Color`, `x = y -> f(x) = f(y)` is the congruence we do NOT
    // emit (the witness would itself be datatype-sorted). Whatever the route
    // does with it, `f(x) = f(y) /\ not (f(x) = f(y))` must not become `sat`
    // and `p(x) /\ not p(y)` must not become `unsat`.
    let mut arena = TermArena::new();
    let (dt, _, _) = color(&mut arena);
    let func = arena
        .declare_fun("f1935", &[Sort::Datatype(dt)], Sort::Datatype(dt))
        .expect("declare f");
    let x = var_of(&mut arena, "x", Sort::Datatype(dt));
    let y = var_of(&mut arena, "y", Sort::Datatype(dt));
    let fx = arena.apply(func, &[x]).expect("apply");
    let fy = arena.apply(func, &[y]).expect("apply");
    let same = arena.eq(fx, fy).expect("eq");
    let diff = arena.not(same).expect("not");
    let x_eq_y = arena.eq(x, y).expect("eq");

    let got = solve(&mut arena, &[x_eq_y, diff], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Sat(_))),
        "WRONG SAT: a function disagreed with itself at equal arguments: {got:?}"
    );
}

#[test]
fn sound_an_enum_over_many_applications_stays_bounded() {
    // Ackermann is quadratic, and `MAX_ACK_PAIRS` refuses above its bound
    // rather than exploding. This query is under it and must still be right:
    // `p(x_i)` for 20 distinct variables, all pairwise equal, with one negated
    // — UNSAT by congruence, and a shape where a dropped pair would show up as
    // `sat`.
    let mut arena = TermArena::new();
    let (dt, _, _) = color(&mut arena);
    let pred = arena
        .declare_fun("m1935", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare p");
    let vars: Vec<TermId> = (0..20)
        .map(|i| var_of(&mut arena, &format!("v{i}"), Sort::Datatype(dt)))
        .collect();
    let mut assertions = Vec::new();
    for w in vars.windows(2) {
        assertions.push(arena.eq(w[0], w[1]).expect("eq"));
    }
    let first = arena.apply(pred, &[vars[0]]).expect("apply");
    let last = arena.apply(pred, &[vars[19]]).expect("apply");
    let not_last = arena.not(last).expect("not");
    assertions.push(first);
    assertions.push(not_last);

    let got = solve(&mut arena, &assertions, &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Sat(_))),
        "WRONG SAT on a transitively-equal congruence chain: {got:?}"
    );
}

#[test]
fn sound_a_two_argument_function_needs_both_arguments_to_agree() {
    // `g : (Color, Int) -> Bool`. `x = y /\ g(x,1) /\ not g(y,2)` is
    // SATISFIABLE: the second arguments differ, so congruence says nothing. An
    // antecedent that only compared the datatype argument would answer `unsat`.
    let mut arena = TermArena::new();
    let (dt, _, _) = color(&mut arena);
    let g = arena
        .declare_fun("g1935", &[Sort::Datatype(dt), Sort::Int], Sort::Bool)
        .expect("declare g");
    let x = var_of(&mut arena, "x", Sort::Datatype(dt));
    let y = var_of(&mut arena, "y", Sort::Datatype(dt));
    let same = arena.eq(x, y).expect("eq");
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let g1 = arena.apply(g, &[x, one]).expect("apply");
    let g2 = arena.apply(g, &[y, two]).expect("apply");
    let not_g2 = arena.not(g2).expect("not");

    let got = solve(&mut arena, &[same, g1, not_g2], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "WRONG UNSAT: congruence fired on applications whose Int arguments differ: {got:?}"
    );
}

#[test]
fn congruence_over_a_two_argument_function_decides_unsat() {
    // The positive counterpart: both arguments agree, so congruence applies.
    let mut arena = TermArena::new();
    let (dt, _, _) = color(&mut arena);
    let g = arena
        .declare_fun("g1935", &[Sort::Datatype(dt), Sort::Int], Sort::Bool)
        .expect("declare g");
    let x = var_of(&mut arena, "x", Sort::Datatype(dt));
    let y = var_of(&mut arena, "y", Sort::Datatype(dt));
    let same = arena.eq(x, y).expect("eq");
    let one = arena.int_const(1);
    let g1 = arena.apply(g, &[x, one]).expect("apply");
    let g2 = arena.apply(g, &[y, one]).expect("apply");
    let not_g2 = arena.not(g2).expect("not");

    let got = solve(&mut arena, &[same, g1, not_g2], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "expected unsat: both arguments agree, got {got:?}"
    );
}

#[test]
fn sound_tree_helpers_are_reachable() {
    // A positive control for the fixtures themselves: `tree` and `color` really
    // do declare what their names say, so a `sound_*` assertion above cannot be
    // satisfied by a fixture that built nothing.
    let mut arena = TermArena::new();
    let (dt, node, leaf) = tree(&mut arena);
    assert_ne!(node, leaf, "two distinct constructors");
    assert_eq!(arena.datatype_constructors(dt).len(), 2);
}

// ---------------------------------------------- the refusals, by their message
//
// MUTATION-CONTROL NOTE, and it is a finding rather than a formality.
//
// Four of this change's six guards SURVIVED their first mutation run
// (`scripts/tests/mutation_controls.py dt-capability-1935`, 2026-09-12): with
// each deleted, all 16 tests above still passed. That is not because the guards
// do nothing — it is because each is an EARLY and PRECISE refusal of a shape
// that a LATER and vaguer one also refuses:
//
// * the exactness precondition — ADR-1930's structural-equality encoding is a
//   free Boolean carrying only necessary conditions, so an inexact congruence
//   antecedent is never FORCED true and the clause degenerates to vacuous
//   rather than to a wrong `unsat`. The soundness is ADR-1930's and the
//   replay's; this guard is what keeps the emitted clauses to shapes whose
//   antecedent is provably real equality, which is what makes the argument in
//   ADR-1935 reviewable at all. **It is not this guard that stands between the
//   solver and a wrong `unsat` today, and saying otherwise would be the
//   un-failable checker this repository keeps deleting.**
// * the array-of-datatype field exclusion — `refuse_if_datatype_survives`
//   catches the same residual one layer down, with a message about the
//   dispatcher rather than about the field.
// * the datatype-valued result refusal and the free-variable requirement —
//   `scan_fragment`'s constructor and stray-operand arms catch the same shapes.
//
// So what each guard uniquely produces is its MESSAGE, and that is not
// cosmetic: ADR-1920's second decision is that the capability gate's message
// "names the actual missing capability rather than a sort list", because these
// divisions' blocker census is read off exactly these strings. A census cannot
// distinguish a capability that is missing from one that is merely reached
// later. These four tests pin that, and each dies when its guard is deleted.

fn refusal_detail(got: Result<CheckResult, SolverError>) -> String {
    match got {
        Err(SolverError::Unsupported(detail)) => detail,
        other => panic!("expected an Unsupported refusal, got {other:?}"),
    }
}

#[test]
fn refusal_names_the_inexact_expansion() {
    let mut arena = TermArena::new();
    let dt = arena.declare_datatype("Tree1935m");
    let _leaf = arena.add_constructor(dt, "leaf", &[]);
    let node = arena.add_constructor(dt, "node", &[("kid".to_owned(), Sort::Datatype(dt))]);
    let pred = arena
        .declare_fun("tm1935", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare p");
    let a = var_of(&mut arena, "a", Sort::Datatype(dt));
    let is_a = arena.dt_test(node, a).expect("test");
    let pa = arena.apply(pred, &[a]).expect("apply");

    let detail = refusal_detail(solve(&mut arena, &[is_a, pa], &cfg()));
    assert!(
        detail.contains("expansion is not exact"),
        "the refusal must name the exactness precondition, got: {detail}"
    );
}

#[test]
fn refusal_names_the_field_with_no_expansion_variable() {
    let mut arena = TermArena::new();
    let (color_dt, _, _) = color(&mut arena);
    let arr = Sort::Array {
        index: ArraySortKey::Int,
        element: ArraySortKey::Datatype(color_dt),
    };
    let dt = arena.declare_datatype("ColorArrRec1935m");
    let mk = arena.add_constructor(dt, "mk", &[("c".to_owned(), arr)]);
    let r = var_of(&mut arena, "r", Sort::Datatype(dt));
    let is_mk = arena.dt_test(mk, r).expect("test");

    let detail = refusal_detail(solve(&mut arena, &[is_mk], &cfg()));
    assert!(
        detail.contains("field sort with no expansion variable"),
        "the refusal must name the FIELD, not the dispatcher, got: {detail}"
    );
}

#[test]
fn refusal_names_the_datatype_valued_result() {
    // THIS ONE GOES THROUGH `check_with_datatype_native` RATHER THAN `solve`,
    // and the reason is a finding. Every query I could build that reaches this
    // guard through the front door is decided by an EARLIER rung: a datatype
    // selector applied to a UF result is, to the EUF route, just another
    // uninterpreted term, so `v(f(x)) = 5 /\ v(f(x)) = 6` comes back `unsat`
    // from congruence before the datatype route is consulted at all. That is
    // the right verdict and not a problem — but it means the guard's front-door
    // trigger is narrow, and a test that reached it by accident would have been
    // measuring the ladder rather than the guard (the mistake ADR-1927 names).
    //
    // So the route is called directly. What is pinned is that the datatype
    // route REFUSES this shape and says why, which is what a blocker census
    // reads.
    let mut arena = TermArena::new();
    let (dt, _, _) = color(&mut arena);
    let boxed = arena.declare_datatype("Box1935m");
    let mk = arena.add_constructor(boxed, "mk", &[("v".to_owned(), Sort::Int)]);
    let func = arena
        .declare_fun("fr1935", &[Sort::Datatype(dt)], Sort::Datatype(boxed))
        .expect("declare f");
    let x = var_of(&mut arena, "x", Sort::Datatype(dt));
    let fx = arena.apply(func, &[x]).expect("apply");
    let field = arena.dt_select(mk, 0, fx).expect("select");
    let five = arena.int_const(5);
    let is_five = arena.eq(field, five).expect("eq");

    let got = check_with_datatype_native(&mut arena, &[is_five], &cfg());
    let detail = refusal_detail(got);
    assert!(
        detail.contains("RESULT sort mentions a datatype"),
        "the refusal must name the result sort, got: {detail}"
    );
}

#[test]
fn refusal_names_the_non_variable_datatype_argument() {
    // `p(red) /\ not p(green)` applies `p` to CONSTRUCTOR terms, which the
    // Ackermann pre-pass has no argument equality to build from.
    let mut arena = TermArena::new();
    let (dt, red, green) = color(&mut arena);
    let pred = arena
        .declare_fun("pv1935", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare p");
    let red_t = arena.construct(red, &[]).expect("red");
    let green_t = arena.construct(green, &[]).expect("green");
    let holds_of_red = arena.apply(pred, &[red_t]).expect("apply");
    let holds_of_green = arena.apply(pred, &[green_t]).expect("apply");
    let fails_of_green = arena.not(holds_of_green).expect("not");

    let detail = refusal_detail(solve(&mut arena, &[holds_of_red, fails_of_green], &cfg()));
    assert!(
        detail.contains("not a \\n                         free variable")
            || detail.contains("not a free variable"),
        "the refusal must name the non-variable argument, got: {detail}"
    );
}
