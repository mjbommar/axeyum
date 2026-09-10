//! Integration tests for word-level preprocessing (P1.2) through the real
//! pure-Rust sat-bv backend: `check_with_preprocessing` must eliminate variables
//! before solving and return a model over the *original* symbols that satisfies
//! the *original* assertions.
#![cfg(feature = "full")]

use axeyum_ir::{FuncId, FuncValue, Rational, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, SatBvBackend, SolverConfig, check_auto, check_with_preprocessing,
};

fn check(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    let mut backend = SatBvBackend::new();
    check_with_preprocessing(&mut backend, arena, assertions, &SolverConfig::default())
        .expect("preprocessing + sat-bv backend succeeds")
}

fn assert_model_satisfies(arena: &TermArena, model: &axeyum_solver::Model, originals: &[TermId]) {
    let assignment = model.to_assignment();
    for &a in originals {
        assert_eq!(
            eval(arena, a, &assignment).unwrap(),
            Value::Bool(true),
            "returned model must satisfy original assertion #{}",
            a.index()
        );
    }
}

#[test]
fn constant_pin_is_eliminated_and_reconstructed() {
    // x = 7 ∧ x + y = 10. propagate_values pins x; the model must still assign it.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let seven = arena.bv_const(8, 7).unwrap();
    let ten = arena.bv_const(8, 10).unwrap();
    let x_is_7 = arena.eq(xv, seven).unwrap();
    let sum = arena.bv_add(xv, yv).unwrap();
    let sum_is_10 = arena.eq(sum, ten).unwrap();
    let originals = [x_is_7, sum_is_10];

    let CheckResult::Sat(model) = check(&mut arena, &originals) else {
        panic!("expected sat");
    };
    assert_eq!(model.get(x), Some(Value::Bv { width: 8, value: 7 }));
    assert_eq!(model.get(y), Some(Value::Bv { width: 8, value: 3 }));
    assert_model_satisfies(&arena, &model, &originals);
}

#[test]
fn variable_definition_is_solved_and_reconstructed() {
    // x = y + 1 ∧ x * y = 12. solve_eqs substitutes x := y + 1.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let one = arena.bv_const(8, 1).unwrap();
    let y1 = arena.bv_add(yv, one).unwrap();
    let x_def = arena.eq(xv, y1).unwrap();
    let prod = arena.bv_mul(xv, yv).unwrap();
    let twelve = arena.bv_const(8, 12).unwrap();
    let prod_is_12 = arena.eq(prod, twelve).unwrap();
    let originals = [x_def, prod_is_12];

    let CheckResult::Sat(model) = check(&mut arena, &originals) else {
        panic!("expected sat");
    };
    // Whatever y the backend chose, x = y + 1 must hold and x*y = 12.
    assert_model_satisfies(&arena, &model, &originals);
}

#[test]
fn conflicting_constants_are_unsat_after_preprocessing() {
    // x = 5 ∧ x = 6: propagate_values pins x = 5, leaving the false (5 = 6).
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let xv = arena.var(x);
    let five = arena.bv_const(8, 5).unwrap();
    let six = arena.bv_const(8, 6).unwrap();
    let x_is_5 = arena.eq(xv, five).unwrap();
    let x_is_6 = arena.eq(xv, six).unwrap();

    assert_eq!(check(&mut arena, &[x_is_5, x_is_6]), CheckResult::Unsat);
}

#[test]
fn pure_problem_without_facts_passes_through() {
    // No top-level variable=term fact; the backend solves the whole thing and the
    // model still satisfies the originals.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(4)).unwrap();
    let y = arena.declare("y", Sort::BitVec(4)).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let sum = arena.bv_add(xv, yv).unwrap();
    let nine = arena.bv_const(4, 9).unwrap();
    let sum_is_9 = arena.eq(sum, nine).unwrap();
    let lt = arena.bv_ult(xv, yv).unwrap();
    let originals = [sum_is_9, lt];

    let CheckResult::Sat(model) = check(&mut arena, &originals) else {
        panic!("expected sat");
    };
    assert_model_satisfies(&arena, &model, &originals);
}

#[test]
fn chained_definitions_all_reconstruct() {
    // x = y + 1 ∧ y = z ∧ z + 0 = 4  (z anchored via an arithmetic fact).
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let z = arena.declare("z", Sort::BitVec(8)).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let zv = arena.var(z);
    let one = arena.bv_const(8, 1).unwrap();
    let y1 = arena.bv_add(yv, one).unwrap();
    let x_def = arena.eq(xv, y1).unwrap();
    let y_def = arena.eq(yv, zv).unwrap();
    let four = arena.bv_const(8, 4).unwrap();
    let z_is_4 = arena.eq(zv, four).unwrap();
    let originals = [x_def, y_def, z_is_4];

    let CheckResult::Sat(model) = check(&mut arena, &originals) else {
        panic!("expected sat");
    };
    assert_eq!(model.get(z), Some(Value::Bv { width: 8, value: 4 }));
    assert_eq!(model.get(y), Some(Value::Bv { width: 8, value: 4 }));
    assert_eq!(model.get(x), Some(Value::Bv { width: 8, value: 5 }));
    assert_model_satisfies(&arena, &model, &originals);
}

/// Multiplier-commutativity is refuted by canonicalization alone — no multiplier
/// bit-blasting. `(not (= (a*b) (b*a)))` is unsat; commutative-operand ordering
/// makes the two products coincide, so the canonicalizer folds the equality to
/// `true` and the negation to `false`. Wide operands (32-bit) would make a
/// genuine multiplier blast slow; this returns immediately.
#[test]
fn multiplier_commutativity_is_refuted_by_canonicalization() {
    let mut arena = TermArena::new();
    let a = arena.declare("a", Sort::BitVec(32)).unwrap();
    let b = arena.declare("b", Sort::BitVec(32)).unwrap();
    let av = arena.var(a);
    let bv = arena.var(b);
    let ab = arena.bv_mul(av, bv).unwrap();
    let ba = arena.bv_mul(bv, av).unwrap();
    let eq = arena.eq(ab, ba).unwrap();
    let neq = arena.not(eq).unwrap();

    assert_eq!(
        check(&mut arena, &[neq]),
        CheckResult::Unsat,
        "a*b = b*a, so its negation is unsat — decided by canonicalization, not blasting"
    );
}

/// AC-flattening refutes a commute-shaped instance over a multiplier *tree*,
/// across intermediate variable bindings: `s1 = a*(b*c)`, `s2 = c*(a*b)`, and
/// `(not (= s1 s2))`. `solve_eqs` inlines `s1`/`s2`, and the assertion is
/// canonicalized so both products AC-normalize to the same term, fold the
/// equality to `true`, and the negation to `false` — unsat with no 32-bit
/// multiplier-tree bit-blasting.
#[test]
fn ac_multiplier_tree_commute_is_refuted_by_preprocessing() {
    let mut arena = TermArena::new();
    let a = arena.declare("a", Sort::BitVec(32)).unwrap();
    let b = arena.declare("b", Sort::BitVec(32)).unwrap();
    let c = arena.declare("c", Sort::BitVec(32)).unwrap();
    let s1 = arena.declare("s1", Sort::BitVec(32)).unwrap();
    let s2 = arena.declare("s2", Sort::BitVec(32)).unwrap();
    let av = arena.var(a);
    let bv = arena.var(b);
    let cv = arena.var(c);
    let s1v = arena.var(s1);
    let s2v = arena.var(s2);

    let bc = arena.bv_mul(bv, cv).unwrap();
    let abc = arena.bv_mul(av, bc).unwrap(); // a*(b*c)
    let ab = arena.bv_mul(av, bv).unwrap();
    let cab = arena.bv_mul(cv, ab).unwrap(); // c*(a*b)

    let s1_def = arena.eq(s1v, abc).unwrap();
    let s2_def = arena.eq(s2v, cab).unwrap();
    let eq = arena.eq(s1v, s2v).unwrap();
    let neq = arena.not(eq).unwrap();
    let originals = [s1_def, s2_def, neq];

    assert_eq!(
        check(&mut arena, &originals),
        CheckResult::Unsat,
        "s1 = a*(b*c), s2 = c*(a*b); s1 != s2 is unsat by AC-normalization, not blasting"
    );
}

/// `elim_unconstrained` (T1.2.4) fires end-to-end: in `(bvult (bvadd x y) 100) ∧
/// (bvugt y 1)`, `x` occurs once, so the `bvadd` is unconstrained and dropped; the
/// `sat` model must still recover `x` and satisfy the original assertions.
#[test]
fn unconstrained_layer_is_eliminated_and_sat_model_reconstructs() {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let (xv, yv) = (arena.var(x), arena.var(y));
    let sum = arena.bv_add(xv, yv).unwrap();
    let hundred = arena.bv_const(8, 100).unwrap();
    let a1 = arena.bv_ult(sum, hundred).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let a2 = arena.bv_ugt(yv, one).unwrap();
    let originals = [a1, a2];

    let CheckResult::Sat(model) = check(&mut arena, &originals) else {
        panic!("expected sat");
    };
    assert!(model.get(x).is_some(), "eliminated x must be reconstructed");
    assert_model_satisfies(&arena, &model, &originals);
}

/// `elim_unconstrained` must not change an `unsat` verdict: the contradiction
/// lives in the surviving variable `y` (`y > 200 ∧ y < 50`), while `x`'s `bvadd`
/// layer is unconstrained and eliminated. Still unsat.
#[test]
fn unconstrained_elimination_preserves_unsat() {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let (xv, yv) = (arena.var(x), arena.var(y));
    let sum = arena.bv_add(xv, yv).unwrap();
    let hundred = arena.bv_const(8, 100).unwrap();
    let a1 = arena.bv_ult(sum, hundred).unwrap();
    let two_hundred = arena.bv_const(8, 200).unwrap();
    let fifty = arena.bv_const(8, 50).unwrap();
    let a2 = arena.bv_ugt(yv, two_hundred).unwrap();
    let a3 = arena.bv_ult(yv, fifty).unwrap();

    assert_eq!(
        check(&mut arena, &[a1, a2, a3]),
        CheckResult::Unsat,
        "y > 200 ∧ y < 50 is unsat; eliminating x's add must not change that"
    );
}

/// The **product path** (`check_auto` / `solve`) honors `config.preprocess` by
/// running the full model-sound pipeline (not just canonicalization, ADR-0037):
/// `solve_eqs` eliminates `x = y + 1`, the reduced problem is solved, and the
/// returned model reconstructs `x` and satisfies the ORIGINAL assertions.
#[test]
fn check_auto_preprocess_eliminates_and_reconstructs_on_the_product_path() {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let (xv, yv) = (arena.var(x), arena.var(y));
    let one = arena.bv_const(8, 1).unwrap();
    let y_plus_1 = arena.bv_add(yv, one).unwrap();
    let x_def = arena.eq(xv, y_plus_1).unwrap(); // x = y + 1  (solve_eqs eliminates x)
    let ten = arena.bv_const(8, 10).unwrap();
    let x_is_10 = arena.eq(xv, ten).unwrap(); // x = 10  ⇒  y = 9
    let originals = [x_def, x_is_10];

    let config = SolverConfig::default().with_preprocess(true);
    let CheckResult::Sat(model) = check_auto(&mut arena, &originals, &config).unwrap() else {
        panic!("x = y+1 ∧ x = 10 is sat (y=9, x=10)");
    };
    // The reconstructed model assigns the eliminated `x` and satisfies the originals.
    assert_model_satisfies(&arena, &model, &originals);
    assert_eq!(
        model.to_assignment().get(x),
        Some(Value::Bv {
            width: 8,
            value: 10
        })
    );
    assert_eq!(
        model.to_assignment().get(y),
        Some(Value::Bv { width: 8, value: 9 })
    );
}

/// **Default-flip soundness guard (ADR-0034/0037):** with `preprocess` now default-on,
/// the `solve()` path with preprocessing must agree with preprocessing-off on every
/// instance — same verdict, no DISAGREE. A battery of `QF_BV` + `LIA` sat/unsat cases is
/// solved both ways and the verdicts compared (an `Unknown` from either side is not a
/// disagreement). Guards the global default flip against any reduction-induced unsoundness.
#[test]
fn preprocess_on_off_agree_on_a_battery() {
    use axeyum_solver::{CheckResult, solve};

    fn verdict(r: &CheckResult) -> Option<bool> {
        match r {
            CheckResult::Sat(_) => Some(true),
            CheckResult::Unsat => Some(false),
            CheckResult::Unknown(_) => None,
        }
    }

    let mut arena = TermArena::new();
    // Build a battery of (name, assertions) with mixed sat/unsat over BV and Int.
    let mut cases: Vec<(&str, Vec<TermId>)> = Vec::new();
    {
        // BV: x = y + 1 ∧ x = 10  (sat, y=9).
        let x = arena.declare("bx", Sort::BitVec(8)).unwrap();
        let y = arena.declare("by", Sort::BitVec(8)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let one = arena.bv_const(8, 1).unwrap();
        let y1 = arena.bv_add(yv, one).unwrap();
        let xdef = arena.eq(xv, y1).unwrap();
        let ten = arena.bv_const(8, 10).unwrap();
        let x10 = arena.eq(xv, ten).unwrap();
        cases.push(("bv_sat", vec![xdef, x10]));
        // BV unsat: x = 5 ∧ x = 6.
        let five = arena.bv_const(8, 5).unwrap();
        let six = arena.bv_const(8, 6).unwrap();
        let x5 = arena.eq(xv, five).unwrap();
        let x6 = arena.eq(xv, six).unwrap();
        cases.push(("bv_unsat", vec![x5, x6]));
        // Int unsat: 5 ≤ z ≤ 2.
        let z = arena.declare("iz", Sort::Int).unwrap();
        let zv = arena.var(z);
        let two = arena.int_const(2);
        let fivei = arena.int_const(5);
        let lo = arena.int_ge(zv, fivei).unwrap();
        let hi = arena.int_le(zv, two).unwrap();
        cases.push(("int_unsat", vec![lo, hi]));
        // Int sat: 0 ≤ w ≤ 3 ∧ w = 2.
        let w = arena.declare("iw", Sort::Int).unwrap();
        let wv = arena.var(w);
        let zero = arena.int_const(0);
        let threei = arena.int_const(3);
        let twoi = arena.int_const(2);
        let wlo = arena.int_ge(wv, zero).unwrap();
        let whi = arena.int_le(wv, threei).unwrap();
        let weq = arena.eq(wv, twoi).unwrap();
        cases.push(("int_sat", vec![wlo, whi, weq]));
    }

    let on = SolverConfig::default(); // preprocess defaults ON now
    assert!(on.preprocess, "this guard assumes preprocess defaults on");
    let off = SolverConfig::default().with_preprocess(false);
    for (name, asserts) in &cases {
        let r_on = solve(&mut arena, asserts, &on).unwrap();
        let r_off = solve(&mut arena, asserts, &off).unwrap();
        if let (Some(a), Some(b)) = (verdict(&r_on), verdict(&r_off)) {
            assert_eq!(
                a, b,
                "{name}: preprocess on/off DISAGREE ({r_on:?} vs {r_off:?})"
            );
        }
    }
}

#[test]
fn fixpoint_resolves_a_deep_definition_chain() {
    use axeyum_solver::{CheckResult, solve};
    // A definitional chain whose layers collapse fully only when the reductions are
    // ITERATED: w = 2 ∧ x1 = w+1 ∧ x2 = x1+1 ∧ x3 = x2+1 forces x3 = 5. The fixpoint
    // must resolve the whole chain (not just one layer) so the goal decides without
    // bit-blasting a wide search; the result is replay-checked against the originals.
    let mut arena = TermArena::new();
    let w = arena.declare("cw", Sort::BitVec(8)).unwrap();
    let x1 = arena.declare("cx1", Sort::BitVec(8)).unwrap();
    let x2 = arena.declare("cx2", Sort::BitVec(8)).unwrap();
    let x3 = arena.declare("cx3", Sort::BitVec(8)).unwrap();
    let (wv, x1v, x2v, x3v) = (arena.var(w), arena.var(x1), arena.var(x2), arena.var(x3));
    let one = arena.bv_const(8, 1).unwrap();
    let two = arena.bv_const(8, 2).unwrap();
    let w_is_2 = arena.eq(wv, two).unwrap();
    let w1 = arena.bv_add(wv, one).unwrap();
    let x1_def = arena.eq(x1v, w1).unwrap();
    let x1p1 = arena.bv_add(x1v, one).unwrap();
    let x2_def = arena.eq(x2v, x1p1).unwrap();
    let x2p1 = arena.bv_add(x2v, one).unwrap();
    let x3_def = arena.eq(x3v, x2p1).unwrap();

    // Consistent (x3 = 5): sat, model replays against the originals.
    let five = arena.bv_const(8, 5).unwrap();
    let x3_is_5 = arena.eq(x3v, five).unwrap();
    let sat_case = [w_is_2, x1_def, x2_def, x3_def, x3_is_5];
    let CheckResult::Sat(model) = check(&mut arena, &sat_case) else {
        panic!("consistent definition chain must be sat");
    };
    assert_eq!(model.get(x3), Some(Value::Bv { width: 8, value: 5 }));
    assert_model_satisfies(&arena, &model, &sat_case);

    // Contradictory (x3 = 9 ≠ 5): unsat, and preprocess agrees with no-preprocess.
    let nine = arena.bv_const(8, 9).unwrap();
    let x3_is_9 = arena.eq(x3v, nine).unwrap();
    let unsat_case = [w_is_2, x1_def, x2_def, x3_def, x3_is_9];
    assert!(
        matches!(check(&mut arena, &unsat_case), CheckResult::Unsat),
        "contradicted chain must be unsat after fixpoint preprocessing"
    );
    assert!(matches!(
        solve(&mut arena, &unsat_case, &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}

// ===========================================================================
// ADR-1811: `replay_preprocessed_model` is the ONE place that decides which
// witness kinds a preprocessed model carries.
// ===========================================================================
//
// Until 2026-09-09 there were two copies of the reduce + replay: this module's
// and `auto::dispatch_reduced`'s. They drifted — `auto` gained the
// uninterpreted-function carry on 2026-07-02 (`124e18aa0`) and `preprocess` did
// not — so a model handed back through `check_with_preprocessing` silently lost
// every function interpretation. The tests below pin all three carries.
//
// The backend here is canned ON PURPOSE. The carries are a property of the
// replay, not of any theory route, and no shipped route decides a query that
// needs a `/0` witness AND a function interpretation at once (see the
// `front_door_*` tests below, which cover the two kinds separately). A canned
// backend that CHECKS its own candidate against the reduced query is the only
// way to put both witness kinds through the merged path in one fixture.

/// A backend that answers with a fixed candidate model and **verifies it**
/// against whatever reduced query the preprocessing pipeline hands it. If the
/// reduction were unsound, the candidate would stop satisfying the reduced
/// query and this returns `Unsat` — so the fixture cannot pass vacuously.
struct CannedWitnessBackend {
    model: axeyum_solver::Model,
}

impl axeyum_solver::SolverBackend for CannedWitnessBackend {
    fn capabilities(&self) -> axeyum_solver::Capabilities {
        axeyum_solver::Capabilities {
            name: "canned-witness".to_owned(),
            produces_models: true,
            complete: false,
        }
    }

    fn check(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        _config: &SolverConfig,
    ) -> Result<CheckResult, axeyum_solver::SolverError> {
        let assignment = self.model.to_assignment();
        for &assertion in assertions {
            match eval(arena, assertion, &assignment) {
                Ok(Value::Bool(true)) => {}
                // The candidate does not satisfy the REDUCED query: say so
                // rather than handing back a model the replay would reject.
                _ => return Ok(CheckResult::Unsat),
            }
        }
        Ok(CheckResult::Sat(self.model.clone()))
    }
}

/// The ADR-1811 fixture: `y = 0 ∧ x = 5 ∧ x/y = 100 ∧ f(x) = 7`.
///
/// Replaying it needs all three witness kinds — the symbol values for `x`/`y`,
/// the `/0` witness (without it the evaluator falls back to the total `x/0 = 0`
/// convention and `0 = 100` is false), and `f`'s interpretation (without it
/// `eval` raises `UnboundFunction`).
fn both_witness_kinds_fixture() -> (
    TermArena,
    Vec<TermId>,
    CannedWitnessBackend,
    SymbolId,
    FuncId,
) {
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let x = arena.declare("wx", Sort::Real).unwrap();
    let y = arena.declare("wy", Sort::Real).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let zero = arena.real_const(Rational::integer(0));
    let five = arena.real_const(Rational::integer(5));
    let seven = arena.real_const(Rational::integer(7));
    let hundred = arena.real_const(Rational::integer(100));
    let quotient = arena.real_div(xv, yv).unwrap();
    let y_is_0 = arena.eq(yv, zero).unwrap();
    let x_is_5 = arena.eq(xv, five).unwrap();
    let quotient_is_100 = arena.eq(quotient, hundred).unwrap();
    let fx = arena.apply(f, &[xv]).unwrap();
    let fx_is_7 = arena.eq(fx, seven).unwrap();

    let mut model = axeyum_solver::Model::new();
    model.set(x, Value::Real(Rational::integer(5)));
    model.set(y, Value::Real(Rational::integer(0)));
    model.set_function(
        f,
        FuncValue::constant_value(
            vec![Sort::Real],
            Sort::Real,
            Value::Real(Rational::integer(0)),
        )
        .define_value(
            &[Value::Real(Rational::integer(5))],
            Value::Real(Rational::integer(7)),
        ),
    );
    model.set_real_div_zero(Rational::integer(5), Rational::integer(100));

    let originals = vec![y_is_0, x_is_5, quotient_is_100, fx_is_7];
    (arena, originals, CannedWitnessBackend { model }, x, f)
}

/// **The ADR-1811 exit-criterion fixture.** A query carrying a real `/0`
/// witness AND an uninterpreted-function interpretation goes through
/// `check_with_preprocessing`, and the model it hands BACK replays every
/// original assertion. Dropping any one of the three carries breaks this.
#[test]
fn preprocessed_model_with_both_witness_kinds_replays() {
    let (mut arena, originals, mut backend, _x, _f) = both_witness_kinds_fixture();
    let result = check_with_preprocessing(
        &mut backend,
        &mut arena,
        &originals,
        &SolverConfig::default(),
    )
    .expect("the canned candidate satisfies the reduced query, so the replay succeeds");
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    assert_model_satisfies(&arena, &model, &originals);
}

/// Negative control 1 of 3 — the SYMBOL-value carry.
#[test]
fn preprocessed_model_carries_symbol_values() {
    let (mut arena, originals, mut backend, x, _f) = both_witness_kinds_fixture();
    let CheckResult::Sat(model) = check_with_preprocessing(
        &mut backend,
        &mut arena,
        &originals,
        &SolverConfig::default(),
    )
    .unwrap() else {
        panic!("expected sat");
    };
    assert_eq!(
        model.get(x),
        Some(Value::Real(Rational::integer(5))),
        "the returned model must carry the symbol values"
    );
}

/// Negative control 2 of 3 — the UNINTERPRETED-FUNCTION carry. This is the one
/// `preprocess.rs` did not have before ADR-1811.
#[test]
fn preprocessed_model_carries_function_interpretations() {
    let (mut arena, originals, mut backend, _x, f) = both_witness_kinds_fixture();
    let CheckResult::Sat(model) = check_with_preprocessing(
        &mut backend,
        &mut arena,
        &originals,
        &SolverConfig::default(),
    )
    .unwrap() else {
        panic!("expected sat");
    };
    let interp = model
        .function(f)
        .expect("the returned model must carry the interpretation of `f`");
    assert_eq!(
        interp.apply_value(&[Value::Real(Rational::integer(5))]),
        Value::Real(Rational::integer(7))
    );
}

/// Negative control 3 of 3 — the free-division `/0` carry.
#[test]
fn preprocessed_model_carries_the_real_div_zero_witness() {
    let (mut arena, originals, mut backend, _x, _f) = both_witness_kinds_fixture();
    let CheckResult::Sat(model) = check_with_preprocessing(
        &mut backend,
        &mut arena,
        &originals,
        &SolverConfig::default(),
    )
    .unwrap() else {
        panic!("expected sat");
    };
    assert_eq!(
        model.real_div_zero(Rational::integer(5)),
        Some(Rational::integer(100)),
        "the returned model must carry the chosen value of 5/0"
    );
}

/// The replay is a soundness ALARM, not a formality: a backend whose candidate
/// needs a `/0` witness it does not supply must never come back as `sat`.
/// (`5/0` then falls back to the total `x/0 = 0` convention, so `0 = 100` is
/// false.)
#[test]
fn a_candidate_missing_the_div_zero_witness_is_never_sat() {
    let (mut arena, originals, backend, _x, _f) = both_witness_kinds_fixture();
    let mut stripped = axeyum_solver::Model::new();
    for (symbol, value) in backend.model.iter() {
        stripped.set(symbol, value);
    }
    for (func, interp) in backend.model.functions() {
        stripped.set_function(func, interp.clone());
    }
    let mut backend = CannedWitnessBackend { model: stripped };
    let result = check_with_preprocessing(
        &mut backend,
        &mut arena,
        &originals,
        &SolverConfig::default(),
    );
    match result {
        Ok(CheckResult::Sat(model)) => {
            panic!("a candidate with no /0 witness must not come back as sat; got {model:?}")
        }
        Ok(_) | Err(_) => {}
    }
}

/// The FRONT DOOR half of the ADR-1811 exit criterion, part 1: a query whose
/// model needs the `/0` witness decides `sat` through `check_auto`'s
/// preprocessed path (route trace: `nra`, inside `dispatch_reduced`) and the
/// returned model replays.
#[test]
fn front_door_preprocessed_model_carries_the_real_div_zero_witness() {
    let mut arena = TermArena::new();
    let x = arena.declare("dx", Sort::Real).unwrap();
    let y = arena.declare("dy", Sort::Real).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let zero = arena.real_const(Rational::integer(0));
    let five = arena.real_const(Rational::integer(5));
    let hundred = arena.real_const(Rational::integer(100));
    let quotient = arena.real_div(xv, yv).unwrap();
    let y_is_0 = arena.eq(yv, zero).unwrap();
    let x_is_5 = arena.eq(xv, five).unwrap();
    let quotient_is_100 = arena.eq(quotient, hundred).unwrap();
    let originals = [y_is_0, x_is_5, quotient_is_100];
    let config = SolverConfig::default().with_preprocess(true);
    let CheckResult::Sat(model) = check_auto(&mut arena, &originals, &config).unwrap() else {
        panic!("x = 5 ∧ y = 0 ∧ x/y = 100 is sat under SMT-LIB free division");
    };
    assert_eq!(
        model.real_div_zero(Rational::integer(5)),
        Some(Rational::integer(100))
    );
    assert_model_satisfies(&arena, &model, &originals);
}

/// The FRONT DOOR half, part 2: a `QF_UFLIA` query decides `sat` through the
/// preprocessed path and the returned model carries `g`'s interpretation. Drop
/// the function loop from the merged replay and `eval` raises `UnboundFunction`
/// on the original `g(x) = 7`.
#[test]
fn front_door_preprocessed_model_carries_the_function_interpretation() {
    let mut arena = TermArena::new();
    let g = arena.declare_fun("g", &[Sort::Int], Sort::Int).unwrap();
    let x = arena.declare("ux", Sort::Int).unwrap();
    let z = arena.declare("uz", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zv = arena.var(z);
    let one = arena.int_const(1);
    let five = arena.int_const(5);
    let six = arena.int_const(6);
    let seven = arena.int_const(7);
    let x_plus_1 = arena.int_add(xv, one).unwrap();
    let gx = arena.apply(g, &[xv]).unwrap();
    let x_is_5 = arena.eq(xv, five).unwrap();
    // `z = x + 1` is a definition `solve_eqs` eliminates, so the trail is
    // non-empty and the reconstruction is exercised, not bypassed.
    let z_def = arena.eq(zv, x_plus_1).unwrap();
    let gx_is_7 = arena.eq(gx, seven).unwrap();
    let z_is_6 = arena.eq(zv, six).unwrap();
    let originals = [x_is_5, z_def, gx_is_7, z_is_6];
    let config = SolverConfig::default().with_preprocess(true);
    let CheckResult::Sat(model) = check_auto(&mut arena, &originals, &config).unwrap() else {
        panic!("x = 5 ∧ z = x+1 ∧ g(x) = 7 ∧ z = 6 is sat");
    };
    assert!(
        model.function(g).is_some(),
        "the returned model must carry the interpretation of `g`"
    );
    assert_model_satisfies(&arena, &model, &originals);
}
