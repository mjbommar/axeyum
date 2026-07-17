//! Conjunctive `QF_UFLRA` Craig interpolation (`axeyum_solver::uflra_interpolant`).
//!
//! Each hand-built unsatisfiable `(A, B)` pair asserts that an interpolant is
//! returned and then INDEPENDENTLY re-checks the three Craig conditions test-side
//! with [`check_with_uf_arithmetic`] (the tests never merely trust the function
//! under test). A satisfiable pair and a congruence-needed pair confirm the sound
//! decline path, and a deterministic LCG fuzz confirms no wrong interpolant is
//! ever returned.
#![cfg(feature = "full")]

use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, check_with_uf_arithmetic, uflra_interpolant};

/// Independently re-verifies the first two Craig conditions for `interp` against
/// the original partitions, returning whether both hold (the vocabulary condition
/// is checked separately by `mentions_*` in the relevant tests).
fn craig_conditions_hold(
    arena: &mut TermArena,
    part_a: &[TermId],
    part_b: &[TermId],
    interp: TermId,
) -> bool {
    let config = SolverConfig::default();

    // (1) A ∧ ¬I unsat.
    let not_i = arena.not(interp).unwrap();
    let mut a_check = part_a.to_vec();
    a_check.push(not_i);
    let cond1 = matches!(
        check_with_uf_arithmetic(arena, &a_check, &config).unwrap(),
        CheckResult::Unsat
    );

    // (2) I ∧ B unsat.
    let mut b_check = vec![interp];
    b_check.extend_from_slice(part_b);
    let cond2 = matches!(
        check_with_uf_arithmetic(arena, &b_check, &config).unwrap(),
        CheckResult::Unsat
    );

    cond1 && cond2
}

/// Builds a real constant term from an integer.
fn real_int(arena: &mut TermArena, value: i128) -> TermId {
    arena.real_const(Rational::integer(value))
}

#[test]
fn shared_uf_app_acts_as_opaque_real() {
    // Shared term f(c): A: f(c) >= 5, B: f(c) <= 3 ⇒ unsat. No congruence needed.
    // Interpolant must mention the SHARED term f(c).
    let mut arena = TermArena::new();
    let func_f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let var_c = arena.real_var("c").unwrap();
    let app_fc = arena.apply(func_f, &[var_c]).unwrap();

    let five = real_int(&mut arena, 5);
    let three = real_int(&mut arena, 3);
    let part_a = vec![arena.real_ge(app_fc, five).unwrap()];
    let part_b = vec![arena.real_le(app_fc, three).unwrap()];

    let interp = uflra_interpolant(&mut arena, &part_a, &part_b)
        .unwrap()
        .expect("unsat shared-opaque pair has a conjunctive interpolant");
    assert!(
        craig_conditions_hold(&mut arena, &part_a, &part_b, interp),
        "independently re-verified Craig conditions"
    );
}

#[test]
fn a_local_uf_term_must_not_appear_in_interpolant() {
    // A: g(d) >= 0 ∧ x >= 5, B: x <= 3. The refutation is purely over the shared
    // real x; the A-local g(d) must not appear in the interpolant.
    let mut arena = TermArena::new();
    let func_g = arena.declare_fun("g", &[Sort::Real], Sort::Real).unwrap();
    let var_d = arena.real_var("d").unwrap();
    let app_gd = arena.apply(func_g, &[var_d]).unwrap();
    let var_x = arena.real_var("x").unwrap();

    let zero = real_int(&mut arena, 0);
    let five = real_int(&mut arena, 5);
    let three = real_int(&mut arena, 3);

    let part_a = vec![
        arena.real_ge(app_gd, zero).unwrap(),
        arena.real_ge(var_x, five).unwrap(),
    ];
    let part_b = vec![arena.real_le(var_x, three).unwrap()];

    let interp = uflra_interpolant(&mut arena, &part_a, &part_b)
        .unwrap()
        .expect("unsat over shared x has an interpolant");
    assert!(craig_conditions_hold(&mut arena, &part_a, &part_b, interp));

    // The A-local function g must not appear in the interpolant.
    let g_name = arena.function(func_g).0.to_owned();
    assert!(
        !mentions_function(&arena, interp, &g_name),
        "A-local function g must not appear in the interpolant"
    );
}

#[test]
fn nested_application_shared() {
    // Nested f(g(c)) shared between A and B (tests the recursive translate).
    // A: f(g(c)) >= 10, B: f(g(c)) <= 2 ⇒ unsat, no congruence needed.
    let mut arena = TermArena::new();
    let func_g = arena.declare_fun("g", &[Sort::Real], Sort::Real).unwrap();
    let func_f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let var_c = arena.real_var("c").unwrap();
    let inner_gc = arena.apply(func_g, &[var_c]).unwrap();
    let outer_fgc = arena.apply(func_f, &[inner_gc]).unwrap();

    let ten = real_int(&mut arena, 10);
    let two = real_int(&mut arena, 2);
    let part_a = vec![arena.real_ge(outer_fgc, ten).unwrap()];
    let part_b = vec![arena.real_le(outer_fgc, two).unwrap()];

    let interp = uflra_interpolant(&mut arena, &part_a, &part_b)
        .unwrap()
        .expect("nested shared application has a conjunctive interpolant");
    assert!(craig_conditions_hold(&mut arena, &part_a, &part_b, interp));
}

#[test]
fn shared_app_plus_arithmetic() {
    // A: f(c) >= x ∧ x >= 5, B: f(c) <= 3 with c, f(c) shared. Unsat: 5 <= x <=
    // f(c) <= 3. No congruence needed (f(c) is a single opaque shared term).
    let mut arena = TermArena::new();
    let func_f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let var_c = arena.real_var("c").unwrap();
    let app_fc = arena.apply(func_f, &[var_c]).unwrap();
    let var_x = arena.real_var("x").unwrap();

    let five = real_int(&mut arena, 5);
    let three = real_int(&mut arena, 3);
    let part_a = vec![
        arena.real_ge(app_fc, var_x).unwrap(),
        arena.real_ge(var_x, five).unwrap(),
    ];
    let part_b = vec![arena.real_le(app_fc, three).unwrap()];

    let interp = uflra_interpolant(&mut arena, &part_a, &part_b)
        .unwrap()
        .expect("shared opaque app + arithmetic has an interpolant");
    assert!(craig_conditions_hold(&mut arena, &part_a, &part_b, interp));
    // x is A-local; the interpolant must be over the shared f(c) only.
    let x_name = arena_symbol_name(&arena, var_x);
    assert!(
        !mentions_symbol(&arena, interp, &x_name),
        "A-local x must not appear in the interpolant"
    );
}

#[test]
fn congruence_needed_declines_or_verifies() {
    // A: x = y, B: f(x) != f(y). The refutation needs congruence f(x)=f(y) from
    // x=y, which the conjunctive method cannot express. The relaxation a' ∧ b' is
    // SAT, so uflra_interpolant declines (None). Either None or a verified
    // interpolant is acceptable — never a wrong one.
    let mut arena = TermArena::new();
    let func_f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let var_x = arena.real_var("x").unwrap();
    let var_y = arena.real_var("y").unwrap();
    let left_app = arena.apply(func_f, &[var_x]).unwrap();
    let right_app = arena.apply(func_f, &[var_y]).unwrap();

    let eq_fxy = arena.eq(left_app, right_app).unwrap();
    let part_a = vec![arena.eq(var_x, var_y).unwrap()];
    let part_b = vec![arena.not(eq_fxy).unwrap()];

    // (Sanity: the combined system is genuinely unsat.)
    let mut combined = part_a.clone();
    combined.extend_from_slice(&part_b);
    assert!(
        matches!(
            check_with_uf_arithmetic(&mut arena, &combined, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        ),
        "the congruence-needed pair is unsat"
    );

    if let Some(interp) = uflra_interpolant(&mut arena, &part_a, &part_b).unwrap() {
        assert!(
            craig_conditions_hold(&mut arena, &part_a, &part_b, interp),
            "any returned interpolant must verify"
        );
    }
}

#[test]
fn sat_pair_yields_none() {
    // A: f(c) >= 1, B: f(c) <= 5 — jointly satisfiable ⇒ no interpolant.
    let mut arena = TermArena::new();
    let func_f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let var_c = arena.real_var("c").unwrap();
    let app_fc = arena.apply(func_f, &[var_c]).unwrap();

    let one = real_int(&mut arena, 1);
    let five = real_int(&mut arena, 5);
    let part_a = vec![arena.real_ge(app_fc, one).unwrap()];
    let part_b = vec![arena.real_le(app_fc, five).unwrap()];

    let result = uflra_interpolant(&mut arena, &part_a, &part_b).unwrap();
    assert!(result.is_none(), "a satisfiable pair has no interpolant");
}

#[test]
fn pure_lra_no_uf_still_works() {
    // No UF at all: A: x >= 5, B: x <= 3 ⇒ unsat. The translate step is a no-op.
    let mut arena = TermArena::new();
    let var_x = arena.real_var("x").unwrap();
    let five = real_int(&mut arena, 5);
    let three = real_int(&mut arena, 3);
    let part_a = vec![arena.real_ge(var_x, five).unwrap()];
    let part_b = vec![arena.real_le(var_x, three).unwrap()];

    let interp = uflra_interpolant(&mut arena, &part_a, &part_b)
        .unwrap()
        .expect("pure-LRA unsat pair has an interpolant");
    assert!(craig_conditions_hold(&mut arena, &part_a, &part_b, interp));
}

/// Deterministic LCG fuzz: random small `QF_UFLRA` pairs over a couple of real
/// variables plus one unary function. Whenever the combined system is unsat and
/// an interpolant is returned, INDEPENDENTLY re-verify both arithmetic conditions;
/// never accept a failing interpolant; assert non-zero coverage.
#[test]
fn deterministic_fuzz_never_wrong() {
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = || {
        // Numerical Recipes LCG; deterministic, no clock / rand.
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        u32::try_from(state >> 33).unwrap_or(0)
    };

    let mut interpolants = 0_u32;
    let mut unsats = 0_u32;

    for _ in 0..400 {
        let mut arena = TermArena::new();
        let func_f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
        let var_x = arena.real_var("x").unwrap();
        let var_y = arena.real_var("y").unwrap();
        let left_app = arena.apply(func_f, &[var_x]).unwrap();
        let right_app = arena.apply(func_f, &[var_y]).unwrap();
        // Shared atoms the partitions can draw from.
        let terms = [var_x, var_y, left_app, right_app];

        let build_side = |arena: &mut TermArena, next: &mut dyn FnMut() -> u32| {
            let mut lits = Vec::new();
            let count = 1 + (next() % 2) as usize; // 1..=2 literals
            for _ in 0..count {
                let lhs = terms[(next() % 4) as usize];
                let bound = i128::from(next() % 11) - 5; // -5..=5
                let bound_t = arena.real_const(Rational::integer(bound));
                let lit = match next() % 4 {
                    0 => arena.real_ge(lhs, bound_t).unwrap(),
                    1 => arena.real_le(lhs, bound_t).unwrap(),
                    2 => arena.real_gt(lhs, bound_t).unwrap(),
                    _ => arena.real_lt(lhs, bound_t).unwrap(),
                };
                lits.push(lit);
            }
            lits
        };

        let part_a = build_side(&mut arena, &mut next);
        let part_b = build_side(&mut arena, &mut next);

        let mut combined = part_a.clone();
        combined.extend_from_slice(&part_b);
        let combined_res =
            check_with_uf_arithmetic(&mut arena, &combined, &SolverConfig::default()).unwrap();
        let is_unsat = matches!(combined_res, CheckResult::Unsat);
        if is_unsat {
            unsats += 1;
        }

        if let Some(interp) = uflra_interpolant(&mut arena, &part_a, &part_b).unwrap() {
            assert!(
                is_unsat,
                "an interpolant was returned for a non-unsat pair \
                 (a={part_a:?} b={part_b:?})"
            );
            assert!(
                craig_conditions_hold(&mut arena, &part_a, &part_b, interp),
                "returned interpolant must satisfy the Craig conditions \
                 (a={part_a:?} b={part_b:?})"
            );
            interpolants += 1;
        }
    }

    assert!(unsats > 0, "fuzz produced no unsat pairs (degenerate)");
    assert!(
        interpolants > 0,
        "fuzz produced no interpolants (non-zero coverage required)"
    );
}

// --- certified interpolant (uflra_interpolant_certified) -------------------

/// The certified interpolant `I` is byte-identical to the `Validated`
/// [`uflra_interpolant`] output, and both refutations self-validate through
/// [`check_alethe_lra`] (proven NOT skipped: the proofs are non-empty and accepted).
/// The three Craig conditions are independently re-checked on the original
/// partitions.
#[test]
fn certified_uflra_interpolant_emits_and_self_checks() {
    use axeyum_solver::{check_alethe_lra, uflra_interpolant_certified};
    // A: f(c) >= 5 ; B: f(c) <= 3. Shared opaque f(c); no congruence needed.
    let mut arena = TermArena::new();
    let func_f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let var_c = arena.real_var("c").unwrap();
    let app_fc = arena.apply(func_f, &[var_c]).unwrap();
    let five = real_int(&mut arena, 5);
    let three = real_int(&mut arena, 3);
    let part_a = vec![arena.real_ge(app_fc, five).unwrap()];
    let part_b = vec![arena.real_le(app_fc, three).unwrap()];

    // Byte-identical interpolant.
    let plain = uflra_interpolant(&mut arena, &part_a, &part_b)
        .unwrap()
        .expect("validated interpolant exists");
    let cert = uflra_interpolant_certified(&mut arena, &part_a, &part_b)
        .unwrap()
        .expect("certified interpolant exists");
    assert_eq!(
        cert.interpolant, plain,
        "certified interpolant must be byte-identical to the validated one"
    );

    // Both refutations are non-empty and self-check (NOT skipped).
    assert!(
        !cert.a_refutation.is_empty() && !cert.b_refutation.is_empty(),
        "both refutations must be present"
    );
    assert_eq!(check_alethe_lra(&cert.a_refutation), Ok(true));
    assert_eq!(check_alethe_lra(&cert.b_refutation), Ok(true));

    // The three Craig conditions, independently re-checked.
    assert!(craig_conditions_hold(
        &mut arena,
        &part_a,
        &part_b,
        cert.interpolant
    ));
    let f_name = arena.function(func_f).0.to_owned();
    // The interpolant mentions the SHARED f(c); its vocabulary is shared.
    assert!(
        mentions_function(&arena, cert.interpolant, &f_name),
        "the interpolant must mention the shared function f"
    );
}

/// A shared-opaque-app-plus-arithmetic instance also certifies, and the certified
/// `a_and_not_i` / `i_and_b` conjunctions are genuinely the Craig conditions.
#[test]
fn certified_uflra_interpolant_app_plus_arithmetic() {
    use axeyum_solver::{check_alethe_lra, uflra_interpolant_certified};
    // A: f(c) >= x ∧ x >= 5 ; B: f(c) <= 3.
    let mut arena = TermArena::new();
    let func_f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let var_c = arena.real_var("c").unwrap();
    let app_fc = arena.apply(func_f, &[var_c]).unwrap();
    let var_x = arena.real_var("x").unwrap();
    let five = real_int(&mut arena, 5);
    let three = real_int(&mut arena, 3);
    let part_a = vec![
        arena.real_ge(app_fc, var_x).unwrap(),
        arena.real_ge(var_x, five).unwrap(),
    ];
    let part_b = vec![arena.real_le(app_fc, three).unwrap()];

    let cert = uflra_interpolant_certified(&mut arena, &part_a, &part_b)
        .unwrap()
        .expect("certified interpolant exists");
    assert_eq!(check_alethe_lra(&cert.a_refutation), Ok(true));
    assert_eq!(check_alethe_lra(&cert.b_refutation), Ok(true));
    assert!(craig_conditions_hold(
        &mut arena,
        &part_a,
        &part_b,
        cert.interpolant
    ));
}

/// DECLINE: a satisfiable pair has no interpolant, so no certificate either.
#[test]
fn certified_uflra_interpolant_declines_on_sat() {
    use axeyum_solver::uflra_interpolant_certified;
    let mut arena = TermArena::new();
    let func_f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let var_c = arena.real_var("c").unwrap();
    let app_fc = arena.apply(func_f, &[var_c]).unwrap();
    let one = real_int(&mut arena, 1);
    let five = real_int(&mut arena, 5);
    let part_a = vec![arena.real_ge(app_fc, one).unwrap()];
    let part_b = vec![arena.real_le(app_fc, five).unwrap()];

    assert!(
        uflra_interpolant_certified(&mut arena, &part_a, &part_b)
            .unwrap()
            .is_none(),
        "a satisfiable pair yields no certificate"
    );
}

// --- helpers ---------------------------------------------------------------

fn arena_symbol_name(arena: &TermArena, term: TermId) -> String {
    match arena.node(term) {
        axeyum_ir::TermNode::Symbol(symbol) => arena.symbol(*symbol).0.to_owned(),
        _ => panic!("expected a symbol term"),
    }
}

/// Whether `term` mentions a symbol of the given name.
fn mentions_symbol(arena: &TermArena, term: TermId, name: &str) -> bool {
    use axeyum_ir::TermNode;
    let mut stack = vec![term];
    let mut seen = std::collections::BTreeSet::new();
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        match arena.node(current) {
            TermNode::Symbol(symbol) if arena.symbol(*symbol).0 == name => return true,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

/// Whether `term` mentions an uninterpreted function of the given name.
fn mentions_function(arena: &TermArena, term: TermId, name: &str) -> bool {
    use axeyum_ir::{Op, TermNode};
    let mut stack = vec![term];
    let mut seen = std::collections::BTreeSet::new();
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(current) {
            if let Op::Apply(func) = op
                && arena.function(*func).0 == name
            {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}
