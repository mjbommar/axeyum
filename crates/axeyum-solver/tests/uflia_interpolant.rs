//! Conjunctive `QF_UFLIA` Craig interpolation (`axeyum_solver::uflia_interpolant`).
//!
//! Each hand-built unsatisfiable `(A, B)` pair asserts that an interpolant is
//! returned and then INDEPENDENTLY re-checks the three Craig conditions test-side
//! with [`check_with_uf_arithmetic`] (the tests never merely trust the function
//! under test). A satisfiable pair, a congruence-needed pair, and a cuts-needed
//! integer pair confirm the sound decline path, and a deterministic LCG fuzz
//! confirms no wrong interpolant is ever returned.

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, check_with_uf_arithmetic, uflia_interpolant};

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

/// Integer constant term.
fn int_k(arena: &mut TermArena, value: i128) -> TermId {
    arena.int_const(value)
}

#[test]
fn shared_uf_app_acts_as_opaque_int() {
    // Shared term f(c): A: f(c) >= 5, B: f(c) <= 3 ⇒ unsat. No congruence needed.
    // Interpolant must mention the SHARED term f(c).
    let mut arena = TermArena::new();
    let func_f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let var_c = arena.declare("c", Sort::Int).unwrap();
    let var_c = arena.var(var_c);
    let app_fc = arena.apply(func_f, &[var_c]).unwrap();

    let five = int_k(&mut arena, 5);
    let three = int_k(&mut arena, 3);
    let part_a = vec![arena.int_ge(app_fc, five).unwrap()];
    let part_b = vec![arena.int_le(app_fc, three).unwrap()];

    let interp = uflia_interpolant(&mut arena, &part_a, &part_b)
        .unwrap()
        .expect("unsat shared-opaque pair has a conjunctive interpolant");
    assert!(
        craig_conditions_hold(&mut arena, &part_a, &part_b, interp),
        "independently re-verified Craig conditions"
    );
    let f_name = arena.function(func_f).0.to_owned();
    assert!(
        mentions_function(&arena, interp, &f_name),
        "interpolant must mention the shared term f(c)"
    );
}

#[test]
fn a_local_uf_term_must_not_appear_in_interpolant() {
    // A: g(d) >= 0 ∧ x >= 5, B: x <= 3. The refutation is purely over the shared
    // integer x; the A-local g(d) must not appear in the interpolant.
    let mut arena = TermArena::new();
    let func_g = arena.declare_fun("g", &[Sort::Int], Sort::Int).unwrap();
    let var_d = arena.declare("d", Sort::Int).unwrap();
    let var_d = arena.var(var_d);
    let app_gd = arena.apply(func_g, &[var_d]).unwrap();
    let var_x = arena.declare("x", Sort::Int).unwrap();
    let var_x = arena.var(var_x);

    let zero = int_k(&mut arena, 0);
    let five = int_k(&mut arena, 5);
    let three = int_k(&mut arena, 3);

    let part_a = vec![
        arena.int_ge(app_gd, zero).unwrap(),
        arena.int_ge(var_x, five).unwrap(),
    ];
    let part_b = vec![arena.int_le(var_x, three).unwrap()];

    let interp = uflia_interpolant(&mut arena, &part_a, &part_b)
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
    let func_g = arena.declare_fun("g", &[Sort::Int], Sort::Int).unwrap();
    let func_f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let var_c = arena.declare("c", Sort::Int).unwrap();
    let var_c = arena.var(var_c);
    let inner_gc = arena.apply(func_g, &[var_c]).unwrap();
    let outer_fgc = arena.apply(func_f, &[inner_gc]).unwrap();

    let ten = int_k(&mut arena, 10);
    let two = int_k(&mut arena, 2);
    let part_a = vec![arena.int_ge(outer_fgc, ten).unwrap()];
    let part_b = vec![arena.int_le(outer_fgc, two).unwrap()];

    let interp = uflia_interpolant(&mut arena, &part_a, &part_b)
        .unwrap()
        .expect("nested shared application has a conjunctive interpolant");
    assert!(craig_conditions_hold(&mut arena, &part_a, &part_b, interp));
}

#[test]
fn shared_app_plus_arithmetic() {
    // A: f(c) >= x ∧ x >= 5, B: f(c) <= 3 with c, f(c) shared. Unsat: 5 <= x <=
    // f(c) <= 3. No congruence needed (f(c) is a single opaque shared term).
    let mut arena = TermArena::new();
    let func_f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let var_c = arena.declare("c", Sort::Int).unwrap();
    let var_c = arena.var(var_c);
    let app_fc = arena.apply(func_f, &[var_c]).unwrap();
    let var_x = arena.declare("x", Sort::Int).unwrap();
    let var_x = arena.var(var_x);

    let five = int_k(&mut arena, 5);
    let three = int_k(&mut arena, 3);
    let part_a = vec![
        arena.int_ge(app_fc, var_x).unwrap(),
        arena.int_ge(var_x, five).unwrap(),
    ];
    let part_b = vec![arena.int_le(app_fc, three).unwrap()];

    let interp = uflia_interpolant(&mut arena, &part_a, &part_b)
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
    // SAT, so uflia_interpolant declines (None). Either None or a verified
    // interpolant is acceptable — never a wrong one.
    let mut arena = TermArena::new();
    let func_f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let var_x = arena.declare("x", Sort::Int).unwrap();
    let var_x = arena.var(var_x);
    let var_y = arena.declare("y", Sort::Int).unwrap();
    let var_y = arena.var(var_y);
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

    if let Some(interp) = uflia_interpolant(&mut arena, &part_a, &part_b).unwrap() {
        assert!(
            craig_conditions_hold(&mut arena, &part_a, &part_b, interp),
            "any returned interpolant must verify"
        );
    }
}

#[test]
fn cuts_needed_integer_declines_or_verifies() {
    // A: 2*f(c) = 1 is UNSAT over ℤ (f(c) opaque integer with no half-integer),
    // but its rational relaxation 2*y = 1 is SAT over ℚ (y = 1/2). The rational
    // relaxation underlying the interpolation route is NOT Farkas-refutable, so
    // the function must DECLINE (Ok(None)) — never a wrong interpolant. B just
    // constrains the shared f(c).
    let mut arena = TermArena::new();
    let func_f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let var_c = arena.declare("c", Sort::Int).unwrap();
    let var_c = arena.var(var_c);
    let app_fc = arena.apply(func_f, &[var_c]).unwrap();

    let two = int_k(&mut arena, 2);
    let one = int_k(&mut arena, 1);
    let zero = int_k(&mut arena, 0);
    let two_fc = arena.int_mul(two, app_fc).unwrap();
    let part_a = vec![arena.eq(two_fc, one).unwrap()];
    let part_b = vec![arena.int_ge(app_fc, zero).unwrap()];

    // A alone is integer-UNSAT (2*f(c) = 1 has no integer solution for f(c)).
    assert!(
        matches!(
            check_with_uf_arithmetic(&mut arena, &part_a, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        ),
        "2*f(c) = 1 is integer-UNSAT"
    );

    // The rational relaxation is SAT, so the rational-relaxation method declines.
    let result = uflia_interpolant(&mut arena, &part_a, &part_b).unwrap();
    if let Some(interp) = result {
        // If something is ever returned it MUST verify; the expected outcome is
        // None, but a sound interpolant is acceptable.
        assert!(
            craig_conditions_hold(&mut arena, &part_a, &part_b, interp),
            "any returned cuts-needed interpolant must verify"
        );
    }
}

#[test]
fn sat_pair_yields_none() {
    // A: f(c) >= 1, B: f(c) <= 5 — jointly satisfiable ⇒ no interpolant.
    let mut arena = TermArena::new();
    let func_f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let var_c = arena.declare("c", Sort::Int).unwrap();
    let var_c = arena.var(var_c);
    let app_fc = arena.apply(func_f, &[var_c]).unwrap();

    let one = int_k(&mut arena, 1);
    let five = int_k(&mut arena, 5);
    let part_a = vec![arena.int_ge(app_fc, one).unwrap()];
    let part_b = vec![arena.int_le(app_fc, five).unwrap()];

    let result = uflia_interpolant(&mut arena, &part_a, &part_b).unwrap();
    assert!(result.is_none(), "a satisfiable pair has no interpolant");
}

#[test]
fn pure_lia_no_uf_still_works() {
    // No UF at all: A: x >= 5, B: x <= 3 ⇒ unsat. The translate step is a no-op.
    let mut arena = TermArena::new();
    let var_x = arena.declare("x", Sort::Int).unwrap();
    let var_x = arena.var(var_x);
    let five = int_k(&mut arena, 5);
    let three = int_k(&mut arena, 3);
    let part_a = vec![arena.int_ge(var_x, five).unwrap()];
    let part_b = vec![arena.int_le(var_x, three).unwrap()];

    let interp = uflia_interpolant(&mut arena, &part_a, &part_b)
        .unwrap()
        .expect("pure-LIA unsat pair has an interpolant");
    assert!(craig_conditions_hold(&mut arena, &part_a, &part_b, interp));
}

/// Deterministic LCG fuzz: random small `QF_UFLIA` pairs over a couple of integer
/// terms plus one unary function. Whenever the combined system is unsat and an
/// interpolant is returned, INDEPENDENTLY re-verify both arithmetic conditions;
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
        let func_f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let var_c = arena.declare("c0", Sort::Int).unwrap();
        let var_c = arena.var(var_c);
        let app_fc = arena.apply(func_f, &[var_c]).unwrap();
        // A small shared pool {c0, f(c0)} so opposing integer bounds on the same
        // term contradict often — the fragment that yields interpolants.
        let terms = [var_c, app_fc];

        let build_side = |arena: &mut TermArena, next: &mut dyn FnMut() -> u32| {
            let mut lits = Vec::new();
            let count = 1 + (next() % 2) as usize; // 1..=2 literals
            for _ in 0..count {
                let lhs = terms[(next() % 2) as usize];
                let bound = i128::from(next() % 11) - 5; // -5..=5
                let bound_t = arena.int_const(bound);
                let lit = match next() % 4 {
                    0 => arena.int_ge(lhs, bound_t).unwrap(),
                    1 => arena.int_le(lhs, bound_t).unwrap(),
                    2 => arena.int_gt(lhs, bound_t).unwrap(),
                    _ => arena.int_lt(lhs, bound_t).unwrap(),
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

        if let Some(interp) = uflia_interpolant(&mut arena, &part_a, &part_b).unwrap() {
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
