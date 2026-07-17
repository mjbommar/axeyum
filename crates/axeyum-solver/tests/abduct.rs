//! Boolean abduction (`axeyum_solver::abduct`, the `get-abduct` slice).
//!
//! Every test that gets back `Some(H)` INDEPENDENTLY re-checks `H`'s three
//! abduction conditions — consistency, sufficiency, and the shared-vocabulary
//! restriction — test-side via [`check_auto`], rather than trusting the function
//! under test. The edge cases (already-entailed ⇒ `⊤`, inconsistent axioms ⇒
//! `None`, no shared atom ⇒ `None`) and a deterministic LCG fuzz confirm the
//! sound decline path: a returned abduct is always genuine, and an over-eager
//! `None` is acceptable.
#![cfg(feature = "full")]

use std::collections::BTreeSet;

use axeyum_ir::{FuncId, Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_solver::{CheckResult, SolverConfig, abduct, check_auto};

/// Independently re-verifies all three abduction conditions for `hypothesis`
/// against the original `axioms` / `conjecture`, returning whether all hold.
fn abduct_conditions_hold(
    arena: &mut TermArena,
    axioms: &[TermId],
    conjecture: TermId,
    hypothesis: TermId,
    config: &SolverConfig,
) -> bool {
    // (1) Consistency: axioms ∧ H sat.
    let mut consistency = axioms.to_vec();
    consistency.push(hypothesis);
    let cond1 = matches!(
        check_auto(arena, &consistency, config).unwrap(),
        CheckResult::Sat(_)
    );

    // (2) Sufficiency: axioms ∧ H ∧ ¬C unsat.
    let not_c = arena.not(conjecture).unwrap();
    let mut sufficiency = axioms.to_vec();
    sufficiency.push(hypothesis);
    sufficiency.push(not_c);
    let cond2 = matches!(
        check_auto(arena, &sufficiency, config).unwrap(),
        CheckResult::Unsat
    );

    // (3) Vocabulary: H ⊆ (axioms-vocab ∩ conjecture-vocab).
    let cond3 = vocabulary_subset(arena, axioms, conjecture, hypothesis);

    cond1 && cond2 && cond3
}

/// Whether the hypothesis only mentions symbols/functions shared by the axioms
/// and the conjecture.
fn vocabulary_subset(
    arena: &TermArena,
    axioms: &[TermId],
    conjecture: TermId,
    hypothesis: TermId,
) -> bool {
    let (a_syms, a_funcs) = vocab_of_slice(arena, axioms);
    let (c_syms, c_funcs) = vocab_of(arena, conjecture);
    let (h_syms, h_funcs) = vocab_of(arena, hypothesis);

    let shared_syms: BTreeSet<SymbolId> = a_syms.intersection(&c_syms).copied().collect();
    let shared_funcs: BTreeSet<FuncId> = a_funcs.intersection(&c_funcs).copied().collect();

    h_syms.is_subset(&shared_syms) && h_funcs.is_subset(&shared_funcs)
}

fn vocab_of_slice(arena: &TermArena, terms: &[TermId]) -> (BTreeSet<SymbolId>, BTreeSet<FuncId>) {
    let mut syms = BTreeSet::new();
    let mut funcs = BTreeSet::new();
    for &t in terms {
        collect(arena, t, &mut syms, &mut funcs);
    }
    (syms, funcs)
}

fn vocab_of(arena: &TermArena, term: TermId) -> (BTreeSet<SymbolId>, BTreeSet<FuncId>) {
    let mut syms = BTreeSet::new();
    let mut funcs = BTreeSet::new();
    collect(arena, term, &mut syms, &mut funcs);
    (syms, funcs)
}

fn collect(
    arena: &TermArena,
    term: TermId,
    syms: &mut BTreeSet<SymbolId>,
    funcs: &mut BTreeSet<FuncId>,
) {
    let mut stack = vec![term];
    let mut seen = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(symbol) => {
                syms.insert(*symbol);
            }
            TermNode::App { op, args } => {
                if let Op::Apply(func) = op {
                    funcs.insert(*func);
                }
                stack.extend(args.iter().copied());
            }
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_) => {}
        }
    }
}

fn real_int(arena: &mut TermArena, value: i128) -> TermId {
    arena.real_const(Rational::integer(value))
}

/// Collects every distinct subterm id of `term` (including `term`) — used to
/// assert that a synthesized abduct is genuinely NOT present in the formulas.
fn collect_subterms(arena: &TermArena, term: TermId, out: &mut BTreeSet<TermId>) {
    if !out.insert(term) {
        return;
    }
    if let TermNode::App { args, .. } = arena.node(term) {
        let children = args.to_vec();
        for child in children {
            collect_subterms(arena, child, out);
        }
    }
}

#[test]
fn lra_non_entailed_finds_verified_abduct() {
    // Reals x, y shared by axioms and conjecture.
    // Axioms: { x <= 0, y <= x + 10 }. Conjecture: y <= 5.
    // Not entailed (y could be 8). An abduct like `y <= 5` (a shared atom of C)
    // or `x = y` works; the search must return a verified one.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = real_int(&mut arena, 0);
    let ten = real_int(&mut arena, 10);
    let five = real_int(&mut arena, 5);

    let x_le_0 = arena.real_le(x, zero).unwrap();
    let x_plus_10 = arena.real_add(x, ten).unwrap();
    let y_le_x10 = arena.real_le(y, x_plus_10).unwrap();
    let axioms = vec![x_le_0, y_le_x10];
    let conjecture = arena.real_le(y, five).unwrap();

    let config = SolverConfig::default();

    // Sanity: not already entailed.
    let not_c = arena.not(conjecture).unwrap();
    let mut entail = axioms.clone();
    entail.push(not_c);
    assert!(
        !matches!(
            check_auto(&mut arena, &entail, &config).unwrap(),
            CheckResult::Unsat
        ),
        "test setup: conjecture must NOT already be entailed"
    );

    let h = abduct(&mut arena, &axioms, conjecture, &config)
        .unwrap()
        .expect("a shared-vocabulary abduct exists for this LRA case");

    assert!(
        abduct_conditions_hold(&mut arena, &axioms, conjecture, h, &config),
        "independently re-verified all three abduction conditions"
    );
}

#[test]
fn euf_already_entailed_returns_top() {
    // Axioms: { a = b }. Conjecture: f(a) = f(b). Congruence already entails it,
    // so the trivial abduct `⊤` is correct.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let a = arena.real_var("a").unwrap();
    let b = arena.real_var("b").unwrap();
    let a_eq_b = arena.eq(a, b).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let conjecture = arena.eq(fa, fb).unwrap();
    let axioms = vec![a_eq_b];

    let config = SolverConfig::default();
    let h = abduct(&mut arena, &axioms, conjecture, &config)
        .unwrap()
        .expect("already-entailed ⇒ trivial ⊤ abduct");

    // It must be exactly `⊤`, and it must verify.
    assert_eq!(arena.node(h), &TermNode::BoolConst(true), "expected ⊤");
    assert!(
        abduct_conditions_hold(&mut arena, &axioms, conjecture, h, &config),
        "⊤ verifies as a sound abduct"
    );
}

#[test]
fn euf_non_entailed_finds_equality_abduct() {
    // Axioms: { f(a) = c, (a = b) ∨ (b = c) }. Conjecture: f(b) = c.
    // Not entailed; the equality atom `a = b` (which appears in the axioms, so it
    // is in the abducible grammar and shares vocabulary with the conjecture
    // through `f(b)`) closes the gap: f(a) = f(b) = c.
    let mut arena = TermArena::new();
    let fun_f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let var_a = arena.real_var("a").unwrap();
    let var_b = arena.real_var("b").unwrap();
    let var_c = arena.real_var("c").unwrap();
    let apply_to_a = arena.apply(fun_f, &[var_a]).unwrap();
    let apply_to_b = arena.apply(fun_f, &[var_b]).unwrap();
    // `a = b` and `b = c` appear as atoms in the axioms (inside a disjunction),
    // so they enter the grammar. a, b, c are shared with the conjecture (a via
    // f(a)+disjunction, b via f(b), c via f(a)=c and f(b)=c).
    let lhs_equals_b = arena.eq(var_a, var_b).unwrap();
    let mid_equals_c = arena.eq(var_b, var_c).unwrap();
    let disjunction = arena.or(lhs_equals_b, mid_equals_c).unwrap();
    let axiom_image_c = arena.eq(apply_to_a, var_c).unwrap();
    let axioms = vec![axiom_image_c, disjunction];
    // Conjecture mentions a (via the inert `a = a`) as well as b, c, f, so the
    // abducible atom `a = b` lies in the shared vocabulary.
    let self_equal_a = arena.eq(var_a, var_a).unwrap();
    let goal_image_c = arena.eq(apply_to_b, var_c).unwrap();
    let conjecture = arena.and(goal_image_c, self_equal_a).unwrap();

    let config = SolverConfig::default();

    let not_c = arena.not(conjecture).unwrap();
    let mut entail = axioms.clone();
    entail.push(not_c);
    assert!(
        !matches!(
            check_auto(&mut arena, &entail, &config).unwrap(),
            CheckResult::Unsat
        ),
        "test setup: conjecture must NOT already be entailed"
    );

    let h = abduct(&mut arena, &axioms, conjecture, &config)
        .unwrap()
        .expect("a shared equality abduct exists for this EUF case");
    assert!(
        abduct_conditions_hold(&mut arena, &axioms, conjecture, h, &config),
        "independently re-verified all three abduction conditions"
    );
}

#[test]
fn lra_synthesized_comparison_abduct() {
    // SYNTHESIZED-ATOM coverage. Axioms: { x <= y, z <= y }. Conjecture:
    // (x <= 5) ∧ (z <= 5) ∧ (y <= y) (the inert `y <= y` makes y shared). No
    // single syntactic atom abduces (x <= 5 alone leaves z unbounded, and vice
    // versa), but the synthesized comparison `y <= 5` of the shared term y to the
    // constant 5 (drawn from the conjecture) closes BOTH gaps at once:
    // x <= y <= 5 and z <= y <= 5. A single literal is always tried before any
    // conjunction, so the synthesized `y <= 5` wins — and it is NOT literally
    // present in either formula.
    let mut arena = TermArena::new();
    let var_x = arena.real_var("x").unwrap();
    let var_y = arena.real_var("y").unwrap();
    let var_z = arena.real_var("z").unwrap();
    let five = real_int(&mut arena, 5);

    let x_le_y = arena.real_le(var_x, var_y).unwrap();
    let z_le_y = arena.real_le(var_z, var_y).unwrap();
    let axioms = vec![x_le_y, z_le_y];

    let x_le_5 = arena.real_le(var_x, five).unwrap();
    let z_le_5 = arena.real_le(var_z, five).unwrap();
    let y_le_y = arena.real_le(var_y, var_y).unwrap();
    let inner = arena.and(x_le_5, z_le_5).unwrap();
    let conjecture = arena.and(inner, y_le_y).unwrap();

    let config = SolverConfig::default();

    // Setup sanity: not already entailed (x could be 0, y = 100).
    let not_c = arena.not(conjecture).unwrap();
    let mut entail = axioms.clone();
    entail.push(not_c);
    assert!(
        !matches!(
            check_auto(&mut arena, &entail, &config).unwrap(),
            CheckResult::Unsat
        ),
        "test setup: conjecture must NOT already be entailed"
    );

    let abduct_h = abduct(&mut arena, &axioms, conjecture, &config)
        .unwrap()
        .expect("a synthesized comparison abduct exists for this LRA case");

    // Independently re-verify all three conditions test-side.
    assert!(
        abduct_conditions_hold(&mut arena, &axioms, conjecture, abduct_h, &config),
        "independently re-verified all three abduction conditions"
    );

    // And confirm the abduct is genuinely a SYNTHESIZED atom: neither it nor its
    // negation occurs syntactically in the axioms or conjecture.
    let present: BTreeSet<TermId> = {
        let mut subterms = BTreeSet::new();
        for &root in axioms.iter().chain(std::iter::once(&conjecture)) {
            collect_subterms(&arena, root, &mut subterms);
        }
        subterms
    };
    let neg_h = arena.not(abduct_h).unwrap();
    assert!(
        !present.contains(&abduct_h) && !present.contains(&neg_h),
        "the abduct must be synthesized, not literally present in the formulas"
    );
}

#[test]
fn euf_synthesized_equality_abduct() {
    // SYNTHESIZED-ATOM coverage (equality). The abduct `a = b` — an equality
    // between two shared constants that does NOT appear in axioms or conjecture —
    // closes the gap by congruence: a = b ⟹ f(a) = f(b) and g(a) = g(b).
    //
    // Axioms: { f(a) = c, g(a) = d, (a = c) ∨ (b = c) }. The disjunction puts b
    // in the axiom vocabulary (so a, b, c, d are shared) and constrains the model
    // for a clean projection. Conjecture: { f(b) = c ∧ g(b) = d ∧ (a = a) } (the
    // inert `a = a` makes a shared so the equality `a = b` is admissible). No
    // single present atom abduces the WHOLE conjecture (`f(b)=c` leaves g(b)=d
    // open and vice versa), and a single literal is always tried before any
    // conjunction — so the SYNTHESIZED equality `a = b`, which closes both at
    // once, is returned.
    let mut arena = TermArena::new();
    let fun_f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let fun_g = arena.declare_fun("g", &[Sort::Real], Sort::Real).unwrap();
    let var_a = arena.real_var("a").unwrap();
    let var_b = arena.real_var("b").unwrap();
    let var_c = arena.real_var("c").unwrap();
    let var_d = arena.real_var("d").unwrap();

    let f_of_a = arena.apply(fun_f, &[var_a]).unwrap();
    let f_of_b = arena.apply(fun_f, &[var_b]).unwrap();
    let g_of_a = arena.apply(fun_g, &[var_a]).unwrap();
    let g_of_b = arena.apply(fun_g, &[var_b]).unwrap();
    let axiom_fa_is_c = arena.eq(f_of_a, var_c).unwrap();
    let axiom_ga_is_d = arena.eq(g_of_a, var_d).unwrap();
    let a_eq_c = arena.eq(var_a, var_c).unwrap();
    let b_eq_c = arena.eq(var_b, var_c).unwrap();
    let disjunction = arena.or(a_eq_c, b_eq_c).unwrap();
    let axioms = vec![axiom_fa_is_c, axiom_ga_is_d, disjunction];

    let goal_fb_is_c = arena.eq(f_of_b, var_c).unwrap();
    let goal_gb_is_d = arena.eq(g_of_b, var_d).unwrap();
    let a_eq_a = arena.eq(var_a, var_a).unwrap();
    let goals = arena.and(goal_fb_is_c, goal_gb_is_d).unwrap();
    let conjecture = arena.and(goals, a_eq_a).unwrap();

    let config = SolverConfig::default();

    let not_c = arena.not(conjecture).unwrap();
    let mut entail = axioms.clone();
    entail.push(not_c);
    assert!(
        !matches!(
            check_auto(&mut arena, &entail, &config).unwrap(),
            CheckResult::Unsat
        ),
        "test setup: conjecture must NOT already be entailed"
    );

    let abduct_h = abduct(&mut arena, &axioms, conjecture, &config)
        .unwrap()
        .expect("a synthesized equality abduct exists for this EUF case");

    assert!(
        abduct_conditions_hold(&mut arena, &axioms, conjecture, abduct_h, &config),
        "independently re-verified all three abduction conditions"
    );

    // The abduct is the synthesized equality `a = b`, which is not present
    // syntactically (only `a = c`, `b = c`, `f(a)=c`, `g(a)=d`, `f(b)=c`,
    // `g(b)=d` are).
    let a_eq_b = arena.eq(var_a, var_b).unwrap();
    assert_eq!(abduct_h, a_eq_b, "expected the synthesized equality a = b");

    let present: BTreeSet<TermId> = {
        let mut subterms = BTreeSet::new();
        for &root in axioms.iter().chain(std::iter::once(&conjecture)) {
            collect_subterms(&arena, root, &mut subterms);
        }
        subterms
    };
    let neg_h = arena.not(abduct_h).unwrap();
    assert!(
        !present.contains(&abduct_h) && !present.contains(&neg_h),
        "the equality abduct must be synthesized, not literally present"
    );
}

#[test]
fn no_abduct_in_grammar_within_budget_declines() {
    // The conjecture is NOT entailed and NO atom in the (now larger) grammar —
    // shared literals plus synthesized equalities/comparisons over the shared
    // vocabulary — can close the gap, so the sound answer is a decline. Here the
    // shared vocabulary is empty (axioms over x, conjecture over y), so no
    // synthesized atom is admissible and `None` is correct. (A decline is always
    // acceptable; a wrong abduct never is.)
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = real_int(&mut arena, 0);
    let three = real_int(&mut arena, 3);
    let x_ge_0 = arena.real_ge(x, zero).unwrap();
    let axioms = vec![x_ge_0];
    let conjecture = arena.real_le(y, three).unwrap();

    let config = SolverConfig::default();
    let result = abduct(&mut arena, &axioms, conjecture, &config).unwrap();
    assert!(
        result.is_none(),
        "no admissible abduct in the larger grammar ⇒ decline, never wrong"
    );
}

#[test]
fn inconsistent_axioms_decline() {
    // Axioms: { x <= 0, x >= 1 } over reals — unsatisfiable. No useful abduct.
    let mut arena = TermArena::new();
    let var_x = arena.real_var("x").unwrap();
    let zero = real_int(&mut arena, 0);
    let one = real_int(&mut arena, 1);
    let x_at_most_zero = arena.real_le(var_x, zero).unwrap();
    let x_at_least_one = arena.real_ge(var_x, one).unwrap();
    let axioms = vec![x_at_most_zero, x_at_least_one];
    let conjecture = arena.real_le(var_x, zero).unwrap();

    let config = SolverConfig::default();
    let result = abduct(&mut arena, &axioms, conjecture, &config).unwrap();
    assert!(result.is_none(), "inconsistent axioms ⇒ None");
}

#[test]
fn no_shared_vocabulary_decline() {
    // Axioms over x only; conjecture over y only — disjoint vocabularies, no
    // shared atom can close the gap, and the conjecture is not entailed.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = real_int(&mut arena, 0);
    let five = real_int(&mut arena, 5);
    let x_le_0 = arena.real_le(x, zero).unwrap();
    let axioms = vec![x_le_0];
    let conjecture = arena.real_le(y, five).unwrap();

    let config = SolverConfig::default();
    let result = abduct(&mut arena, &axioms, conjecture, &config).unwrap();
    assert!(
        result.is_none(),
        "no shared vocabulary ⇒ decline (never a wrong abduct)"
    );
}

#[test]
fn lcg_fuzz_no_unsound_abduct() {
    // Deterministic LCG over a handful of real vars: random small axiom sets and
    // a random conjecture. Whenever `abduct` returns Some(H), independently
    // re-verify all three conditions. Assert non-zero coverage; never unsound.
    let config = SolverConfig::default();
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let next = |s: &mut u64| {
        *s = s
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (*s >> 33) as u32
    };

    let mut some_count = 0usize;
    let mut none_count = 0usize;

    for _ in 0..120 {
        let mut arena = TermArena::new();
        let vars: Vec<TermId> = ["a", "b", "c"]
            .iter()
            .map(|n| arena.real_var(n).unwrap())
            .collect();

        // Build a random atom `vars[i] <relop> k` for small k.
        let rand_atom = |arena: &mut TermArena, s: &mut u64| -> TermId {
            let vi = (next(s) % 3) as usize;
            let k = i128::from(next(s) % 11) - 5;
            let kc = arena.real_const(Rational::integer(k));
            match next(s) % 3 {
                0 => arena.real_le(vars[vi], kc).unwrap(),
                1 => arena.real_ge(vars[vi], kc).unwrap(),
                _ => arena.eq(vars[vi], kc).unwrap(),
            }
        };

        let n_ax = 1 + (next(&mut state) % 3) as usize;
        let axioms: Vec<TermId> = (0..n_ax)
            .map(|_| rand_atom(&mut arena, &mut state))
            .collect();
        let conjecture = rand_atom(&mut arena, &mut state);

        match abduct(&mut arena, &axioms, conjecture, &config).unwrap() {
            Some(h) => {
                some_count += 1;
                assert!(
                    abduct_conditions_hold(&mut arena, &axioms, conjecture, h, &config),
                    "fuzz: returned abduct must independently verify all three conditions"
                );
            }
            None => none_count += 1,
        }
    }

    assert!(
        some_count > 0,
        "fuzz coverage: at least one Some(H) expected (got {some_count} some / {none_count} none)"
    );
}
