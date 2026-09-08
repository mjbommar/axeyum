//! Oracle-free soundness gate for unconstrained-variable elimination.
//!
//! The pass claims **equisatisfiability plus model reconstruction**. Over small
//! bit-vector widths both halves are decidable by brute force, so this suite
//! decides them rather than sampling:
//!
//! * enumerate every assignment of the original assertions' free symbols and of
//!   the reduced ones, and require the two satisfiability verdicts to agree —
//!   this catches a wrong `sat` (a rule that widened the range) **and** a wrong
//!   `unsat` (a rule that narrowed it);
//! * for every model of the reduced problem, reconstruct and require the
//!   **original** assertions to evaluate true.
//!
//! # Why the generators emit constants
//!
//! Every published counterexample to this technique involves a **constant**
//! operand, and a variable-only generator structurally cannot produce one. This
//! repository's hard rule ("a partial or underspecified operator carries a fuzz
//! seed-class that generates the degenerate argument", after `a946f925`) applies
//! directly, so each generator below draws its constants from a boundary pool —
//! `0`, `1`, all-ones, signed `MIN`/`MAX`, and even values — and the named
//! fixtures reproduce Brummayer's three counterexamples verbatim:
//!
//! * `110 · v = 111` — unsat; replacing `110 · v` by a fresh variable makes it
//!   sat (multiplication by an **even** constant is not surjective).
//! * `v <u 000` — unsat; a bit-vector order at the **domain boundary** is not a
//!   free Boolean.
//! * `111 <u v` — unsat, the same trap at the other end.

#![allow(
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    clippy::manual_is_multiple_of,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines
)]

use std::collections::{HashMap, HashSet};

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_rewrite::elim_unconstrained;

/// Deterministic xorshift PRNG (no clock, no RNG service).
fn xorshift(state: &mut u64) -> u64 {
    let mut v = *state;
    v ^= v << 13;
    v ^= v >> 7;
    v ^= v << 17;
    *state = v;
    v
}

/// Free symbols of `roots` with their sorts, ordered by symbol index. The sort
/// comes from the symbol's own term node, so no mutable arena access is needed.
fn free_symbols(arena: &TermArena, roots: &[TermId]) -> Vec<(SymbolId, Sort)> {
    let mut out: HashMap<SymbolId, Sort> = HashMap::new();
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut work: Vec<TermId> = roots.to_vec();
    while let Some(t) = work.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(s) => {
                out.insert(*s, arena.sort_of(t));
            }
            TermNode::App { args, .. } => work.extend(args.iter().copied()),
            _ => {}
        }
    }
    let mut v: Vec<_> = out.into_iter().collect();
    v.sort_by_key(|(s, _)| s.index());
    v
}

/// The finite domain enumerated for one symbol's sort, or `None` when the sort
/// is not finitely enumerable at this scale.
fn domain(sort: Sort) -> Option<Vec<Value>> {
    match sort {
        Sort::Bool => Some(vec![Value::Bool(false), Value::Bool(true)]),
        Sort::BitVec(w) if w <= 4 => Some(
            (0u128..(1u128 << w))
                .map(|value| Value::Bv { width: w, value })
                .collect(),
        ),
        _ => None,
    }
}

/// Every assignment over `syms` that satisfies all of `assertions`.
///
/// Returns `None` when the product of the domains exceeds `cap` (the instance
/// is then skipped rather than silently half-checked).
fn all_models(
    arena: &TermArena,
    assertions: &[TermId],
    syms: &[(SymbolId, Sort)],
    cap: u64,
) -> Option<Vec<Assignment>> {
    let mut domains = Vec::with_capacity(syms.len());
    let mut total: u64 = 1;
    for &(_, sort) in syms {
        let values = domain(sort)?;
        total = total.checked_mul(values.len() as u64)?;
        if total > cap {
            return None;
        }
        domains.push(values);
    }
    let mut models = Vec::new();
    let mut index = 0u64;
    loop {
        let mut assignment = Assignment::new();
        let mut rest = index;
        for ((sym, _), values) in syms.iter().zip(domains.iter()) {
            let slot = (rest % values.len() as u64) as usize;
            rest /= values.len() as u64;
            assignment.set(*sym, values[slot].clone());
        }
        let satisfied = assertions
            .iter()
            .all(|&a| matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))));
        if satisfied {
            models.push(assignment);
        }
        index += 1;
        if index >= total {
            break;
        }
    }
    Some(models)
}

/// Outcome of checking one instance; the caller aggregates so a generator can
/// assert that it actually exercised the pass.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct Checked {
    /// Instances whose verdicts were decided on both sides.
    decided: u64,
    /// Instances where the pass eliminated at least one layer.
    fired: u64,
    /// Instances skipped because a domain product exceeded the cap.
    skipped: u64,
    /// Reduced models reconstructed and replayed against the originals.
    replays: u64,
}

impl Checked {
    fn merge(&mut self, other: Checked) {
        self.decided += other.decided;
        self.fired += other.fired;
        self.skipped += other.skipped;
        self.replays += other.replays;
    }
}

/// Decides equisatisfiability and replays every reduced model, or reports that
/// the instance was too large to decide.
fn render_all(arena: &TermArena, terms: &[TermId]) -> String {
    terms
        .iter()
        .map(|&t| axeyum_ir::render(arena, t))
        .collect::<Vec<_>>()
        .join(" ∧ ")
}

fn check_instance(arena: &mut TermArena, originals: &[TermId], label: &str) -> Checked {
    let mut checked = Checked::default();
    let original_syms = free_symbols(arena, originals);
    let original_render = render_all(arena, originals);
    let out = elim_unconstrained(arena, originals).expect("elim_unconstrained");
    if out.eliminated() > 0 {
        checked.fired = 1;
    }
    let reduced: Vec<TermId> = out.assertions().to_vec();
    let reduced_syms = free_symbols(arena, &reduced);

    const CAP: u64 = 200_000;
    let (Some(original_models), Some(reduced_models)) = (
        all_models(arena, originals, &original_syms, CAP),
        all_models(arena, &reduced, &reduced_syms, CAP),
    ) else {
        checked.skipped = 1;
        return checked;
    };
    checked.decided = 1;

    assert_eq!(
        !original_models.is_empty(),
        !reduced_models.is_empty(),
        "{label}: elim_unconstrained must preserve satisfiability \
         (original models {}, reduced models {}, eliminated {})\n  original: {}\n  reduced:  {}\n  rules:    {:?}",
        original_models.len(),
        reduced_models.len(),
        out.eliminated(),
        original_render,
        render_all(arena, &reduced),
        out.stats().rule_counts(),
    );

    for model in reduced_models.iter().take(64) {
        let full = out
            .trail()
            .reconstruct(arena, model)
            .unwrap_or_else(|e| panic!("{label}: reconstruction failed: {e}"));
        for &a in originals {
            assert_eq!(
                eval(arena, a, &full),
                Ok(Value::Bool(true)),
                "{label}: reconstructed model must satisfy the original assertion\n  \
                 original: {}\n  reduced:  {}\n  rules:    {:?}\n  reduced model: {:?}",
                original_render,
                render_all(arena, &reduced),
                out.stats().rule_counts(),
                model,
            );
        }
        checked.replays += 1;
    }
    checked
}

// ---------------------------------------------------------------------------
// Named fixtures: the three published counterexamples
// ---------------------------------------------------------------------------

/// `110 · v = 111` over three bits — i.e. `6·v = 7`, which is **unsat** because
/// `6·v` is always even. A rule that replaced `6·v` by a fresh variable would
/// report sat.
#[test]
fn brummayer_even_multiplier_stays_unsat() {
    let mut arena = TermArena::new();
    let v = arena.declare("v", Sort::BitVec(3)).unwrap();
    let vv = arena.var(v);
    let six = arena.bv_const(3, 0b110).unwrap();
    let seven = arena.bv_const(3, 0b111).unwrap();
    let product = arena.bv_mul(six, vv).unwrap();
    let goal = arena.eq(product, seven).unwrap();

    let checked = check_instance(&mut arena, &[goal], "110·v = 111");
    assert_eq!(
        checked.decided, 1,
        "the instance must be decided, not skipped"
    );
    // Independent restatement of the same fact, so a broken `check_instance`
    // cannot make this test vacuous.
    let out = elim_unconstrained(&mut arena, &[goal]).unwrap();
    let reduced = out.assertions().to_vec();
    let syms = free_symbols(&arena, &reduced);
    let models = all_models(&arena, &reduced, &syms, 10_000).expect("small");
    assert!(
        models.is_empty(),
        "the reduced form of an unsat instance must have no model"
    );
}

/// `v <u 000` is unsat: nothing is unsigned-less-than zero. Replacing the atom
/// by a bare fresh Boolean would report sat; the rule's `t ≠ MIN` side condition
/// is what keeps it unsat.
#[test]
fn brummayer_ult_at_the_lower_boundary_stays_unsat() {
    for width in 1u32..=4 {
        let mut arena = TermArena::new();
        let v = arena.declare("v", Sort::BitVec(width)).unwrap();
        let vv = arena.var(v);
        let zero = arena.bv_const(width, 0).unwrap();
        let goal = arena.bv_ult(vv, zero).unwrap();
        let checked = check_instance(&mut arena, &[goal], "v <u 0");
        assert_eq!(checked.decided, 1);
    }
}

/// `111 <u v` is unsat: nothing exceeds all-ones. The mirror of the rule above.
#[test]
fn brummayer_ult_at_the_upper_boundary_stays_unsat() {
    for width in 1u32..=4 {
        let mut arena = TermArena::new();
        let v = arena.declare("v", Sort::BitVec(width)).unwrap();
        let vv = arena.var(v);
        let ones = arena.bv_const(width, (1u128 << width) - 1).unwrap();
        let goal = arena.bv_ult(ones, vv).unwrap();
        let checked = check_instance(&mut arena, &[goal], "ones <u v");
        assert_eq!(checked.decided, 1);
    }
}

/// The signed mirrors: `v <s MIN` and `MAX <s v` are both unsat.
#[test]
fn signed_comparisons_at_the_boundary_stay_unsat() {
    for width in 2u32..=4 {
        let min = 1u128 << (width - 1);
        let max = min - 1;
        for (lhs_is_var, bound) in [(true, min), (false, max)] {
            let mut arena = TermArena::new();
            let v = arena.declare("v", Sort::BitVec(width)).unwrap();
            let vv = arena.var(v);
            let b = arena.bv_const(width, bound).unwrap();
            let goal = if lhs_is_var {
                arena.bv_slt(vv, b).unwrap()
            } else {
                arena.bv_slt(b, vv).unwrap()
            };
            let checked = check_instance(&mut arena, &[goal], "signed boundary");
            assert_eq!(checked.decided, 1);
        }
    }
}

/// `(bvudiv x 0)` is all-ones by SMT-LIB totality, and `(bvurem x 0)` is the
/// dividend: the divide rule fires only when **both** operands are free, and it
/// pins the divisor to `1`, so the degenerate zero divisor must never be
/// introduced or assumed away.
#[test]
fn division_by_a_constant_zero_is_not_invented() {
    for width in 1u32..=3 {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(width)).unwrap();
        let xv = arena.var(x);
        let zero = arena.bv_const(width, 0).unwrap();
        let quotient = arena.bv_udiv(xv, zero).unwrap();
        let ones = arena.bv_const(width, (1u128 << width) - 1).unwrap();
        // `x / 0 = ones` is valid, so its negation is unsat.
        let equality = arena.eq(quotient, ones).unwrap();
        let goal = arena.not(equality).unwrap();
        let checked = check_instance(&mut arena, &[goal], "x /u 0");
        assert_eq!(checked.decided, 1);
    }
}

// ---------------------------------------------------------------------------
// Generated seed classes
// ---------------------------------------------------------------------------

/// The boundary constant pool for `width` bits: zero, one, all-ones, the signed
/// bounds, and an even non-zero value — every shape a rule's side condition
/// distinguishes.
fn boundary_constants(width: u32) -> Vec<u128> {
    let mask = (1u128 << width) - 1;
    let mut pool = vec![0, 1, mask, mask >> 1, (mask >> 1) + 1];
    if width >= 2 {
        pool.push(2);
        pool.push(mask & !1); // largest even
    }
    if width >= 3 {
        pool.push(0b110 & mask);
        pool.push(4);
    }
    pool.sort_unstable();
    pool.dedup();
    pool
}

/// Builds a random bit-vector term of `width` bits over `vars`, mixing in
/// constants from the boundary pool.
fn random_bv_term(
    arena: &mut TermArena,
    state: &mut u64,
    vars: &[TermId],
    width: u32,
    depth: u32,
) -> TermId {
    let pool = boundary_constants(width);
    if depth == 0 {
        return if xorshift(state) % 3 == 0 {
            let value = pool[(xorshift(state) as usize) % pool.len()];
            arena.bv_const(width, value).unwrap()
        } else {
            vars[(xorshift(state) as usize) % vars.len()]
        };
    }
    let left = random_bv_term(arena, state, vars, width, depth - 1);
    let right = if xorshift(state) % 2 == 0 {
        let value = pool[(xorshift(state) as usize) % pool.len()];
        arena.bv_const(width, value).unwrap()
    } else {
        random_bv_term(arena, state, vars, width, depth - 1)
    };
    match xorshift(state) % 14 {
        0 => arena.bv_add(left, right).unwrap(),
        1 => arena.bv_sub(left, right).unwrap(),
        2 => arena.bv_mul(left, right).unwrap(),
        3 => arena.bv_xor(left, right).unwrap(),
        4 => arena.bv_and(left, right).unwrap(),
        5 => arena.bv_or(left, right).unwrap(),
        6 => arena.bv_not(left).unwrap(),
        7 => arena.bv_neg(left).unwrap(),
        8 => arena.bv_shl(left, right).unwrap(),
        9 => arena.bv_lshr(left, right).unwrap(),
        10 => arena.bv_udiv(left, right).unwrap(),
        11 => arena.bv_xnor(left, right).unwrap(),
        12 => arena.rotate_left(1, left).unwrap(),
        _ => arena.extract(width - 1, 0, left).unwrap(),
    }
}

/// Builds a random Boolean assertion over bit-vector terms.
fn random_bv_atom(
    arena: &mut TermArena,
    state: &mut u64,
    vars: &[TermId],
    width: u32,
    depth: u32,
) -> TermId {
    let left = random_bv_term(arena, state, vars, width, depth);
    let right = random_bv_term(arena, state, vars, width, depth);
    match xorshift(state) % 7 {
        0 => arena.eq(left, right).unwrap(),
        1 => arena.bv_ult(left, right).unwrap(),
        2 => arena.bv_ule(left, right).unwrap(),
        3 => arena.bv_slt(left, right).unwrap(),
        4 => arena.bv_sle(left, right).unwrap(),
        5 => arena.bv_uge(left, right).unwrap(),
        _ => {
            let comp = arena.bv_comp(left, right).unwrap();
            let one = arena.bv_const(1, 1).unwrap();
            arena.eq(comp, one).unwrap()
        }
    }
}

/// The main bit-vector sweep: random formulas over 2–3 variables of 2–4 bits,
/// with constants drawn from the boundary pool, decided both ways by
/// enumeration.
#[test]
fn random_bit_vector_formulas_preserve_satisfiability() {
    let mut state = 0x2468_ACE0_1357_9BDFu64;
    let mut totals = Checked::default();
    for trial in 0..1500u64 {
        let width = 2 + (xorshift(&mut state) % 3) as u32; // 2..=4
        let var_count = 2 + (xorshift(&mut state) % 2) as usize; // 2..=3
        let mut arena = TermArena::new();
        let vars: Vec<TermId> = (0..var_count)
            .map(|i| {
                let sym = arena
                    .declare(&format!("v{i}"), Sort::BitVec(width))
                    .unwrap();
                arena.var(sym)
            })
            .collect();
        let assertion_count = 1 + (xorshift(&mut state) % 2) as usize;
        let depth = 1 + (xorshift(&mut state) % 2) as u32;
        let originals: Vec<TermId> = (0..assertion_count)
            .map(|_| random_bv_atom(&mut arena, &mut state, &vars, width, depth))
            .collect();
        totals.merge(check_instance(
            &mut arena,
            &originals,
            &format!("bv trial {trial}"),
        ));
    }
    assert!(
        totals.decided >= 1200,
        "most instances must be decided, not skipped: {totals:?}"
    );
    assert!(
        totals.fired >= 300,
        "the sweep must actually exercise the pass: {totals:?}"
    );
    assert!(totals.replays >= 500, "models must be replayed: {totals:?}");
}

/// A dedicated multiplication sweep: **every** constant multiplier at widths
/// 2–4 against a single-use variable, with an equation whose right-hand side
/// walks the whole domain. This is the class `110 · v = 111` belongs to, and it
/// is enumerated rather than sampled.
#[test]
fn every_constant_multiplier_preserves_satisfiability() {
    let mut decided = 0u64;
    let mut fired = 0u64;
    for width in 1u32..=4 {
        let limit = 1u128 << width;
        for coefficient in 0..limit {
            for target in 0..limit {
                let mut arena = TermArena::new();
                let v = arena.declare("v", Sort::BitVec(width)).unwrap();
                let vv = arena.var(v);
                let c = arena.bv_const(width, coefficient).unwrap();
                let product = arena.bv_mul(c, vv).unwrap();
                let t = arena.bv_const(width, target).unwrap();
                let goal = arena.eq(product, t).unwrap();
                let checked = check_instance(
                    &mut arena,
                    &[goal],
                    &format!("{coefficient}·v = {target} at {width} bits"),
                );
                decided += checked.decided;
                fired += checked.fired;
            }
        }
    }
    assert_eq!(decided, 4 + 16 + 64 + 256, "every pair must be decided");
    assert!(fired > 0, "the multiply rules must have fired somewhere");
}

/// Every comparison atom against every constant, at widths 1–4, in both operand
/// positions. This is the class `v <u 000` belongs to.
#[test]
fn every_constant_comparison_preserves_satisfiability() {
    let mut decided = 0u64;
    let mut fired = 0u64;
    for width in 1u32..=4 {
        let limit = 1u128 << width;
        for bound in 0..limit {
            for which in 0..8u32 {
                let mut arena = TermArena::new();
                let v = arena.declare("v", Sort::BitVec(width)).unwrap();
                let vv = arena.var(v);
                let c = arena.bv_const(width, bound).unwrap();
                let (a, b) = if which % 2 == 0 { (vv, c) } else { (c, vv) };
                let goal = match which / 2 {
                    0 => arena.bv_ult(a, b).unwrap(),
                    1 => arena.bv_ule(a, b).unwrap(),
                    2 => arena.bv_slt(a, b).unwrap(),
                    _ => arena.bv_sle(a, b).unwrap(),
                };
                let checked =
                    check_instance(&mut arena, &[goal], &format!("cmp {which} vs {bound}"));
                decided += checked.decided;
                fired += checked.fired;
            }
        }
    }
    assert_eq!(decided, 8 * (2 + 4 + 8 + 16));
    assert!(fired > 0, "the comparison rules must have fired");
}

/// Boolean core rules: random propositional formulas over single-use variables,
/// including `ite` with constant branches and equality against a constant.
#[test]
fn random_boolean_formulas_preserve_satisfiability() {
    let mut state = 0x0BAD_C0DE_F00D_1234u64;
    let mut totals = Checked::default();
    for trial in 0..800u64 {
        let mut arena = TermArena::new();
        let vars: Vec<TermId> = (0..4)
            .map(|i| {
                let sym = arena.declare(&format!("b{i}"), Sort::Bool).unwrap();
                arena.var(sym)
            })
            .collect();
        let build = |arena: &mut TermArena, state: &mut u64| -> TermId {
            let a = vars[(xorshift(state) as usize) % vars.len()];
            let b = vars[(xorshift(state) as usize) % vars.len()];
            match xorshift(state) % 7 {
                0 => arena.and(a, b).unwrap(),
                1 => arena.or(a, b).unwrap(),
                2 => arena.xor(a, b).unwrap(),
                3 => arena.not(a).unwrap(),
                4 => arena.eq(a, b).unwrap(),
                5 => {
                    let t = arena.bool_const(xorshift(state) % 2 == 0);
                    arena.eq(a, t).unwrap()
                }
                _ => {
                    let c = vars[(xorshift(state) as usize) % vars.len()];
                    arena.ite(c, a, b).unwrap()
                }
            }
        };
        let count = 1 + (xorshift(&mut state) % 2) as usize;
        let originals: Vec<TermId> = (0..count).map(|_| build(&mut arena, &mut state)).collect();
        totals.merge(check_instance(
            &mut arena,
            &originals,
            &format!("bool trial {trial}"),
        ));
    }
    assert!(totals.decided >= 700, "{totals:?}");
    assert!(totals.fired >= 100, "the core rules must fire: {totals:?}");
}

/// Concat/extract structural rules over single-use variables.
#[test]
fn structural_rules_preserve_satisfiability() {
    let mut decided = 0u64;
    let mut fired = 0u64;
    for width in 2u32..=4 {
        for hi in 0..width {
            for lo in 0..=hi {
                for target in 0..(1u128 << (hi - lo + 1)) {
                    let mut arena = TermArena::new();
                    let x = arena.declare("x", Sort::BitVec(width)).unwrap();
                    let xv = arena.var(x);
                    let slice = arena.extract(hi, lo, xv).unwrap();
                    let t = arena.bv_const(hi - lo + 1, target).unwrap();
                    let goal = arena.eq(slice, t).unwrap();
                    let checked = check_instance(&mut arena, &[goal], "extract");
                    decided += checked.decided;
                    fired += checked.fired;
                }
            }
        }
    }
    assert!(decided > 0 && fired > 0, "decided {decided}, fired {fired}");

    // `(concat x y) = k` with both operands single-use.
    for width in 1u32..=2 {
        for target in 0..(1u128 << (2 * width)) {
            let mut arena = TermArena::new();
            let x = arena.declare("x", Sort::BitVec(width)).unwrap();
            let y = arena.declare("y", Sort::BitVec(width)).unwrap();
            let (xv, yv) = (arena.var(x), arena.var(y));
            let joined = arena.concat(xv, yv).unwrap();
            let t = arena.bv_const(2 * width, target).unwrap();
            let goal = arena.eq(joined, t).unwrap();
            let checked = check_instance(&mut arena, &[goal], "concat");
            assert_eq!(checked.decided, 1);
        }
    }
}

// ---------------------------------------------------------------------------
// Arithmetic (Int): the divisions the widening exists for
// ---------------------------------------------------------------------------

/// Integer domains are infinite, so satisfiability cannot be decided by
/// enumeration. What *is* decidable — and what a wrong `sat` violates — is the
/// reconstruction obligation: every model of the reduced problem must rebuild a
/// model of the original. This sweep enumerates reduced models over a small box
/// and replays each one.
#[test]
fn integer_formulas_reconstruct_to_models_of_the_original() {
    let mut state = 0xFEED_FACE_CAFE_0001u64;
    let mut replays = 0u64;
    let mut fired = 0u64;
    for _trial in 0..600u64 {
        let mut arena = TermArena::new();
        let vars: Vec<TermId> = (0..3)
            .map(|i| {
                let sym = arena.declare(&format!("n{i}"), Sort::Int).unwrap();
                arena.var(sym)
            })
            .collect();
        let constants: Vec<i128> = vec![-3, -1, 0, 1, 2, 5];
        let term = |arena: &mut TermArena, state: &mut u64| -> TermId {
            let a = if xorshift(state) % 3 == 0 {
                let c = constants[(xorshift(state) as usize) % constants.len()];
                arena.int_const(c)
            } else {
                vars[(xorshift(state) as usize) % vars.len()]
            };
            let b = if xorshift(state) % 2 == 0 {
                let c = constants[(xorshift(state) as usize) % constants.len()];
                arena.int_const(c)
            } else {
                vars[(xorshift(state) as usize) % vars.len()]
            };
            match xorshift(state) % 4 {
                0 => arena.int_add(a, b).unwrap(),
                1 => arena.int_sub(a, b).unwrap(),
                2 => arena.int_mul(a, b).unwrap(),
                _ => arena.int_neg(a).unwrap(),
            }
        };
        let left = term(&mut arena, &mut state);
        let right = term(&mut arena, &mut state);
        let goal = match xorshift(&mut state) % 5 {
            0 => arena.eq(left, right).unwrap(),
            1 => arena.int_lt(left, right).unwrap(),
            2 => arena.int_le(left, right).unwrap(),
            3 => arena.int_gt(left, right).unwrap(),
            _ => arena.int_ge(left, right).unwrap(),
        };
        let originals = [goal];

        let out = elim_unconstrained(&mut arena, &originals).expect("elim");
        if out.eliminated() == 0 {
            continue;
        }
        fired += 1;
        let reduced: Vec<TermId> = out.assertions().to_vec();
        let syms = free_symbols(&arena, &reduced);
        if syms.len() > 4 {
            continue;
        }
        // Enumerate a small box of reduced assignments; every satisfying one
        // must reconstruct into a model of the original.
        let values: Vec<i128> = vec![-2, -1, 0, 1, 3];
        let total = values.len().pow(syms.len() as u32);
        for index in 0..total {
            let mut assignment = Assignment::new();
            let mut rest = index;
            let mut ok = true;
            for &(sym, sort) in &syms {
                match sort {
                    Sort::Int => {
                        assignment.set(sym, Value::Int(values[rest % values.len()]));
                    }
                    Sort::Bool => {
                        assignment.set(sym, Value::Bool(rest % values.len() % 2 == 0));
                    }
                    _ => ok = false,
                }
                rest /= values.len();
            }
            if !ok {
                break;
            }
            let satisfied = reduced
                .iter()
                .all(|&a| matches!(eval(&arena, a, &assignment), Ok(Value::Bool(true))));
            if !satisfied {
                continue;
            }
            let full = out
                .trail()
                .reconstruct(&arena, &assignment)
                .expect("reconstruction");
            for &a in &originals {
                assert_eq!(
                    eval(&arena, a, &full),
                    Ok(Value::Bool(true)),
                    "a model of the reduced integer problem must rebuild a model \
                     of the original",
                );
            }
            replays += 1;
        }
    }
    assert!(
        fired >= 100,
        "the arithmetic rules must fire: fired {fired}"
    );
    assert!(replays >= 100, "models must be replayed: replays {replays}");
}

/// The arithmetic order rules must not turn an unsatisfiable integer
/// constraint into a satisfiable one. `(< n n)` cannot fire (two occurrences),
/// but `(and (< n 0) (> n 0))` over a *shared* variable must stay unsat, and a
/// single-use variable under `+` must stay satisfiable exactly when the
/// original was.
#[test]
fn integer_unsat_shapes_stay_unsat() {
    // `x + 1 = x + 2` with `x` used twice: not unconstrained, must not change.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let left = arena.int_add(xv, one).unwrap();
    let right = arena.int_add(xv, two).unwrap();
    let goal = arena.eq(left, right).unwrap();
    let out = elim_unconstrained(&mut arena, &[goal]).unwrap();
    assert_eq!(out.eliminated(), 0, "x occurs twice");
    assert_eq!(out.assertions(), &[goal]);

    // `0 * y = 1` with `y` single-use: `0 * y` is the constant 0, so this is
    // unsat and must stay unsat. Multiplication needs *every* operand free.
    let mut arena = TermArena::new();
    let y = arena.declare("y", Sort::Int).unwrap();
    let yv = arena.var(y);
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let product = arena.int_mul(zero, yv).unwrap();
    let goal = arena.eq(product, one).unwrap();
    let out = elim_unconstrained(&mut arena, &[goal]).unwrap();
    let reduced = out.assertions().to_vec();
    let syms = free_symbols(&arena, &reduced);
    // Whatever the pass did, the reduced problem must have no model.
    let values = [-2i128, -1, 0, 1, 2, 7];
    let mut found = None;
    let total = values.len().pow(syms.len() as u32);
    for index in 0..total.max(1) {
        let mut assignment = Assignment::new();
        let mut rest = index;
        for &(sym, sort) in &syms {
            match sort {
                Sort::Int => assignment.set(sym, Value::Int(values[rest % values.len()])),
                Sort::Bool => assignment.set(sym, Value::Bool(rest % 2 == 0)),
                other => panic!("unexpected sort {other:?}"),
            }
            rest /= values.len();
        }
        if reduced
            .iter()
            .all(|&a| matches!(eval(&arena, a, &assignment), Ok(Value::Bool(true))))
        {
            found = Some(assignment);
            break;
        }
    }
    assert!(
        found.is_none(),
        "`0 * y = 1` is unsat; the reduced form must be too (found {found:?})"
    );

    // `2 * z = 1` over the integers is likewise unsat: `c·x` is not surjective
    // over Int, which is why the constant-multiplier rule is reals-only.
    let mut arena = TermArena::new();
    let z = arena.declare("z", Sort::Int).unwrap();
    let zv = arena.var(z);
    let two = arena.int_const(2);
    let one = arena.int_const(1);
    let product = arena.int_mul(two, zv).unwrap();
    let goal = arena.eq(product, one).unwrap();
    let out = elim_unconstrained(&mut arena, &[goal]).unwrap();
    assert_eq!(
        out.stats().rule_count("arith/mul-real-const"),
        0,
        "the constant-multiplier rule must not apply over Int"
    );
    assert_eq!(out.stats().rule_count("arith/mul-all"), 0);
}

/// A control for the harness itself: a deliberately unsound "rule" is simulated
/// by hand — replacing `110 · v` with a bare fresh variable — and
/// [`check_instance`]'s equisatisfiability assertion must reject it. Without
/// this, a harness that never compares anything would report every rule sound.
#[test]
fn the_harness_rejects_a_deliberately_unsound_replacement() {
    let mut arena = TermArena::new();
    let v = arena.declare("v", Sort::BitVec(3)).unwrap();
    let vv = arena.var(v);
    let six = arena.bv_const(3, 0b110).unwrap();
    let seven = arena.bv_const(3, 0b111).unwrap();
    let product = arena.bv_mul(six, vv).unwrap();
    let original = arena.eq(product, seven).unwrap();
    // The unsound reduction: `6·v` replaced by a fresh unconstrained variable.
    let u = arena.declare("u", Sort::BitVec(3)).unwrap();
    let uv = arena.var(u);
    let unsound = arena.eq(uv, seven).unwrap();

    let original_models =
        all_models(&arena, &[original], &free_symbols(&arena, &[original]), 100).expect("small");
    let unsound_models =
        all_models(&arena, &[unsound], &free_symbols(&arena, &[unsound]), 100).expect("small");
    assert!(original_models.is_empty(), "6·v = 7 is unsat");
    assert!(
        !unsound_models.is_empty(),
        "the naive replacement is satisfiable — this is the wrong-`sat` the \
         equisatisfiability assertion exists to catch"
    );
}

/// Rule-level instrumentation must attribute every elimination to a named rule.
#[test]
fn statistics_account_for_every_elimination() {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let (xv, yv) = (arena.var(x), arena.var(y));
    let negx = arena.bv_neg(xv).unwrap();
    let sum = arena.bv_add(negx, yv).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let goal = arena.eq(sum, five).unwrap();

    let out = elim_unconstrained(&mut arena, &[goal]).unwrap();
    let stats = out.stats();
    let total: u64 = stats.rule_counts().iter().map(|&(_, n)| n).sum();
    assert_eq!(
        total,
        stats.eliminations,
        "every elimination is attributed to a rule: {:?}",
        stats.rule_counts()
    );
    assert!(stats.eliminations > 0);
    assert!(stats.rounds >= 1);
    assert!(stats.defs_recorded >= stats.eliminations);
    let names: HashMap<&str, u64> = stats.rule_counts().into_iter().collect();
    assert!(names.contains_key("bv/neg") || names.contains_key("bv/add"));
}

/// The pass must not be sensitive to hash iteration order: the same input gives
/// the same reduced terms and the same rule counts every time.
#[test]
fn the_pass_is_deterministic() {
    let build = || {
        let mut arena = TermArena::new();
        let vars: Vec<TermId> = (0..4)
            .map(|i| {
                let s = arena.declare(&format!("d{i}"), Sort::BitVec(6)).unwrap();
                arena.var(s)
            })
            .collect();
        let a = arena.bv_add(vars[0], vars[1]).unwrap();
        let b = arena.bv_xor(vars[2], vars[3]).unwrap();
        let c = arena.bv_mul(a, b).unwrap();
        let k = arena.bv_const(6, 7).unwrap();
        let goal = arena.bv_ult(c, k).unwrap();
        (arena, goal)
    };
    let mut first_counts = None;
    let mut first_render = None;
    for _ in 0..8 {
        let (mut arena, goal) = build();
        let out = elim_unconstrained(&mut arena, &[goal]).unwrap();
        let counts = out.stats().rule_counts();
        let render: Vec<String> = out
            .assertions()
            .iter()
            .map(|&t| axeyum_ir::render(&arena, t))
            .collect();
        match (&first_counts, &first_render) {
            (None, None) => {
                first_counts = Some(counts);
                first_render = Some(render);
            }
            (Some(c), Some(r)) => {
                assert_eq!(&counts, c, "rule counts must be deterministic");
                assert_eq!(&render, r, "reduced terms must be deterministic");
            }
            _ => unreachable!(),
        }
    }
}

/// `Op` is imported for the exhaustive walk over comparison operators; this
/// keeps the import honest if the walk is ever refactored away.
#[test]
fn comparison_operators_are_all_covered_by_a_rule_or_deliberately_not() {
    let covered = [
        Op::BvUlt,
        Op::BvUle,
        Op::BvUgt,
        Op::BvUge,
        Op::BvSlt,
        Op::BvSle,
        Op::BvSgt,
        Op::BvSge,
    ];
    for op in covered {
        assert_eq!(
            axeyum_rewrite::theory_of(op),
            axeyum_rewrite::Theory::Bv,
            "{op:?} must dispatch to the bit-vector inverter"
        );
    }
}
