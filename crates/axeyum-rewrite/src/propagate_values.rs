//! Constant propagation (Track 1, P1.2 / task T1.2.2).
//!
//! `propagate_values` is the first word-level preprocessing pass: it finds
//! top-level facts that pin a variable to a constant — `(= x c)`, `(= c x)`, a
//! bare Boolean assertion `p` (so `p = true`), or `(not p)` (so `p = false`) —
//! substitutes that constant for the variable throughout the remaining assertions,
//! drops the now-redundant defining assertion, and repeats to a fixpoint (a
//! substitution can expose a fresh fact, e.g. `(= y x)` once `x` is known).
//! Independent facts are applied together in one DAG rebuild per fixpoint round;
//! this avoids quadratic intermediate terms on definition-heavy generated input.
//!
//! Every eliminated variable is recorded in a [`ModelReconstructionTrail`], so the
//! pass is **model-sound**: the backend solves the smaller, variable-reduced
//! problem, and a `sat` model reconstructs — `x` is reassigned its constant — into
//! a model that satisfies the *original* assertions. Because the substituted
//! constant is literally the variable's only possible value, this is also
//! satisfiability-preserving for `unsat` (a conflicting `(= x c1)`/`(= x c2)`
//! collapses to a constant disequality the backend rejects).
//!
//! Scope: this pass only acts on *syntactic* top-level variable-equals-constant
//! facts. Variable-equals-term elimination (`x = t`) is `solve_eqs` (T1.2.3); deep
//! constant folding is the canonicalizer's job. Keeping the pass small keeps it
//! obviously sound.

use std::collections::{HashMap, HashSet};

use axeyum_ir::{
    Assignment, IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
};

use crate::canonical::replace_subterms;
use crate::reconstruct::ModelReconstructionTrail;

/// The result of [`propagate_values`]: the variable-reduced assertions plus the
/// trail that rebuilds the eliminated variables' values for model reconstruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValuePropagation {
    assertions: Vec<TermId>,
    trail: ModelReconstructionTrail,
}

impl ValuePropagation {
    /// The reduced assertions (the defining facts removed, their variables
    /// substituted by constants throughout).
    #[must_use]
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// The model-reconstruction trail for the eliminated variables.
    #[must_use]
    pub fn trail(&self) -> &ModelReconstructionTrail {
        &self.trail
    }

    /// Number of variables eliminated.
    #[must_use]
    pub fn eliminated(&self) -> usize {
        self.trail.len()
    }

    /// Consumes into `(reduced assertions, trail)`.
    #[must_use]
    pub fn into_parts(self) -> (Vec<TermId>, ModelReconstructionTrail) {
        (self.assertions, self.trail)
    }
}

/// Whether a term node is a literal constant of any sort.
fn is_constant(node: &TermNode) -> bool {
    matches!(
        node,
        TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_)
    )
}

/// Whether evaluating `term` would have to consult an **underspecified** value:
/// a `div`/`mod`/`/` node whose divisor is not a provably non-zero constant.
///
/// The ground evaluator is *total* — it resolves `div a 0`/`mod a 0`/`a / 0` with
/// the in-tree conventions (`0`, `a`, `0`). Those are legitimate values for a
/// *witness*, but SMT-LIB fixes no value for them, so they are not facts about
/// every model, and a rewrite that commits to one produces a WRONG UNSAT.
/// Measured before this guard existed, through the shipped front door:
/// `(= x (div 5 0)) ∧ x > 100` and `(= x (mod 0 0)) ∧ x > 775` both returned
/// `unsat`, while both are `sat` (the free value can be anything). The equivalent
/// query without the defining equality — `(< 775 (mod 0 0))` — was already
/// correctly `sat`, because [`crate::eliminate_int_divmod`] models a zero divisor
/// as a fresh congruent variable; the hole was this pass alone, folding the term
/// to the convention *before* that pass ever saw it. Same defect class as the P0
/// regressed by `a946f925` and fixed by `52f3b1d1`.
///
/// The test is deliberately conservative: a divisor that does not evaluate to a
/// definite non-zero constant counts as underspecified. A non-ground divisor makes
/// the enclosing `eval` fail anyway, so nothing is lost.
fn depends_on_underspecified_division(arena: &TermArena, term: TermId) -> bool {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack = vec![term];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        if matches!(op, Op::IntDiv | Op::IntMod | Op::RealDiv) {
            let divisor_nonzero = match eval(arena, args[1], &Assignment::new()) {
                Ok(Value::Int(value)) => value != 0,
                Ok(Value::Real(value)) => !value.is_zero(),
                _ => false,
            };
            if !divisor_nonzero {
                return true;
            }
        }
        stack.extend(args.iter().copied());
    }
    false
}

/// Reifies a ground evaluator result while preserving finite-domain wrapper
/// sorts whose runtime representation is a bit-vector.
///
/// Declines any term whose value depends on an underspecified division — see
/// [`depends_on_underspecified_division`].
fn ground_constant(arena: &mut TermArena, term: TermId) -> Option<TermId> {
    if is_constant(arena.node(term)) {
        return Some(term);
    }
    if depends_on_underspecified_division(arena, term) {
        return None;
    }
    let sort = arena.sort_of(term);
    let value = eval(arena, term, &Assignment::new()).ok()?;
    match (sort, value) {
        (Sort::Bool, Value::Bool(value)) => Some(arena.bool_const(value)),
        (Sort::BitVec(width), Value::Bv { width: got, value }) if width == got => {
            arena.bv_const(width, value).ok()
        }
        (Sort::Float { exp, sig }, Value::Bv { width, value }) if width == exp + sig => {
            let bits = arena.bv_const(width, value).ok()?;
            arena.fp_from_bits(bits, exp, sig).ok()
        }
        (Sort::RoundingMode, Value::Bv { width: 3, value }) => {
            let bits = arena.bv_const(3, value).ok()?;
            arena.rounding_mode_from_bits(bits).ok()
        }
        (Sort::Int, Value::Int(value)) => Some(arena.int_const(value)),
        (Sort::Real, Value::Real(value)) => Some(arena.real_const(value)),
        _ => None,
    }
}

/// Detects a top-level `variable = constant` fact in assertion `a`, returning the
/// eliminated symbol and the constant term it equals. `bool_true`/`bool_false` are
/// the interned Boolean constants used for bare-literal assertions.
fn detect_fact(
    arena: &mut TermArena,
    a: TermId,
    bool_true: TermId,
    bool_false: TermId,
) -> Option<(SymbolId, TermId)> {
    match arena.node(a) {
        // A bare Boolean variable asserted true.
        TermNode::Symbol(s) => Some((*s, bool_true)),
        TermNode::App { op, args } => match op {
            // `(not p)` with `p` a variable: `p = false`.
            Op::BoolNot if args.len() == 1 => match arena.node(args[0]) {
                TermNode::Symbol(s) => Some((*s, bool_false)),
                _ => None,
            },
            // `(= x c)` / `(= c x)` with one side a variable and the other a constant.
            Op::Eq if args.len() == 2 => {
                let (l, r) = (args[0], args[1]);
                if let TermNode::Symbol(s) = arena.node(l).clone()
                    && let Some(constant) = ground_constant(arena, r)
                {
                    return Some((s, constant));
                }
                if let TermNode::Symbol(s) = arena.node(r).clone()
                    && let Some(constant) = ground_constant(arena, l)
                {
                    return Some((s, constant));
                }
                None
            }
            _ => None,
        },
        _ => None,
    }
}

/// Propagates top-level `variable = constant` facts (see module docs).
///
/// # Errors
///
/// Returns [`IrError`] only if rebuilding a substituted term fails sort checking,
/// which cannot happen here (a variable and its equal constant share a sort).
pub fn propagate_values(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<ValuePropagation, IrError> {
    let bool_true = arena.bool_const(true);
    let bool_false = arena.bool_const(false);

    let mut current: Vec<TermId> = assertions.to_vec();
    let mut trail = ModelReconstructionTrail::new();
    let mut defined: HashSet<SymbolId> = HashSet::new();

    loop {
        // Select the first defining assertion for every as-yet-undefined symbol.
        // All selected right-hand sides are ground constants, so their
        // substitutions are independent and can share one DAG rebuild. Facts
        // exposed by these substitutions are picked up in the next round.
        let mut selected = vec![false; current.len()];
        let mut round_definitions = Vec::new();
        let mut round_symbols = HashSet::new();
        for (index, &assertion) in current.iter().enumerate() {
            if let Some((symbol, constant)) = detect_fact(arena, assertion, bool_true, bool_false)
                && !defined.contains(&symbol)
                && round_symbols.insert(symbol)
            {
                selected[index] = true;
                round_definitions.push((symbol, constant));
            }
        }
        if round_definitions.is_empty() {
            break;
        }

        let mut replacements = HashMap::with_capacity(round_definitions.len());
        for (symbol, constant) in round_definitions {
            trail.define(symbol, constant);
            defined.insert(symbol);
            replacements.insert(arena.var(symbol), constant);
        }

        // Drop each selected defining assertion and apply every independent
        // substitution while sharing one memo across the remaining roots.
        let mut memo: HashMap<TermId, TermId> = HashMap::new();
        let mut next = Vec::with_capacity(current.len() - selected.iter().filter(|&&x| x).count());
        for (index, assertion) in current.into_iter().enumerate() {
            if !selected[index] {
                next.push(replace_subterms(
                    arena,
                    assertion,
                    &replacements,
                    &mut memo,
                )?);
            }
        }
        current = next;
    }

    Ok(ValuePropagation {
        assertions: current,
        trail,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::{Assignment, Sort, Value, eval};

    /// Asserts every original assertion holds under `model`.
    fn assert_satisfies(arena: &TermArena, originals: &[TermId], model: &Assignment) {
        for &a in originals {
            assert_eq!(
                eval(arena, a, model).unwrap(),
                Value::Bool(true),
                "reconstructed model must satisfy original assertion #{}",
                a.index()
            );
        }
    }

    /// The `(= x (div 5 0))` / `(= x (mod 0 0))` shapes from
    /// [`depends_on_underspecified_division`]'s doc: pinning `x` to the
    /// evaluator's div-by-zero convention refutes satisfiable formulas (wrong
    /// `unsat`, the `a946f925` class). The pass must decline the definition and
    /// leave both assertions for `eliminate_int_divmod` to model soundly.
    #[test]
    fn declines_definitions_pinned_to_underspecified_division() {
        for make in [
            |arena: &mut TermArena| {
                let five = arena.int_const(5);
                let zero = arena.int_const(0);
                arena.int_div(five, zero).unwrap()
            },
            |arena: &mut TermArena| {
                let zero = arena.int_const(0);
                arena.int_mod(zero, zero).unwrap()
            },
        ] {
            let mut arena = TermArena::new();
            let x = arena.declare("x", Sort::Int).unwrap();
            let xv = arena.var(x);
            let division = make(&mut arena);
            let def = arena.eq(xv, division).unwrap();
            let hundred = arena.int_const(100);
            let bound = arena.int_gt(xv, hundred).unwrap();
            let originals = [def, bound];

            let out = propagate_values(&mut arena, &originals).unwrap();
            assert_eq!(
                out.eliminated(),
                0,
                "x must not be pinned to a div/mod-by-zero convention value"
            );
            assert_eq!(out.assertions().len(), 2, "both assertions must survive");
        }
    }

    /// Positive control for the guard: a fully specified ground division is
    /// still propagated.
    #[test]
    fn propagates_a_specified_ground_division() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let n48 = arena.int_const(48);
        let n4 = arena.int_const(4);
        let quotient = arena.int_div(n48, n4).unwrap();
        let def = arena.eq(xv, quotient).unwrap();
        let ten = arena.int_const(10);
        let bound = arena.int_gt(xv, ten).unwrap();
        let originals = [def, bound];

        let out = propagate_values(&mut arena, &originals).unwrap();
        assert_eq!(out.eliminated(), 1, "x is pinned to the definite value 12");
        let full = out.trail().reconstruct(&arena, &Assignment::new()).unwrap();
        assert_eq!(full.get(x), Some(Value::Int(12)));
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn eliminates_a_variable_equal_to_a_constant() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let seven = arena.bv_const(8, 7).unwrap();
        let ten = arena.bv_const(8, 10).unwrap();
        let x_is_seven = arena.eq(xv, seven).unwrap();
        let sum = arena.bv_add(xv, yv).unwrap();
        let sum_is_ten = arena.eq(sum, ten).unwrap();
        let originals = [x_is_seven, sum_is_ten];

        let out = propagate_values(&mut arena, &originals).unwrap();
        assert_eq!(out.eliminated(), 1, "x should be eliminated");
        assert_eq!(out.assertions().len(), 1, "the defining (= x 7) is dropped");
        // x no longer occurs in the reduced assertions.
        for &a in out.assertions() {
            assert!(!mentions(&arena, a, x), "x must be substituted away");
        }

        // Solve the reduced problem by hand: y = 3 satisfies (= (bvadd 7 y) 10).
        let mut reduced = Assignment::new();
        reduced.set(y, Value::Bv { width: 8, value: 3 });
        // Sanity: the reduced assertion holds.
        assert_eq!(
            eval(&arena, out.assertions()[0], &reduced).unwrap(),
            Value::Bool(true)
        );

        let full = out.trail().reconstruct(&arena, &reduced).unwrap();
        assert_eq!(full.get(x), Some(Value::Bv { width: 8, value: 7 }));
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn propagates_through_a_chain() {
        // (= x 5) and (= y x): once x is 5, (= y x) becomes (= y 5), a new fact.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let five = arena.bv_const(8, 5).unwrap();
        let x_is_five = arena.eq(xv, five).unwrap();
        let y_is_x = arena.eq(yv, xv).unwrap();
        let originals = [x_is_five, y_is_x];

        let out = propagate_values(&mut arena, &originals).unwrap();
        assert_eq!(out.eliminated(), 2, "both x and y are pinned");
        assert!(out.assertions().is_empty(), "everything was a definition");

        let full = out.trail().reconstruct(&arena, &Assignment::new()).unwrap();
        assert_eq!(full.get(x), Some(Value::Bv { width: 8, value: 5 }));
        assert_eq!(full.get(y), Some(Value::Bv { width: 8, value: 5 }));
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn batches_independent_definitions_without_quadratic_dag_growth() {
        let mut arena = TermArena::new();
        let zero = arena.bv_const(16, 0).unwrap();
        let mut assertions = Vec::new();
        let mut sum = zero;
        let mut expected = 0u64;

        for index in 0..64u64 {
            let name = format!("x{index}");
            let symbol = arena.declare(&name, Sort::BitVec(16)).unwrap();
            let variable = arena.var(symbol);
            let constant = arena.bv_const(16, u128::from(index)).unwrap();
            assertions.push(arena.eq(variable, constant).unwrap());
            sum = arena.bv_add(sum, variable).unwrap();
            expected += index;
        }
        let expected = arena.bv_const(16, u128::from(expected)).unwrap();
        assertions.push(arena.eq(sum, expected).unwrap());

        let before = arena.len();
        let out = propagate_values(&mut arena, &assertions).unwrap();
        let growth = arena.len() - before;

        assert_eq!(out.eliminated(), 64);
        assert_eq!(out.assertions().len(), 1);
        assert_eq!(
            eval(&arena, out.assertions()[0], &Assignment::new()).unwrap(),
            Value::Bool(true)
        );
        assert!(
            growth < 128,
            "one batched rebuild should stay linear; added {growth} arena nodes"
        );
        let full = out.trail().reconstruct(&arena, &Assignment::new()).unwrap();
        assert_satisfies(&arena, &assertions, &full);
    }

    #[test]
    fn propagates_ground_evaluable_float_definition_without_losing_its_sort() {
        let mut arena = TermArena::new();
        let symbol = arena.declare("f", Sort::Float { exp: 8, sig: 24 }).unwrap();
        let variable = arena.var(symbol);
        let one = arena.bv_const(32, 1).unwrap();
        let two = arena.bv_const(32, 2).unwrap();
        let sum = arena.bv_add(one, two).unwrap();
        let ground_float = arena.fp_from_bits(sum, 8, 24).unwrap();
        let definition = arena.eq(variable, ground_float).unwrap();

        let out = propagate_values(&mut arena, &[definition]).unwrap();
        assert_eq!(out.eliminated(), 1);
        assert!(out.assertions().is_empty());
        let reconstructed = out.trail().reconstruct(&arena, &Assignment::new()).unwrap();
        assert_eq!(
            reconstructed.get(symbol),
            Some(Value::Bv {
                width: 32,
                value: 3,
            })
        );
    }

    #[test]
    fn pins_boolean_literals_true_and_false() {
        // `p` (asserted true) and `(not q)` (so q = false), used in a third clause.
        let mut arena = TermArena::new();
        let p = arena.declare("p", Sort::Bool).unwrap();
        let q = arena.declare("q", Sort::Bool).unwrap();
        let r = arena.declare("r", Sort::Bool).unwrap();
        let pv = arena.var(p);
        let qv = arena.var(q);
        let rv = arena.var(r);
        let not_q = arena.not(qv).unwrap();
        // (or q r) : with q = false this forces r = true.
        let q_or_r = arena.or(qv, rv).unwrap();
        let originals = [pv, not_q, q_or_r];

        let out = propagate_values(&mut arena, &originals).unwrap();
        assert_eq!(out.eliminated(), 2, "p and q are pinned");

        // Reduced problem forces r = true; assign it.
        let mut reduced = Assignment::new();
        reduced.set(r, Value::Bool(true));
        let full = out.trail().reconstruct(&arena, &reduced).unwrap();
        assert_eq!(full.get(p), Some(Value::Bool(true)));
        assert_eq!(full.get(q), Some(Value::Bool(false)));
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn conflicting_constants_stay_and_are_unsatisfiable() {
        // (= x 1) and (= x 2): the first pins x = 1; the second becomes (= 1 2),
        // an unsatisfiable constant disequality preserved in the reduced set.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let one = arena.bv_const(8, 1).unwrap();
        let two = arena.bv_const(8, 2).unwrap();
        let x_is_one = arena.eq(xv, one).unwrap();
        let x_is_two = arena.eq(xv, two).unwrap();

        let out = propagate_values(&mut arena, &[x_is_one, x_is_two]).unwrap();
        assert_eq!(out.eliminated(), 1);
        assert_eq!(out.assertions().len(), 1);
        // The surviving assertion is constant-false under any assignment.
        assert_eq!(
            eval(&arena, out.assertions()[0], &Assignment::new()).unwrap(),
            Value::Bool(false),
            "(= 1 2) is unsatisfiable"
        );
    }

    #[test]
    fn no_facts_leaves_the_problem_unchanged() {
        // (= (bvadd x y) 3) has no top-level variable=constant fact.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let three = arena.bv_const(8, 3).unwrap();
        let sum = arena.bv_add(xv, yv).unwrap();
        let eq = arena.eq(sum, three).unwrap();

        let out = propagate_values(&mut arena, &[eq]).unwrap();
        assert_eq!(out.eliminated(), 0);
        assert_eq!(out.assertions(), &[eq]);
        assert!(out.trail().is_empty());
    }

    /// Whether `sym` appears anywhere in `term` (test helper).
    fn mentions(arena: &TermArena, term: TermId, sym: SymbolId) -> bool {
        match arena.node(term) {
            TermNode::Symbol(s) => *s == sym,
            TermNode::App { args, .. } => args.iter().any(|&a| mentions(arena, a, sym)),
            _ => false,
        }
    }
}
