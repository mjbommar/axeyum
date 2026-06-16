//! Constant propagation (Track 1, P1.2 / task T1.2.2).
//!
//! `propagate_values` is the first word-level preprocessing pass: it finds
//! top-level facts that pin a variable to a constant — `(= x c)`, `(= c x)`, a
//! bare Boolean assertion `p` (so `p = true`), or `(not p)` (so `p = false`) —
//! substitutes that constant for the variable throughout the remaining assertions,
//! drops the now-redundant defining assertion, and repeats to a fixpoint (a
//! substitution can expose a fresh fact, e.g. `(= y x)` once `x` is known).
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

use axeyum_ir::{IrError, Op, SymbolId, TermArena, TermId, TermNode};

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

/// Detects a top-level `variable = constant` fact in assertion `a`, returning the
/// eliminated symbol and the constant term it equals. `bool_true`/`bool_false` are
/// the interned Boolean constants used for bare-literal assertions.
fn detect_fact(
    arena: &TermArena,
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
                if let TermNode::Symbol(s) = arena.node(l) {
                    if is_constant(arena.node(r)) {
                        return Some((*s, r));
                    }
                }
                if let TermNode::Symbol(s) = arena.node(r) {
                    if is_constant(arena.node(l)) {
                        return Some((*s, l));
                    }
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
        // Find the first assertion that pins an as-yet-undefined variable.
        let found = current.iter().enumerate().find_map(|(i, &a)| {
            detect_fact(arena, a, bool_true, bool_false)
                .filter(|(s, _)| !defined.contains(s))
                .map(|(s, c)| (i, s, c))
        });
        let Some((index, sym, constant)) = found else {
            break;
        };

        trail.define(sym, constant);
        defined.insert(sym);
        // Drop the defining assertion; substitute the constant into the rest.
        current.remove(index);
        let var_term = arena.var(sym);
        let replacements = HashMap::from([(var_term, constant)]);
        let mut memo: HashMap<TermId, TermId> = HashMap::new();
        for a in &mut current {
            *a = replace_subterms(arena, *a, &replacements, &mut memo)?;
        }
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
