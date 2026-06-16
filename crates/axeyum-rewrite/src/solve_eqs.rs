//! Top-level equation solving / variable substitution (Track 1, P1.2 / T1.2.3).
//!
//! `solve_eqs` is the high-impact word-level pass: it orients a top-level equality
//! `(= x t)` (or `(= t x)`) into a definition `x := t` whenever `x` is a variable
//! that does **not** occur in `t` (the occurs-check that rules out a cyclic
//! `x = f(x)`), substitutes `t` for `x` throughout the remaining assertions, drops
//! the defining equality, and repeats to a fixpoint. Eliminating a variable this
//! way removes it from the bit-blasted problem entirely — Z3's `solve_eqs` is one
//! of its most effective pre-bit-blast stages for exactly this reason.
//!
//! This generalizes [`crate::propagate_values`] (a constant is just a `t` with no
//! variables); run the cheaper constant pass first, then this one.
//!
//! **Model-sound** via the [`ModelReconstructionTrail`]: each `x := t` is recorded,
//! and a `sat` model of the reduced problem reconstructs by evaluating `t` (under
//! the already-reconstructed later eliminations) and assigning `x`. The captured
//! definition `t` is *not* rewritten by subsequent eliminations — reverse replay
//! evaluates it under the full reconstructed model, so a `t` that mentions a
//! later-eliminated variable still resolves correctly.
//!
//! **No blow-up:** terms are DAG-interned, so substituting `x := t` shares `t`'s
//! nodes rather than copying them; the bit-blasted DAG grows linearly even for
//! substitution chains `x1 = f(x2), x2 = f(x3), …`.

use std::collections::{HashMap, HashSet};

use axeyum_ir::{IrError, Op, SymbolId, TermArena, TermId, TermNode};

use crate::canonical::replace_subterms;
use crate::reconstruct::ModelReconstructionTrail;

/// The result of [`solve_eqs`]: the variable-reduced assertions plus the trail
/// that rebuilds eliminated variables for model reconstruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EqSolution {
    assertions: Vec<TermId>,
    trail: ModelReconstructionTrail,
}

impl EqSolution {
    /// The reduced assertions (defining equalities removed, variables substituted).
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

/// Whether `sym` occurs anywhere in `term`, memoized over the shared term DAG so a
/// heavily-shared term is walked once.
fn occurs(
    arena: &TermArena,
    term: TermId,
    sym: SymbolId,
    memo: &mut HashMap<TermId, bool>,
) -> bool {
    if let Some(&hit) = memo.get(&term) {
        return hit;
    }
    let hit = match arena.node(term) {
        TermNode::Symbol(s) => *s == sym,
        TermNode::App { args, .. } => {
            let args = args.clone();
            args.iter().any(|&a| occurs(arena, a, sym, memo))
        }
        _ => false,
    };
    memo.insert(term, hit);
    hit
}

/// Detects a top-level `(= x t)` solvable for an as-yet-undefined variable `x`
/// with `x ∉ t` (occurs-check), returning `(x, t)`.
fn detect_solvable(
    arena: &TermArena,
    a: TermId,
    defined: &HashSet<SymbolId>,
) -> Option<(SymbolId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(a) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (l, r) = (args[0], args[1]);
    let mut memo = HashMap::new();
    // Prefer orienting on the left symbol, then the right.
    if let TermNode::Symbol(s) = arena.node(l) {
        if !defined.contains(s) && !occurs(arena, r, *s, &mut memo) {
            return Some((*s, r));
        }
    }
    if let TermNode::Symbol(s) = arena.node(r) {
        memo.clear();
        if !defined.contains(s) && !occurs(arena, l, *s, &mut memo) {
            return Some((*s, l));
        }
    }
    None
}

/// Solves top-level equalities by variable substitution (see module docs).
///
/// # Errors
///
/// Returns [`IrError`] only if rebuilding a substituted term fails sort checking,
/// which cannot happen here (`x` and its equal term `t` share a sort).
pub fn solve_eqs(arena: &mut TermArena, assertions: &[TermId]) -> Result<EqSolution, IrError> {
    let mut current: Vec<TermId> = assertions.to_vec();
    let mut trail = ModelReconstructionTrail::new();
    let mut defined: HashSet<SymbolId> = HashSet::new();

    loop {
        let found = current
            .iter()
            .enumerate()
            .find_map(|(i, &a)| detect_solvable(arena, a, &defined).map(|(s, t)| (i, s, t)));
        let Some((index, sym, definition)) = found else {
            break;
        };

        trail.define(sym, definition);
        defined.insert(sym);
        current.remove(index);
        let var_term = arena.var(sym);
        let replacements = HashMap::from([(var_term, definition)]);
        let mut memo: HashMap<TermId, TermId> = HashMap::new();
        for a in &mut current {
            *a = replace_subterms(arena, *a, &replacements, &mut memo)?;
        }
    }

    Ok(EqSolution {
        assertions: current,
        trail,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::{Assignment, Sort, Value, eval};

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
    fn eliminates_a_variable_equal_to_a_term() {
        // (= x (bvadd y 1)) and (= (bvmul x y) 12): x is replaced by y+1.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let one = arena.bv_const(8, 1).unwrap();
        let y_plus_1 = arena.bv_add(yv, one).unwrap();
        let x_def = arena.eq(xv, y_plus_1).unwrap();
        let prod = arena.bv_mul(xv, yv).unwrap();
        let twelve = arena.bv_const(8, 12).unwrap();
        let prod_is_12 = arena.eq(prod, twelve).unwrap();
        let originals = [x_def, prod_is_12];

        let out = solve_eqs(&mut arena, &originals).unwrap();
        assert_eq!(out.eliminated(), 1);
        assert_eq!(
            out.assertions().len(),
            1,
            "the defining equality is dropped"
        );
        for &a in out.assertions() {
            assert!(!occurs(&arena, a, x, &mut HashMap::new()));
        }

        // Reduced: (= (bvmul (bvadd y 1) y) 12). y = 3 → 4*3 = 12. ✓
        let mut reduced = Assignment::new();
        reduced.set(y, Value::Bv { width: 8, value: 3 });
        assert_eq!(
            eval(&arena, out.assertions()[0], &reduced).unwrap(),
            Value::Bool(true)
        );
        let full = out.trail().reconstruct(&arena, &reduced).unwrap();
        assert_eq!(full.get(x), Some(Value::Bv { width: 8, value: 4 }));
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn occurs_check_blocks_cyclic_definition() {
        // (= x (bvadd x 1)) is x = x+1 — never solvable for x (and unsat). The
        // occurs-check must refuse to orient it, leaving it in place.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let one = arena.bv_const(8, 1).unwrap();
        let x_plus_1 = arena.bv_add(xv, one).unwrap();
        let cyclic = arena.eq(xv, x_plus_1).unwrap();

        let out = solve_eqs(&mut arena, &[cyclic]).unwrap();
        assert_eq!(out.eliminated(), 0, "cyclic equality must not be solved");
        assert_eq!(out.assertions(), &[cyclic]);
    }

    #[test]
    fn chains_substitutions_and_reconstructs() {
        // (= x (bvadd y 1)), (= y z), (= z 4): x→y+1, y→z, z→4.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let z = arena.declare("z", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let zv = arena.var(z);
        let one = arena.bv_const(8, 1).unwrap();
        let y_plus_1 = arena.bv_add(yv, one).unwrap();
        let x_def = arena.eq(xv, y_plus_1).unwrap();
        let y_def = arena.eq(yv, zv).unwrap();
        let four = arena.bv_const(8, 4).unwrap();
        let z_def = arena.eq(zv, four).unwrap();
        let originals = [x_def, y_def, z_def];

        let out = solve_eqs(&mut arena, &originals).unwrap();
        assert_eq!(out.eliminated(), 3);
        assert!(out.assertions().is_empty());

        let full = out.trail().reconstruct(&arena, &Assignment::new()).unwrap();
        assert_eq!(full.get(z), Some(Value::Bv { width: 8, value: 4 }));
        assert_eq!(full.get(y), Some(Value::Bv { width: 8, value: 4 }));
        assert_eq!(full.get(x), Some(Value::Bv { width: 8, value: 5 }));
        assert_satisfies(&arena, &originals, &full);
    }

    /// Deterministic xorshift PRNG (no clock/`Math.random`).
    fn xorshift(state: &mut u64) -> u64 {
        let mut v = *state;
        v ^= v << 13;
        v ^= v >> 7;
        v ^= v << 17;
        *state = v;
        v
    }

    #[test]
    fn random_definitions_reconstruct_to_satisfy_originals() {
        // Build satisfiable instances of the shape: a chain of definitions
        // x_i = (x_{i+1} op c_i) plus one anchoring x_last = const, all over 8-bit
        // BV. solve_eqs must eliminate every x_i; reconstruction (from the empty
        // reduced model) must satisfy every original definition.
        let mut state = 0x5151_5151_2727_2727u64;
        for trial in 0..200 {
            let mut arena = TermArena::new();
            let n = 2 + (xorshift(&mut state) % 5) as usize; // 2..=6 variables
            let syms: Vec<_> = (0..n)
                .map(|i| arena.declare(&format!("x{i}"), Sort::BitVec(8)).unwrap())
                .collect();
            let vars: Vec<_> = syms.iter().map(|&s| arena.var(s)).collect();

            let mut originals = Vec::new();
            // x_i = x_{i+1} + c_i  (i = 0..n-1)
            for i in 0..n - 1 {
                let c = arena
                    .bv_const(8, u128::from(xorshift(&mut state) % 256))
                    .unwrap();
                let rhs = arena.bv_add(vars[i + 1], c).unwrap();
                originals.push(arena.eq(vars[i], rhs).unwrap());
            }
            // anchor: x_{n-1} = const
            let anchor = arena
                .bv_const(8, u128::from(xorshift(&mut state) % 256))
                .unwrap();
            originals.push(arena.eq(vars[n - 1], anchor).unwrap());

            let out = solve_eqs(&mut arena, &originals).unwrap();
            assert!(
                out.assertions().is_empty(),
                "trial {trial}: all definitions should be solved, left {:?}",
                out.assertions()
            );
            let full = out.trail().reconstruct(&arena, &Assignment::new()).unwrap();
            assert_satisfies(&arena, &originals, &full);
        }
    }
}
