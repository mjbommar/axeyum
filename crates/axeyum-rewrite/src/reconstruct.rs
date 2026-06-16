//! Model-reconstruction trail (Track 1, P1.2 / task T1.2.1).
//!
//! Word-level preprocessing shrinks the problem *before* bit-blasting by
//! eliminating symbols — `propagate_values` replaces a variable by a constant,
//! `solve_eqs` replaces it by a defining term, and so on. Each elimination makes
//! the reduced problem cheaper to solve, but the backend then returns a model over
//! the **surviving** symbols only. The reconstruction trail is what lets a `sat`
//! result still replay through the *original* assertions: every pass that drops a
//! symbol records how to recompute its value, and the trail replays those records
//! to extend a reduced model back to a full one.
//!
//! This is the term-level generalization of the maps axeyum already keeps for
//! soundness — the bit-blast lowering/lift maps, the array-elimination
//! `project_model` trail, and the CNF [`crate`]-adjacent BVE reconstruction stack.
//! Each is "remember enough to rebuild what you removed"; this type is the shared,
//! composable form for the preprocessing pipeline.
//!
//! **Soundness contract.** A [`Step::Define`] records that symbol `x` was
//! eliminated and equals `eval(definition)` under any model of the reduced
//! problem. Passes append steps in elimination order; [`Self::reconstruct`] replays
//! them **in reverse**, so a symbol whose definition mentions a later-eliminated
//! symbol still sees that symbol's reconstructed value (it was recorded after, and
//! is therefore replayed before). The definition term must only mention symbols
//! that are either present in the reduced model or reconstructed by a *later* step.

use axeyum_ir::{Assignment, IrError, SymbolId, TermArena, TermId, eval};

/// One reconstruction step: how to recover an eliminated symbol's value.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Step {
    /// Symbol `sym` was eliminated; its value is `eval(definition)` under the
    /// model reconstructed so far.
    Define { sym: SymbolId, definition: TermId },
}

/// An ordered log of symbol eliminations that extends a model of a reduced problem
/// back to a model over the original symbols. Append with [`Self::define`] in
/// elimination order; apply with [`Self::reconstruct`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ModelReconstructionTrail {
    /// Steps in elimination order; [`Self::reconstruct`] replays them in reverse.
    steps: Vec<Step>,
}

impl ModelReconstructionTrail {
    /// An empty trail (reconstructs to the reduced model unchanged).
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Records that `sym` was eliminated and equals `eval(definition)` under any
    /// model of the reduced problem. Call in elimination order.
    pub fn define(&mut self, sym: SymbolId, definition: TermId) {
        self.steps.push(Step::Define { sym, definition });
    }

    /// Whether the trail recorded no eliminations.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// Number of recorded eliminations.
    #[must_use]
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Appends another trail's steps after this one's (composition: `other`'s
    /// passes ran *after* this trail's, so they reconstruct first on replay).
    pub fn append(&mut self, mut other: ModelReconstructionTrail) {
        self.steps.append(&mut other.steps);
    }

    /// Extends a model of the reduced problem to a model over the original symbols.
    ///
    /// Replays the recorded eliminations in reverse order, evaluating each
    /// definition under the model reconstructed so far and assigning the eliminated
    /// symbol. The returned assignment agrees with `reduced` on every surviving
    /// symbol and additionally assigns every eliminated one.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] if a definition term cannot be evaluated under the
    /// reconstructed model (for a well-formed trail every definition's free symbols
    /// are already assigned by the time it is replayed, so this does not happen).
    pub fn reconstruct(
        &self,
        arena: &TermArena,
        reduced: &Assignment,
    ) -> Result<Assignment, IrError> {
        let mut model = reduced.clone();
        for step in self.steps.iter().rev() {
            match step {
                Step::Define { sym, definition } => {
                    let value = eval(arena, *definition, &model)?;
                    model.set(*sym, value);
                }
            }
        }
        Ok(model)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::{Sort, TermArena, Value};

    #[test]
    fn empty_trail_is_identity() {
        let mut arena = TermArena::new();
        let sym = arena.declare("y", Sort::BitVec(8)).unwrap();
        let mut model = Assignment::new();
        model.set(sym, Value::Bv { width: 8, value: 5 });

        let trail = ModelReconstructionTrail::new();
        assert!(trail.is_empty());
        let out = trail.reconstruct(&arena, &model).unwrap();
        assert_eq!(out.get(sym), Some(Value::Bv { width: 8, value: 5 }));
    }

    #[test]
    fn define_recovers_a_constant_symbol() {
        // x was eliminated as the constant 7; reconstruct must assign it.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let seven = arena.bv_const(8, 7).unwrap();

        let mut trail = ModelReconstructionTrail::new();
        trail.define(x, seven);

        let reduced = Assignment::new(); // x is gone from the reduced problem
        let full = trail.reconstruct(&arena, &reduced).unwrap();
        assert_eq!(full.get(x), Some(Value::Bv { width: 8, value: 7 }));
    }

    #[test]
    fn reverse_replay_resolves_chained_definitions() {
        // Eliminated in order: x = y + 1, then y = z (a later elimination whose
        // value x depends on). Reverse replay recovers y first, then x.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let z = arena.declare("z", Sort::BitVec(8)).unwrap();
        let yv = arena.var(y);
        let one = arena.bv_const(8, 1).unwrap();
        let y_plus_one = arena.bv_add(yv, one).unwrap();
        let zv = arena.var(z);

        let mut trail = ModelReconstructionTrail::new();
        trail.define(x, y_plus_one); // recorded first (eliminated first)
        trail.define(y, zv); // recorded later (eliminated later)

        // Reduced model assigns only the surviving symbol z = 4.
        let mut reduced = Assignment::new();
        reduced.set(z, Value::Bv { width: 8, value: 4 });

        let full = trail.reconstruct(&arena, &reduced).unwrap();
        assert_eq!(full.get(z), Some(Value::Bv { width: 8, value: 4 }));
        assert_eq!(full.get(y), Some(Value::Bv { width: 8, value: 4 })); // y = z = 4
        assert_eq!(full.get(x), Some(Value::Bv { width: 8, value: 5 })); // x = y + 1 = 5
    }

    #[test]
    fn append_composes_trails_in_pass_order() {
        // Trail A (first pass) eliminated y = x while x was still present; trail B
        // (second pass) then eliminated x = 3. Composition `a.append(b)` must
        // reconstruct B's elimination (x) before A's (y, which references x).
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let three = arena.bv_const(8, 3).unwrap();
        let xv = arena.var(x);

        let mut a = ModelReconstructionTrail::new();
        a.define(y, xv); // first pass: y = x (x still live)
        let mut b = ModelReconstructionTrail::new();
        b.define(x, three); // second pass: x = 3
        a.append(b);

        let full = a.reconstruct(&arena, &Assignment::new()).unwrap();
        assert_eq!(full.get(x), Some(Value::Bv { width: 8, value: 3 }));
        assert_eq!(full.get(y), Some(Value::Bv { width: 8, value: 3 }));
    }
}
