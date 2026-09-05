import Axeyum.Tactic
/-!
# Fragment 1 — linear arithmetic and ring identities over ℕ, in Lean core terms

Every goal here is stated the way a Lean user states it: `+`, `*`, `≤`, `<` at
`Nat`, elaborated through `HAdd.hAdd` / `instLENat` / the rest, with no
`Nat.add` spelled by hand and no Mathlib in sight. The tactic ships the
already-elaborated goal to Axeyum and Lean checks the term that comes back.

**The acceptance gate is this file elaborating.** `scripts/check-lean-tactic.sh`
counts the `AXEYUM-TACTIC-ACCEPTED` lines the `#print axioms` block below
emits and fails below a floor, because a file that elaborates and proves
nothing exits 0 exactly like a file that proves everything.

`#print axioms` on every theorem is the trust claim made checkable: a term
Axeyum produced must not have widened what Lean depends on. Lean core's own
arithmetic is axiom-free, so the expected output is
`does not depend on any axioms` for every one — and `sorryAx` appearing
anywhere would be the tactic having admitted something, which the tactic has
no path to do.
-/

set_option linter.unusedVariables false

namespace Tests.NatLinear

/-! ## ring: commutativity, associativity, distributivity -/

theorem add_comm' (a b : Nat) : a + b = b + a := by axeyum

theorem add_assoc' (a b c : Nat) : a + b + c = a + (b + c) := by axeyum

theorem add_right_comm' (a b c : Nat) : a + b + c = a + c + b := by axeyum

theorem mul_comm' (a b : Nat) : a * b = b * a := by axeyum

theorem left_distrib' (a b c : Nat) : a * (b + c) = a * b + a * c := by axeyum

/-! ## linarith: order goals, with and without hypotheses -/

theorem le_add_right' (a b : Nat) : a ≤ a + b := by axeyum

theorem le_add_left' (a b : Nat) : a ≤ b + a := by axeyum

theorem le_refl' (a : Nat) : a ≤ a := by axeyum

theorem zero_le' (a : Nat) : 0 ≤ a := by axeyum

theorem le_of_hyp (a b c : Nat) (hab : a ≤ b) : a ≤ b + c := by axeyum

theorem le_trans' (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by axeyum

/-! ## The axiom claim, one line per accepted goal.

`#print axioms` is what makes "adds no axiom" checkable rather than asserted.
The gate greps for `AXEYUM-TACTIC-ACCEPTED` and for the axiom lines together,
so a theorem that vanished takes the count down with it. -/

#print axioms add_comm'
#print axioms add_assoc'
#print axioms add_right_comm'
#print axioms mul_comm'
#print axioms left_distrib'
#print axioms le_add_right'
#print axioms le_add_left'
#print axioms le_refl'
#print axioms zero_le'
#print axioms le_of_hyp
#print axioms le_trans'

/-! ## The count, derived from the environment rather than from this comment.

A literal `11` here would measure the author's memory. This reads the
declarations back out of Lean's own environment, filtered to this namespace,
so deleting a theorem above moves the number. -/

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let mut accepted := 0
  for (name, info) in env.constants.toList do
    if name.getPrefix == `Tests.NatLinear && !name.isInternal then
      match info with
      | .thmInfo _ => accepted := accepted + 1
      | _ => pure ()
  Lean.logInfo s!"AXEYUM-TACTIC-ACCEPTED goals={accepted}"

end Tests.NatLinear
