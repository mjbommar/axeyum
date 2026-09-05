import Lean
import Axeyum.Shim
/-!
# The name-correspondence table, checked by Lean

`Axeyum.Shim` is the mapping from axeyum's kernel constants to Lean, and it is
already checked by the fact that Lean elaborates it. This file adds the two
things that check are *not*:

1. **What each shim row costs in axioms.** A shim theorem is only as clean as
   the Lean-core lemma it is proved from, and Lean core is not uniformly
   axiom-free. Measured 2026-09-05 on `leanprover/lean4:v4.34.0-rc1`: **ten of
   the thirteen rows depend on no axiom at all**, and three reach `propext` —
   `natLeOfAddLeAddRight`, `natMulAssoc` and `natRightDistrib`. It does not
   split along the lines one would guess (five of the six *order* rows are
   clean; two of the seven *ring* rows are not), which is exactly why it is
   read from `#print axioms` and not asserted. That is Lean core's axiom use,
   not axeyum's: an axeyum-side proof of any of these is axiom-free, and the
   `propext` arrives when the statement is re-proved from Lean's library.
   ADR-1666 carries the measurement.

2. **That every row still corresponds.** Each `example` below re-derives the
   Lean-core lemma *from the shim row*, in the opposite direction to the shim's
   own proof. A row that quietly became a weaker statement would still
   elaborate as a theorem; it would not survive being used to reprove what it
   was supposed to correspond to.
-/

namespace Tests.ShimCorrespondence

open Axeyum.Shim

/-! ## 1. The axiom cost of each row -/

#print axioms natLeRefl
#print axioms natLeTrans
#print axioms natLeAddRight
#print axioms natAddLeAddLeft
#print axioms natAddLeAddRight
#print axioms natLeOfAddLeAddRight
#print axioms natAddComm
#print axioms natAddAssoc
#print axioms natAddRightComm
#print axioms natMulComm
#print axioms natMulAssoc
#print axioms natLeftDistrib
#print axioms natRightDistrib

/-! ## 2. Each row reproves its Lean-core counterpart

The shim's own proofs go core → shim. These go shim → core, so a row that had
been weakened (an argument dropped, a bound loosened, a side swapped) fails
here even though it would still be a well-typed theorem. -/

example (a b : Nat) : a + b = b + a := natAddComm a b
example (a b c : Nat) : a + b + c = a + (b + c) := natAddAssoc a b c
example (a b c : Nat) : a + b + c = a + c + b := natAddRightComm a b c
example (a b : Nat) : a * b = b * a := natMulComm a b
example (a b c : Nat) : a * b * c = a * (b * c) := natMulAssoc a b c
example (a b c : Nat) : a * (b + c) = a * b + a * c := natLeftDistrib a b c
example (a b c : Nat) : (a + b) * c = a * c + b * c := natRightDistrib a b c
example (a : Nat) : a ≤ a := natLeRefl a
example {a b c : Nat} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := natLeTrans a b c h₁ h₂
example (a b : Nat) : a ≤ a + b := natLeAddRight a b
example {m n : Nat} (h : m ≤ n) (k : Nat) : k + m ≤ k + n := natAddLeAddLeft k m n h
example {m n : Nat} (h : m ≤ n) (k : Nat) : m + k ≤ n + k := natAddLeAddRight k m n h
example {k m n : Nat} (h : m + k ≤ n + k) : m ≤ n := natLeOfAddLeAddRight k m n h

/-! ## 3. The count, read from the environment

Thirteen rows. Derived, not written down: a shim theorem that disappears takes
this number with it, and the gate's floor then fails. -/

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let mut rows := 0
  for (name, info) in env.constants.toList do
    if name.getPrefix == `Axeyum.Shim && !name.isInternal then
      match info with
      | .thmInfo _ => rows := rows + 1
      | _ => pure ()
  Lean.logInfo s!"AXEYUM-TACTIC-SHIM-ROWS rows={rows}"

end Tests.ShimCorrespondence
