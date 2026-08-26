import Mathlib.Data.Nat.ModEq

/-!
Proof-free statement adapters for the first arithmetic `Nat.ModEq` sibling
family. The candidate export roots are selected separately; none of these
definitions contains a proof of the corresponding Mathlib theorem.
-/

namespace Axeyum.Autogenesis.Statement.NatModEqArithmetic

def addLeft : Prop :=
  ∀ {n a : ℕ}, n + a ≡ a [MOD n]

def addRight : Prop :=
  ∀ {n a : ℕ}, a + n ≡ a [MOD n]

def modulusZero : Prop :=
  ∀ {n : ℕ}, n ≡ 0 [MOD n]

end Axeyum.Autogenesis.Statement.NatModEqArithmetic
