import Mathlib.Data.Nat.Factorial.Basic

/-!
A proof-free adapter probe for the frozen train fact
`F:ml430-nat-ascfactorial-zero-fd183202`.

The proposition is the value of a transparent `Prop` definition. It is not an
axiom, theorem, or opaque declaration, so exporting this declaration cannot
make the proposition available as a proof assumption.
-/

namespace Axeyum.Autogenesis.Statement

def natAscFactorialZero : Prop :=
  ∀ (n : ℕ), n.ascFactorial 0 = 1

end Axeyum.Autogenesis.Statement
