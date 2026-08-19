import Mathlib.Data.Nat.Factorial.Basic

/-!
Proof-free statement adapters for the frozen natural-factorial zero family.

Each proposition is the value of a transparent `Prop` definition.  This file
contains no axiom, theorem, opaque declaration, or proof value.  Authoritative
operations still bind one exact fact, target, export stream, and checked result;
sharing this source establishes only the adapter-family boundary.
-/

namespace Axeyum.Autogenesis.Statement.FactorialZero

def natAscFactorialZero : Prop :=
  ∀ (n : ℕ), n.ascFactorial 0 = 1

def natDescFactorialZero : Prop :=
  ∀ (n : ℕ), n.descFactorial 0 = 1

end Axeyum.Autogenesis.Statement.FactorialZero
