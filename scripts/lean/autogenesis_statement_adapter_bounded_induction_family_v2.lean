import Mathlib.Data.Nat.Factorial.Basic

/-!
Proof-free statement adapters extending the bounded-induction family to two
more members: `F:ml430-nat-zero-ascfactorial-af4fcdca`
(`Nat.zero_ascFactorial`) and `F:ml430-nat-one-ascfactorial-8bacb017`
(`Nat.one_ascFactorial`).

`bounded_induction_support` (`crates/axeyum-lean-import/examples/
bounded_induction_support/mod.rs`) is target-agnostic: `Eq.refl`, and where
that is stuck, a bounded structural induction over a discovered zero/succ
binder plus one congruence rewrite driven by the induction hypothesis. This
file adapts two more `natural-factorial` train propositions this producer
independently kernel-checks (`axioms = 0`).

Each proposition below is the value of a transparent `Prop` definition. This
file contains no axiom, theorem, opaque declaration, or proof value.
-/

namespace Axeyum.Autogenesis.Statement.BoundedInductionFamily

def natZeroAscFactorialSucc : Prop :=
  ∀ (k : ℕ), Nat.ascFactorial 0 k.succ = 0

def natOneAscFactorial : Prop :=
  ∀ (k : ℕ), Nat.ascFactorial 1 k = k.factorial

end Axeyum.Autogenesis.Statement.BoundedInductionFamily
