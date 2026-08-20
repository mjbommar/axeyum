import Mathlib.Data.Nat.Fib.Basic

namespace Axeyum.Autogenesis

private theorem iterateSuccApplyPointwise
    {α : Type} (f : α → α) (n : Nat) (x : α) :
    f^[Nat.succ n] x = f (f^[n] x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      change f^[Nat.succ n] (f x) = f (f^[n] (f x))
      exact ih (f x)

theorem fibAddTwo (n : Nat) :
    Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := by
  unfold Nat.fib
  rw [iterateSuccApplyPointwise, iterateSuccApplyPointwise]

#print axioms Axeyum.Autogenesis.iterateSuccApplyPointwise
#print axioms Axeyum.Autogenesis.fibAddTwo

end Axeyum.Autogenesis
