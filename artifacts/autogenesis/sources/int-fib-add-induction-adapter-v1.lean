import Mathlib.Data.Int.Fib.Basic

namespace Axeyum.Autogenesis

theorem intSuccPredInductionResidualV1
    (P : Int → Prop)
    (succ pred : Int → Int)
    (split : ∀ z : Int, (∃ n : Nat, z = Int.ofNat n) ∨ ∃ n : Nat, z = Int.negSucc n)
    (ofNat_zero : Int.ofNat 0 = 0)
    (ofNat_succ : ∀ n : Nat, Int.ofNat (n + 1) = succ (Int.ofNat n))
    (negSucc_zero : Int.negSucc 0 = pred 0)
    (negSucc_succ : ∀ n : Nat, Int.negSucc (n + 1) = pred (Int.negSucc n))
    (base : P 0)
    (forward : ∀ n : Int, P n → P (succ n))
    (backward : ∀ n : Int, P n → P (pred n)) :
    ∀ n : Int, P n := by
  have positive : ∀ n : Nat, P (Int.ofNat n) := by
    intro n
    induction n with
    | zero => exact ofNat_zero.symm ▸ base
    | succ n ih => exact (ofNat_succ n).symm ▸ forward (Int.ofNat n) ih
  have negative : ∀ n : Nat, P (Int.negSucc n) := by
    intro n
    induction n with
    | zero => exact negSucc_zero.symm ▸ backward 0 base
    | succ n ih => exact (negSucc_succ n).symm ▸ backward (Int.negSucc n) ih
  intro n
  exact Or.elim (split n)
    (fun h => Exists.elim h fun k hk => hk.symm ▸ positive k)
    (fun h => Exists.elim h fun k hk => hk.symm ▸ negative k)

end Axeyum.Autogenesis
