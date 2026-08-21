import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import autogenesis_div_mod_go_reconstruct_v2

namespace Axeyum.Autogenesis

/-- A signed integer linear combination encoded by positive and negative
natural parts. -/
def OfficialBalancedBezout (m n g : Nat) : Prop :=
  ∃ mp mn np nn : Nat,
    g + m * mn + n * nn = m * mp + n * np

/-- A quotient witness derived without crossing the opaque public quotient
wrapper.  Direct `Nat.mod` syntax deliberately matches the audited computation
equations. -/
theorem modQuotientWitnessV2 (m n : Nat) (hm : 0 < m) :
    ∃ q : Nat, m * q + Nat.mod n m = n := by
  cases n with
  | zero =>
      refine ⟨0, ?_⟩
      rw [Nat.mod.eq_1, Nat.mul_zero, Nat.zero_add]
  | succ n =>
      rw [Nat.mod.eq_2]
      split
      next _ =>
        let hfuel : Nat.succ n < Nat.succ (Nat.succ n) :=
          Nat.lt_succ_self (Nat.succ n)
        let q := Nat.div.go m hm (Nat.succ (Nat.succ n)) (Nat.succ n) hfuel
        refine ⟨q, ?_⟩
        unfold Nat.modCore
        exact divModGoReconstruct
          m hm (Nat.succ (Nat.succ n)) (Nat.succ n) hfuel
      next _ =>
        refine ⟨0, ?_⟩
        rw [Nat.mul_zero, Nat.zero_add]

/-- Balanced Bezout over official `Nat.gcd`, generic in the two gcd equations
that the checked target will later specialize with empty-footprint leaves. -/
theorem officialGcdBalancedBezoutV2
    (gcdZeroLeft : ∀ n : Nat, Nat.gcd 0 n = n)
    (gcdSucc : ∀ m n : Nat,
      Nat.gcd (Nat.succ m) n = Nat.gcd (Nat.mod n (Nat.succ m)) (Nat.succ m))
    (m n : Nat) : OfficialBalancedBezout m n (Nat.gcd m n) := by
  refine Nat.gcd.induction m n ?_ ?_
  · intro n
    rw [gcdZeroLeft]
    refine ⟨0, 0, 1, 0, ?_⟩
    rw [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one]
  · intro m n hm ih
    cases m with
    | zero => exact (Nat.not_lt_zero 0 hm).elim
    | succ m =>
        rw [gcdSucc m n]
        rcases modQuotientWitnessV2 (Nat.succ m) n (Nat.zero_lt_succ m) with
          ⟨q, hq⟩
        rcases ih with ⟨mp, mn, np, nn, hbezout⟩
        have hqMn := congrArg (fun value => value * mn) hq
        have hqMp := congrArg (fun value => value * mp) hq
        refine ⟨np + q * mn, nn + q * mp, mp, mn, ?_⟩
        calc
          Nat.gcd (Nat.mod n (Nat.succ m)) (Nat.succ m) +
                Nat.succ m * (nn + q * mp) + n * mn =
              Nat.gcd (Nat.mod n (Nat.succ m)) (Nat.succ m) +
                Nat.succ m * (nn + q * mp) +
                (Nat.succ m * q + Nat.mod n (Nat.succ m)) * mn := by
                  rw [hqMn]
          _ = (Nat.gcd (Nat.mod n (Nat.succ m)) (Nat.succ m) +
                Nat.mod n (Nat.succ m) * mn + Nat.succ m * nn) +
                Nat.succ m * (q * mp) + Nat.succ m * (q * mn) := by
                  ring
          _ = (Nat.mod n (Nat.succ m) * mp + Nat.succ m * np) +
                Nat.succ m * (q * mp) + Nat.succ m * (q * mn) := by
                  rw [hbezout]
          _ = Nat.succ m * (np + q * mn) +
                (Nat.succ m * q + Nat.mod n (Nat.succ m)) * mp := by
                  ring
          _ = Nat.succ m * (np + q * mn) + n * mp := by
                  rw [hqMp]

end Axeyum.Autogenesis
