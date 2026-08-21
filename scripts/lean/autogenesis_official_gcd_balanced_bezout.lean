import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import autogenesis_div_mod_go_reconstruct_v2

namespace Axeyum.Autogenesis

/-- A signed integer linear combination encoded by positive and negative
natural parts.  Keeping all four witnesses in `Nat` avoids importing an
integer carrier merely to state Bezout's identity. -/
def BalancedBezout (m n g : Nat) : Prop :=
  ∃ mp mn np nn : Nat,
    g + m * mn + n * nn = m * mp + n * np

/-- The private joint quotient/remainder invariant supplies exactly the
existential quotient required by the Euclidean Bezout update.  This theorem
does not mention the opaque public quotient wrapper. -/
theorem modQuotientWitness (m n : Nat) (hm : 0 < m) :
    ∃ q : Nat, m * q + n % m = n := by
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

/-- A proof-isolated balanced Bezout theorem over the official `Nat.gcd`
surface.  The two gcd equations are explicit parameters so the checked target
specialization can supply Axeyum's independently reconstructed, empty-footprint
versions instead of transporting Mathlib's assumption-bearing proofs. -/
theorem officialGcdBalancedBezout
    (gcdZeroLeft : ∀ n : Nat, Nat.gcd 0 n = n)
    (gcdSucc : ∀ m n : Nat,
      Nat.gcd (Nat.succ m) n = Nat.gcd (n % Nat.succ m) (Nat.succ m))
    (m n : Nat) : BalancedBezout m n (Nat.gcd m n) := by
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
        rcases modQuotientWitness (Nat.succ m) n (Nat.zero_lt_succ m) with
          ⟨q, hq⟩
        rcases ih with ⟨mp, mn, np, nn, hbezout⟩
        refine ⟨np + q * mn, nn + q * mp, mp, mn, ?_⟩
        rw [← hq]
        calc
          Nat.gcd (n % Nat.succ m) (Nat.succ m) +
                Nat.succ m * (nn + q * mp) +
                (Nat.succ m * q + n % Nat.succ m) * mn =
              (Nat.gcd (n % Nat.succ m) (Nat.succ m) +
                (n % Nat.succ m) * mn + Nat.succ m * nn) +
                Nat.succ m * (q * mp) + Nat.succ m * (q * mn) := by
                  ring
          _ = ((n % Nat.succ m) * mp + Nat.succ m * np) +
                Nat.succ m * (q * mp) + Nat.succ m * (q * mn) := by
                  rw [hbezout]
          _ = Nat.succ m * (np + q * mn) +
                (Nat.succ m * q + n % Nat.succ m) * mp := by
                  ring

end Axeyum.Autogenesis
