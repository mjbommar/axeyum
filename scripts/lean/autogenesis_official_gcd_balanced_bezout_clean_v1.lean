import AxeyumAutogenesisModQuotientWitnessV4
import AxeyumAutogenesisBalancedBezoutEuclideanUpdateClosedV1

namespace Axeyum.Autogenesis

theorem officialGcdBalancedBezoutCleanV1
    (gcdZeroLeft : ∀ n : Nat, Nat.gcd 0 n = n)
    (gcdSucc : ∀ m n : Nat,
      Nat.gcd (Nat.succ m) n = Nat.gcd (Nat.mod n (Nat.succ m)) (Nat.succ m))
    (m n : Nat) : BalancedBezoutUpdateV2 m n (Nat.gcd m n) := by
  refine Nat.gcd.induction m n ?_ ?_
  · intro n
    have base : BalancedBezoutUpdateV2 0 n n := by
      refine ⟨0, 0, 1, 0, ?_⟩
      exact ((Nat.zero_add (0 + n)).trans (Nat.zero_add n)).symm
    exact Eq.mp
      (congrArg (BalancedBezoutUpdateV2 0 n) (gcdZeroLeft n)).symm base
  · intro m n hm ih
    cases m with
    | zero => exact (Nat.not_lt_zero 0 hm).elim
    | succ m =>
        let divisor := Nat.succ m
        let remainder := Nat.mod n divisor
        rcases modQuotientWitnessV4 divisor n (Nat.zero_lt_succ m) with ⟨q, hq⟩
        have transformed :
            BalancedBezoutUpdateV2 divisor n (Nat.gcd remainder divisor) :=
          balancedBezoutEuclideanUpdateClosedV1
            divisor n remainder q (Nat.gcd remainder divisor) hq ih
        exact Eq.mp
          (congrArg (BalancedBezoutUpdateV2 divisor n) (gcdSucc m n)).symm
          transformed

end Axeyum.Autogenesis
