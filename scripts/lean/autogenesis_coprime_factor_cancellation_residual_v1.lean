import Mathlib.Data.Int.GCD

namespace Axeyum.Autogenesis

def BalancedBezoutCancellationResidualV1 (a c g : Nat) : Prop :=
  ∃ mp mn np nn : Nat,
    g + a * mn + c * nn = a * mp + c * np

theorem dvdMulRightWitnessV1 (d x y : Nat) (divides : d ∣ x) :
    d ∣ x * y := by
  rcases divides with ⟨factor, equation⟩
  refine ⟨factor * y, ?_⟩
  exact
    (congrArg (fun value => value * y) equation).trans
      (Nat.mul_assoc d factor y)

theorem dvdAddWitnessV1 (d x y : Nat)
    (dividesX : d ∣ x) (dividesY : d ∣ y) :
    d ∣ x + y := by
  rcases dividesX with ⟨leftFactor, leftEquation⟩
  rcases dividesY with ⟨rightFactor, rightEquation⟩
  refine ⟨leftFactor + rightFactor, ?_⟩
  calc
    x + y = d * leftFactor + y :=
      congrArg (fun value => value + y) leftEquation
    _ = d * leftFactor + d * rightFactor :=
      congrArg (fun value => d * leftFactor + value) rightEquation
    _ = d * (leftFactor + rightFactor) :=
      (Nat.left_distrib d leftFactor rightFactor).symm

theorem coprimeFactorDivisibilityCancellationResidualV1
    (balancedBezout : ∀ a c : Nat,
      BalancedBezoutCancellationResidualV1 a c (Nat.gcd a c))
    (rightDistrib : ∀ x y z : Nat, (x + y) * z = x * z + y * z)
    (dvdAddCancel : ∀ d excess b : Nat,
      d ∣ excess → d ∣ excess + b → d ∣ b)
    (a c b d : Nat)
    (coprime : Nat.gcd a c = 1)
    (dividesA : d ∣ a)
    (dividesProduct : d ∣ c * b) :
    d ∣ b := by
  have certificate : BalancedBezoutCancellationResidualV1 a c 1 :=
    Eq.mp
      (congrArg (BalancedBezoutCancellationResidualV1 a c) coprime)
      (balancedBezout a c)
  rcases certificate with ⟨mp, mn, np, nn, equation⟩
  have dividesAMnB : d ∣ (a * mn) * b :=
    dvdMulRightWitnessV1 d (a * mn) b
      (dvdMulRightWitnessV1 d a mn dividesA)
  have dividesAMPB : d ∣ (a * mp) * b :=
    dvdMulRightWitnessV1 d (a * mp) b
      (dvdMulRightWitnessV1 d a mp dividesA)
  have dividesCNNB : d ∣ (c * nn) * b := by
    have base : d ∣ (c * b) * nn :=
      dvdMulRightWitnessV1 d (c * b) nn dividesProduct
    have rearranged : (c * b) * nn = (c * nn) * b := by
      calc
        (c * b) * nn = c * (b * nn) := Nat.mul_assoc c b nn
        _ = c * (nn * b) :=
          congrArg (fun value => c * value) (Nat.mul_comm b nn)
        _ = (c * nn) * b := (Nat.mul_assoc c nn b).symm
    exact Eq.mp (congrArg (fun value => d ∣ value) rearranged) base
  have dividesCNPB : d ∣ (c * np) * b := by
    have base : d ∣ (c * b) * np :=
      dvdMulRightWitnessV1 d (c * b) np dividesProduct
    have rearranged : (c * b) * np = (c * np) * b := by
      calc
        (c * b) * np = c * (b * np) := Nat.mul_assoc c b np
        _ = c * (np * b) :=
          congrArg (fun value => c * value) (Nat.mul_comm b np)
        _ = (c * np) * b := (Nat.mul_assoc c np b).symm
    exact Eq.mp (congrArg (fun value => d ∣ value) rearranged) base
  let excess := (a * mn) * b + (c * nn) * b
  have dividesExcess : d ∣ excess :=
    dvdAddWitnessV1 d ((a * mn) * b) ((c * nn) * b)
      dividesAMnB dividesCNNB
  have dividesRight : d ∣ ((a * mp) * b + (c * np) * b) :=
    dvdAddWitnessV1 d ((a * mp) * b) ((c * np) * b)
      dividesAMPB dividesCNPB
  have scaledEquation :
      b + excess = (a * mp) * b + (c * np) * b := by
    calc
      b + excess = (b + (a * mn) * b) + (c * nn) * b :=
        (Nat.add_assoc b ((a * mn) * b) ((c * nn) * b)).symm
      _ = (1 * b + (a * mn) * b) + (c * nn) * b :=
        congrArg
          (fun value => (value + (a * mn) * b) + (c * nn) * b)
          (Nat.one_mul b).symm
      _ = ((1 + a * mn) * b) + (c * nn) * b :=
        congrArg
          (fun value => value + (c * nn) * b)
          (rightDistrib 1 (a * mn) b).symm
      _ = ((1 + a * mn) + c * nn) * b :=
        (rightDistrib (1 + a * mn) (c * nn) b).symm
      _ = (a * mp + c * np) * b :=
        congrArg (fun value => value * b) equation
      _ = (a * mp) * b + (c * np) * b :=
        rightDistrib (a * mp) (c * np) b
  have dividesBPlusExcess : d ∣ b + excess :=
    Eq.mp
      (congrArg (fun value => d ∣ value) scaledEquation).symm
      dividesRight
  have dividesExcessPlusB : d ∣ excess + b :=
    Eq.mp
      (congrArg (fun value => d ∣ value) (Nat.add_comm b excess))
      dividesBPlusExcess
  exact dvdAddCancel d excess b dividesExcess dividesExcessPlusB

end Axeyum.Autogenesis
