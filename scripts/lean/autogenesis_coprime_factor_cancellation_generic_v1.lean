import AxeyumAutogenesisBalancedBezoutEuclideanUpdateV2

namespace Axeyum.Autogenesis

theorem coprimeFactorDivisibilityCancellationGenericV1
    (balancedBezout : ∀ a c : Nat,
      BalancedBezoutUpdateV2 a c (Nat.gcd a c))
    (a c b d : Nat)
    (coprime : Nat.gcd a c = 1)
    (dividesA : d ∣ a)
    (dividesProduct : d ∣ c * b) :
    d ∣ b := by
  have certificate : BalancedBezoutUpdateV2 a c 1 :=
    Eq.mp
      (congrArg (BalancedBezoutUpdateV2 a c) coprime)
      (balancedBezout a c)
  rcases certificate with ⟨mp, mn, np, nn, equation⟩
  have dividesAMnB : d ∣ (a * mn) * b :=
    Nat.dvd_mul_right_of_dvd
      (Nat.dvd_mul_right_of_dvd dividesA mn) b
  have dividesAMPB : d ∣ (a * mp) * b :=
    Nat.dvd_mul_right_of_dvd
      (Nat.dvd_mul_right_of_dvd dividesA mp) b
  have dividesCNNB : d ∣ (c * nn) * b := by
    have base : d ∣ (c * b) * nn :=
      Nat.dvd_mul_right_of_dvd dividesProduct nn
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using base
  have dividesCNPB : d ∣ (c * np) * b := by
    have base : d ∣ (c * b) * np :=
      Nat.dvd_mul_right_of_dvd dividesProduct np
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using base
  let excess := (a * mn) * b + (c * nn) * b
  have dividesExcess : d ∣ excess :=
    Nat.dvd_add dividesAMnB dividesCNNB
  have dividesRight : d ∣ ((a * mp) * b + (c * np) * b) :=
    Nat.dvd_add dividesAMPB dividesCNPB
  have scaledEquation :
      b + excess = (a * mp) * b + (c * np) * b := by
    calc
      b + excess = ((1 + a * mn) + c * nn) * b := by
        simp only [excess, Nat.right_distrib, Nat.one_mul, Nat.add_assoc]
      _ = (a * mp + c * np) * b :=
        congrArg (fun value => value * b) equation
      _ = (a * mp) * b + (c * np) * b :=
        Nat.right_distrib (a * mp) (c * np) b
  have dividesBPlusExcess : d ∣ b + excess :=
    Eq.mp
      (congrArg (fun value => d ∣ value) scaledEquation).symm
      dividesRight
  have dividesExcessPlusB : d ∣ excess + b :=
    Eq.mp
      (congrArg (fun value => d ∣ value) (Nat.add_comm b excess))
      dividesBPlusExcess
  exact (Nat.dvd_add_iff_right dividesExcess).mpr dividesExcessPlusB

end Axeyum.Autogenesis
