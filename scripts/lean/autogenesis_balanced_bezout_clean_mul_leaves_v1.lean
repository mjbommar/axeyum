import Mathlib.Data.Int.GCD

namespace Axeyum.Autogenesis

private theorem swapMiddleFourV1 (x y z w : Nat) :
    (x + y) + (z + w) = (x + z) + (y + w) := by
  calc
    (x + y) + (z + w) = ((x + y) + z) + w :=
      (Nat.add_assoc (x + y) z w).symm
    _ = ((x + z) + y) + w :=
      congrArg (fun value => value + w) (Nat.add_right_comm x y z)
    _ = (x + z) + (y + w) := Nat.add_assoc (x + z) y w

theorem balancedBezoutMulAssocLeafV1 (a b c : Nat) :
    a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
      change a * b * c + a * b = a * (b * c + b)
      exact (congrArg (fun value => value + a * b) ih).trans
        (Nat.left_distrib a (b * c) b).symm

theorem balancedBezoutRightDistribLeafV1 (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rfl
  | succ c ih =>
      change (a + b) * c + (a + b) =
        (a * c + a) + (b * c + b)
      exact (congrArg (fun value => value + (a + b)) ih).trans
        (swapMiddleFourV1 (a * c) (b * c) a b)

end Axeyum.Autogenesis
