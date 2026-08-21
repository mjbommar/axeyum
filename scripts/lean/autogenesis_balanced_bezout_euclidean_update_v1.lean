import Mathlib.Data.Int.GCD

namespace Axeyum.Autogenesis

def BalancedBezoutUpdateV1 (m n g : Nat) : Prop :=
  ∃ mp mn np nn : Nat,
    g + m * mn + n * nn = m * mp + n * np

private theorem rotateLastFiveV1 (a b c d e : Nat) :
    (((a + b) + c) + d) + e = (((a + e) + b) + c) + d := by
  calc
    (((a + b) + c) + d) + e = (((a + b) + c) + e) + d :=
      Nat.add_right_comm ((a + b) + c) d e
    _ = (((a + b) + e) + c) + d :=
      congrArg (fun value => value + d) (Nat.add_right_comm (a + b) c e)
    _ = (((a + e) + b) + c) + d :=
      congrArg (fun value => (value + c) + d) (Nat.add_right_comm a b e)

private theorem rotateFourthThenSwapV1 (a b c d : Nat) :
    ((a + b) + c) + d = ((d + a) + c) + b := by
  calc
    ((a + b) + c) + d = ((a + b) + d) + c :=
      Nat.add_right_comm (a + b) c d
    _ = ((a + d) + b) + c :=
      congrArg (fun value => value + c) (Nat.add_right_comm a b d)
    _ = ((d + a) + b) + c :=
      congrArg (fun value => (value + b) + c) (Nat.add_comm a d)
    _ = ((d + a) + c) + b :=
      Nat.add_right_comm (d + a) b c

theorem balancedBezoutEuclideanUpdateV1
    (divisor dividend remainder quotient common : Nat)
    (divisionEquation : divisor * quotient + remainder = dividend)
    (recursive : BalancedBezoutUpdateV1 remainder divisor common) :
    BalancedBezoutUpdateV1 divisor dividend common := by
  rcases recursive with ⟨mp, mn, np, nn, recursiveEquation⟩
  let dq := divisor * quotient
  let dnn := divisor * nn
  let dqmp := dq * mp
  let dqmn := dq * mn
  let rmp := remainder * mp
  let rmn := remainder * mn
  let dnp := divisor * np
  have divisorQMp : divisor * (quotient * mp) = dqmp := by
    exact (Nat.mul_assoc divisor quotient mp).symm
  have divisorQMn : divisor * (quotient * mn) = dqmn := by
    exact (Nat.mul_assoc divisor quotient mn).symm
  have dividendMp : dividend * mp = dqmp + rmp := by
    exact (congrArg (fun value => value * mp) divisionEquation.symm).trans
      (Nat.right_distrib dq remainder mp)
  have dividendMn : dividend * mn = dqmn + rmn := by
    exact (congrArg (fun value => value * mn) divisionEquation.symm).trans
      (Nat.right_distrib dq remainder mn)
  have recursiveLifted :
      (((common + rmn) + dnn) + dqmp) + dqmn =
        (((rmp + dnp) + dqmp) + dqmn) := by
    exact congrArg (fun value => value + dqmn)
      (congrArg (fun value => value + dqmp) recursiveEquation)
  refine ⟨np + quotient * mn, nn + quotient * mp, mp, mn, ?_⟩
  calc
    common + divisor * (nn + quotient * mp) + dividend * mn =
        common + (dnn + divisor * (quotient * mp)) + dividend * mn :=
      congrArg (fun value => common + value + dividend * mn)
        (Nat.left_distrib divisor nn (quotient * mp))
    _ = common + (dnn + dqmp) + dividend * mn :=
      congrArg (fun value => common + (dnn + value) + dividend * mn) divisorQMp
    _ = (common + dnn) + dqmp + dividend * mn :=
      congrArg (fun value => value + dividend * mn)
        (Nat.add_assoc common dnn dqmp).symm
    _ = (common + dnn) + dqmp + (dqmn + rmn) :=
      congrArg (fun value => (common + dnn) + dqmp + value) dividendMn
    _ = (((common + dnn) + dqmp) + dqmn) + rmn :=
      (Nat.add_assoc ((common + dnn) + dqmp) dqmn rmn).symm
    _ = (((common + rmn) + dnn) + dqmp) + dqmn :=
      rotateLastFiveV1 common dnn dqmp dqmn rmn
    _ = (((rmp + dnp) + dqmp) + dqmn) := recursiveLifted
    _ = ((dnp + dqmn) + dqmp) + rmp :=
      (rotateFourthThenSwapV1 dnp dqmn dqmp rmp).symm
    _ = (dnp + dqmn) + (dqmp + rmp) :=
      Nat.add_assoc (dnp + dqmn) dqmp rmp
    _ = (dnp + dqmn) + dividend * mp :=
      congrArg (fun value => (dnp + dqmn) + value) dividendMp.symm
    _ = (dnp + divisor * (quotient * mn)) + dividend * mp :=
      congrArg (fun value => (dnp + value) + dividend * mp) divisorQMn.symm
    _ = divisor * (np + quotient * mn) + dividend * mp :=
      congrArg (fun value => value + dividend * mp)
        (Nat.left_distrib divisor np (quotient * mn)).symm

end Axeyum.Autogenesis
