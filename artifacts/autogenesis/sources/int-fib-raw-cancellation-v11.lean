import Mathlib.Data.Int.Basic

namespace Axeyum.IntFib

theorem evenAdd (a b : Nat) :
    -(Int.ofNat a) =
      -(Int.ofNat a + (Int.ofNat b + Int.ofNat a)) +
        (Int.ofNat b + Int.ofNat a) := by
  have addSub : ∀ x z : Nat, (x + z) - z = x := by
    intro x z
    induction z with
    | zero => exact Nat.sub_zero x
    | succ z ih =>
        exact
          (congrArg (fun q => q - Nat.succ z) (Nat.add_succ x z)).trans
            ((Nat.succ_sub_succ_eq_sub (x + z) z).trans ih)
  have cancel : ∀ x z : Nat,
      -(Int.ofNat x + Int.ofNat z) + Int.ofNat z = -(Int.ofNat x) := by
    intro x z
    cases x with
    | zero =>
        cases z with
        | zero => rfl
        | succ z =>
            dsimp only [Add.add, HAdd.hAdd, Neg.neg, OfNat.ofNat, Int.add, Int.neg,
              Int.negOfNat]
            have hz : Nat.add 0 z = z := Nat.zero_add z
            have hs : Nat.succ (Nat.add 0 z) = Nat.succ z := congrArg Nat.succ hz
            rw [hs]
            change Int.subNatNat (z + 1) (z + 1) = Int.ofNat 0
            have hzero : (z + 1) - (z + 1) = 0 := Nat.sub_self (z + 1)
            exact
              (Int.subNatNat_of_sub_eq_zero hzero).trans
                (congrArg Int.ofNat hzero)
    | succ x =>
        cases z with
        | zero =>
            dsimp only [Add.add, HAdd.hAdd, Neg.neg, Int.add, Int.neg, Int.negOfNat]
            change Int.subNatNat 0 (x + 1) = Int.negSucc x
            have hsucc : (x + 1) - 0 = x + 1 := Nat.sub_zero (x + 1)
            exact Int.subNatNat_of_sub_eq_succ hsucc
        | succ z =>
            dsimp only [Add.add, HAdd.hAdd, Neg.neg, Int.add, Int.neg, Int.negOfNat]
            change Int.subNatNat (z + 1) ((x + 1) + (z + 1)) = Int.negSucc x
            exact Int.subNatNat_of_sub_eq_succ (addSub (x + 1) (z + 1))
  exact (cancel a (b + a)).symm

theorem oddAdd (a b : Nat) :
    Int.ofNat a =
      Int.ofNat a + (Int.ofNat b + Int.ofNat a) +
        -(Int.ofNat b + Int.ofNat a) := by
  have addSub : ∀ x z : Nat, (x + z) - z = x := by
    intro x z
    induction z with
    | zero => exact Nat.sub_zero x
    | succ z ih =>
        exact
          (congrArg (fun q => q - Nat.succ z) (Nat.add_succ x z)).trans
            ((Nat.succ_sub_succ_eq_sub (x + z) z).trans ih)
  have subAdd : ∀ x z : Nat, z - (x + z) = 0 := by
    intro x z
    induction z with
    | zero =>
        exact
          (congrArg (fun q => 0 - q) (Nat.add_zero x)).trans
            (Nat.zero_sub x)
    | succ z ih =>
        exact
          (congrArg (fun q => Nat.succ z - q) (Nat.add_succ x z)).trans
            ((Nat.succ_sub_succ_eq_sub z (x + z)).trans ih)
  have cancel : ∀ x z : Nat,
      Int.ofNat x + Int.ofNat z + -(Int.ofNat z) = Int.ofNat x := by
    intro x z
    cases z with
    | zero => rfl
    | succ z =>
        dsimp only [Add.add, HAdd.hAdd, Neg.neg, Int.add, Int.neg, Int.negOfNat]
        change Int.subNatNat (x + (z + 1)) (z + 1) = Int.ofNat x
        exact
          (Int.subNatNat_of_sub_eq_zero (subAdd x (z + 1))).trans
            (congrArg Int.ofNat (addSub x (z + 1)))
  exact (cancel a (b + a)).symm

end Axeyum.IntFib
