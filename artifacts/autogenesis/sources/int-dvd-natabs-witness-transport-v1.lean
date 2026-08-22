import Init.Data.Int.DivMod.Lemmas

namespace Axeyum.Autogenesis

theorem intNatAbsDvdForwardResidualV1
    (natAbsMul : ∀ a b : Int,
      (a * b).natAbs = a.natAbs * b.natAbs)
    (a b : Int) : a ∣ b → a.natAbs ∣ b.natAbs := by
  rintro ⟨c, rfl⟩
  exact ⟨c.natAbs, natAbsMul a c⟩

theorem intDvdOfNatAbsDvdDirectV1 (a b : Int) :
    a.natAbs ∣ b.natAbs → a ∣ b := by
  rintro ⟨k, hk⟩
  cases a with
  | ofNat a =>
      cases b with
      | ofNat b =>
          exact ⟨Int.ofNat k, congrArg Int.ofNat hk⟩
      | negSucc b =>
          cases k with
          | zero => cases hk
          | succ k =>
              exact ⟨Int.negSucc k, congrArg Int.negOfNat hk⟩
  | negSucc a =>
      cases b with
      | ofNat b =>
          cases k with
          | zero =>
              exact ⟨Int.ofNat 0, congrArg Int.ofNat hk⟩
          | succ k =>
              exact ⟨Int.negSucc k, congrArg Int.ofNat hk⟩
      | negSucc b =>
          exact ⟨Int.ofNat k, congrArg Int.negOfNat hk⟩

end Axeyum.Autogenesis
