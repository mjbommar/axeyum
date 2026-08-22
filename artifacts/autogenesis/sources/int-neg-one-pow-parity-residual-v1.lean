import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intNegOnePowParityResidualV1
    (powFn : Nat → Int)
    (powZero : powFn 0 = 1)
    (powSucc : ∀ n : Nat, powFn (n + 1) = powFn n * (-1))
    (negMulNeg : (-1 : Int) * (-1) = 1)
    (oneMulNeg : (1 : Int) * (-1) = -1)
    (modCases : ∀ n : Nat, n % 2 = 0 ∨ n % 2 = 1)
    (succOne : ∀ {n : Nat}, n % 2 = 0 → (n + 1) % 2 = 1)
    (succZero : ∀ {n : Nat}, n % 2 = 1 → (n + 1) % 2 = 0) :
    ∀ n : Nat, powFn (n + 1) = if n % 2 = 0 then -1 else 1
  | 0 =>
      (powSucc 0).trans
        ((congrArg (fun value : Int => value * (-1)) powZero).trans oneMulNeg) |>.trans
          (if_pos rfl).symm
  | n + 1 => by
      have ih := intNegOnePowParityResidualV1 powFn powZero powSucc negMulNeg oneMulNeg
        modCases succOne succZero n
      cases modCases n with
      | inl heven =>
          have hnext : (n + 1) % 2 = 1 := succOne heven
          have hnextNe : (n + 1) % 2 ≠ 0 := by
            intro hzero
            cases hnext.symm.trans hzero
          exact
            (powSucc (n + 1)).trans
              ((congrArg (fun value : Int => value * (-1)) (ih.trans (if_pos heven))).trans
                negMulNeg) |>.trans
                  (if_neg hnextNe).symm
      | inr hodd =>
          have hne : n % 2 ≠ 0 := by
            intro hzero
            cases hodd.symm.trans hzero
          have hnext : (n + 1) % 2 = 0 := succZero hodd
          exact
            (powSucc (n + 1)).trans
              ((congrArg (fun value : Int => value * (-1)) (ih.trans (if_neg hne))).trans
                oneMulNeg) |>.trans
                  (if_pos hnext).symm

end Axeyum.Autogenesis
