import Mathlib.Data.Nat.Fib.Basic

namespace Int

@[pp_nodot]
def fib : Int → Int
  | ofNat n => ofNat (Nat.fib n)
  | negSucc k =>
      let n := k + 1
      if n % 2 = 0 then -ofNat (Nat.fib n) else ofNat (Nat.fib n)

theorem fib_add_two_residual
    (natRec : ∀ n : Nat, Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1))
    (modCases : ∀ n : Nat, n % 2 = 0 ∨ n % 2 = 1)
    (succOne : ∀ {n : Nat}, n % 2 = 0 → (n + 1) % 2 = 1)
    (succZero : ∀ {n : Nat}, n % 2 = 1 → (n + 1) % 2 = 0)
    (castAdd : ∀ a b : Nat, (Int.ofNat (a + b)) = (Int.ofNat a) + (Int.ofNat b))
    (evenAdd : ∀ a b : Nat,
      -(Int.ofNat a) =
        -(Int.ofNat a + (Int.ofNat b + Int.ofNat a)) +
          (Int.ofNat b + Int.ofNat a))
    (oddAdd : ∀ a b : Nat,
      Int.ofNat a =
        Int.ofNat a + (Int.ofNat b + Int.ofNat a) +
          -(Int.ofNat b + Int.ofNat a)) :
    ∀ n : Int, fib (n + 2) = fib n + fib (n + 1)
  | ofNat n => by
      change Int.ofNat (Nat.fib (n + 2)) =
        Int.ofNat (Nat.fib n) + Int.ofNat (Nat.fib (n + 1))
      rw [natRec]
      exact castAdd _ _
  | negSucc k => by
      cases k with
      | zero => rfl
      | succ k =>
          cases k with
          | zero => rfl
          | succ k =>
              change
                fib (negSucc k) =
                  fib (negSucc (k + 2)) + fib (negSucc (k + 1))
              rcases modCases (k + 1) with h | h
              · have h₁ : (k + 2) % 2 = 1 := succOne h
                have h₂ : (k + 3) % 2 = 0 := succZero h₁
                have h₁ne : (k + 2) % 2 ≠ 0 := by
                  intro hz
                  cases h₁.symm.trans hz
                change
                  (if (k + 1) % 2 = 0 then -ofNat (Nat.fib (k + 1)) else ofNat (Nat.fib (k + 1))) =
                    (if (k + 3) % 2 = 0 then -ofNat (Nat.fib (k + 3)) else ofNat (Nat.fib (k + 3))) +
                      (if (k + 2) % 2 = 0 then -ofNat (Nat.fib (k + 2)) else ofNat (Nat.fib (k + 2)))
                rw [if_pos h, if_pos h₂, if_neg h₁ne]
                rw [natRec (k + 1), natRec k]
                rw [castAdd, castAdd]
                exact evenAdd _ _
              · have h₁ : (k + 2) % 2 = 0 := succZero h
                have h₂ : (k + 3) % 2 = 1 := succOne h₁
                have hne : (k + 1) % 2 ≠ 0 := by
                  intro hz
                  cases h.symm.trans hz
                have h₂ne : (k + 3) % 2 ≠ 0 := by
                  intro hz
                  cases h₂.symm.trans hz
                change
                  (if (k + 1) % 2 = 0 then -ofNat (Nat.fib (k + 1)) else ofNat (Nat.fib (k + 1))) =
                    (if (k + 3) % 2 = 0 then -ofNat (Nat.fib (k + 3)) else ofNat (Nat.fib (k + 3))) +
                      (if (k + 2) % 2 = 0 then -ofNat (Nat.fib (k + 2)) else ofNat (Nat.fib (k + 2)))
                rw [if_neg hne, if_neg h₂ne, if_pos h₁]
                rw [natRec (k + 1), natRec k]
                rw [castAdd, castAdd]
                exact oddAdd _ _

end Int
