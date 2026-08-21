import Init.Data.Nat.Gcd

namespace Axeyum.Autogenesis

private abbrev GcdArgs := PSigma fun _ : Nat => Nat

private def gcdMeasure : GcdArgs → Nat
  | ⟨m, _⟩ => m

private def gcdStep
    (x : GcdArgs)
    (rec : ∀ y, InvImage (· < ·) gcdMeasure y x → Nat) : Nat :=
  match x with
  | ⟨m, n⟩ =>
      if h : m = 0 then
        n
      else
        rec ⟨n % m, m⟩ (by
          simpa [InvImage, gcdMeasure] using
            Nat.mod_lt n (Nat.zero_lt_of_ne_zero h))

private def gcdUnary : GcdArgs → Nat :=
  WellFounded.Nat.fix (motive := fun _ => Nat) gcdMeasure gcdStep

private def gcdModel (m n : Nat) : Nat := gcdUnary ⟨m, n⟩

theorem modLtSucc
    (mod_lt : ∀ x y : Nat, 0 < y → x % y < y) :
    ∀ n m : Nat, n % Nat.succ m < Nat.succ m :=
  fun n m => mod_lt n (Nat.succ m) (Nat.succ_pos m)

example (m n : Nat) : gcdModel m n = Nat.gcd m n := by
  delta gcdModel gcdUnary Nat.gcd Nat.gcd._unary
  rfl

private theorem gcdGo_succ
    (fuel : Nat)
    (x : GcdArgs)
    (h : gcdMeasure x < Nat.succ fuel) :
    WellFounded.Nat.fix.go gcdMeasure gcdStep (Nat.succ fuel) x h =
      gcdStep x (fun y hy =>
        WellFounded.Nat.fix.go gcdMeasure gcdStep fuel y
          (Nat.lt_of_lt_of_le hy (Nat.le_of_lt_add_one h))) := by
  rfl

private theorem gcdGo_congr
    (x : GcdArgs)
    (fuel₁ fuel₂ : Nat)
    (h₁ : gcdMeasure x < fuel₁)
    (h₂ : gcdMeasure x < fuel₂) :
    WellFounded.Nat.fix.go gcdMeasure gcdStep fuel₁ x h₁ =
      WellFounded.Nat.fix.go gcdMeasure gcdStep fuel₂ x h₂ := by
  induction fuel₁ generalizing x fuel₂ with
  | zero => exact (Nat.not_lt_zero _ h₁).elim
  | succ fuel₁ ih =>
      cases fuel₂ with
      | zero => exact (Nat.not_lt_zero _ h₂).elim
      | succ fuel₂ =>
          cases x with
          | mk m n =>
              by_cases h : m = 0
              · subst m
                rfl
              · rw [gcdGo_succ, gcdGo_succ]
                change
                  (if _h : m = 0 then n else
                    WellFounded.Nat.fix.go gcdMeasure gcdStep fuel₁
                      ⟨n % m, m⟩ _) =
                  (if _h : m = 0 then n else
                    WellFounded.Nat.fix.go gcdMeasure gcdStep fuel₂
                      ⟨n % m, m⟩ _)
                rw [dif_neg h, dif_neg h]
                exact ih _ _ _ _

theorem gcdModel_zero_left (n : Nat) : gcdModel 0 n = n := by
  delta gcdModel gcdUnary WellFounded.Nat.fix
  let x : GcdArgs := ⟨0, n⟩
  have hx : gcdMeasure x < 1 := by
    change 0 < 1
    exact Nat.zero_lt_succ 0
  calc
    _ = WellFounded.Nat.fix.go gcdMeasure gcdStep 1 x hx :=
      gcdGo_congr _ _ _ _ _
    _ = n := by rfl

theorem nat_gcd_zero_left (n : Nat) : Nat.gcd 0 n = n := by
  delta Nat.gcd Nat.gcd._unary
  exact gcdModel_zero_left n

theorem gcdModel_succ
    (mod_lt_succ : ∀ n m : Nat, n % Nat.succ m < Nat.succ m)
    (m n : Nat) :
    gcdModel (Nat.succ m) n = gcdModel (n % Nat.succ m) (Nat.succ m) := by
  delta gcdModel gcdUnary WellFounded.Nat.fix
  let x : GcdArgs := ⟨Nat.succ m, n⟩
  let y : GcdArgs := ⟨n % Nat.succ m, Nat.succ m⟩
  have hx : gcdMeasure x < Nat.succ (Nat.succ m) := by
    change Nat.succ m < Nat.succ (Nat.succ m)
    exact Nat.lt_add_one _
  have hy : gcdMeasure y < Nat.succ m := by
    change n % Nat.succ m < Nat.succ m
    exact mod_lt_succ n m
  calc
    _ = WellFounded.Nat.fix.go gcdMeasure gcdStep
          (Nat.succ (Nat.succ m)) x hx := gcdGo_congr _ _ _ _ _
    _ = WellFounded.Nat.fix.go gcdMeasure gcdStep
          (Nat.succ m) y hy := by rfl
    _ = _ := gcdGo_congr _ _ _ _ _

theorem nat_gcd_succ
    (mod_lt_succ : ∀ n m : Nat, n % Nat.succ m < Nat.succ m)
    (m n : Nat) :
    Nat.gcd (Nat.succ m) n = Nat.gcd (n % Nat.succ m) (Nat.succ m) := by
  delta Nat.gcd Nat.gcd._unary
  exact gcdModel_succ mod_lt_succ m n

#print axioms Axeyum.Autogenesis.gcdModel_succ
#print axioms Axeyum.Autogenesis.gcdModel_zero_left
#print axioms Axeyum.Autogenesis.nat_gcd_zero_left
#print axioms Axeyum.Autogenesis.nat_gcd_succ
#print axioms Axeyum.Autogenesis.modLtSucc
#print axioms Axeyum.Autogenesis.gcdGo_congr

end Axeyum.Autogenesis
