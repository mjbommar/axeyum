import Mathlib.Data.Int.Fib.Basic

namespace Axeyum.Autogenesis

theorem intPairCasesResidualV1
    (P : Int → Int → Prop)
    (split : ∀ z : Int, (∃ n : Nat, z = Int.ofNat n) ∨ ∃ n : Nat, z = Int.negSucc n)
    (ofNat_ofNat : ∀ m n : Nat, P (Int.ofNat m) (Int.ofNat n))
    (ofNat_negSucc : ∀ m n : Nat, P (Int.ofNat m) (Int.negSucc n))
    (negSucc_ofNat : ∀ m n : Nat, P (Int.negSucc m) (Int.ofNat n))
    (negSucc_negSucc : ∀ m n : Nat, P (Int.negSucc m) (Int.negSucc n)) :
    ∀ m n : Int, P m n := by
  intro m n
  exact Or.elim (split m)
    (fun hm => Exists.elim hm fun a ha =>
      Or.elim (split n)
        (fun hn => Exists.elim hn fun b hb => ha ▸ hb ▸ ofNat_ofNat a b)
        (fun hn => Exists.elim hn fun b hb => ha ▸ hb ▸ ofNat_negSucc a b))
    (fun hm => Exists.elim hm fun a ha =>
      Or.elim (split n)
        (fun hn => Exists.elim hn fun b hb => ha ▸ hb ▸ negSucc_ofNat a b)
        (fun hn => Exists.elim hn fun b hb => ha ▸ hb ▸ negSucc_negSucc a b))

end Axeyum.Autogenesis
