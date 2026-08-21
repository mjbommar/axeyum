import Mathlib.Data.Int.GCD
import autogenesis_div_mod_go_reconstruct_v2

namespace Axeyum.Autogenesis

/-- Public-remainder quotient existence proved with pointwise equality
transport only.  No rewrite occurs under an existential or function binder. -/
theorem modQuotientWitnessV4 (m n : Nat) (hm : 0 < m) :
    ∃ q : Nat, m * q + Nat.mod n m = n := by
  cases n with
  | zero =>
      have hmod : Nat.mod 0 m = 0 := Nat.mod.eq_1 m
      refine ⟨0, ?_⟩
      calc
        m * 0 + Nat.mod 0 m = 0 + Nat.mod 0 m :=
          congrArg (fun value => value + Nat.mod 0 m) (Nat.mul_zero m)
        _ = 0 + 0 := congrArg (fun value => 0 + value) hmod
        _ = 0 := Nat.zero_add 0
  | succ n =>
      by_cases hle : m ≤ Nat.succ n
      · let hfuel : Nat.succ n < Nat.succ (Nat.succ n) :=
          Nat.lt_succ_self (Nat.succ n)
        let q := Nat.div.go m hm (Nat.succ (Nat.succ n)) (Nat.succ n) hfuel
        have hworker :
            m * q + Nat.modCore.go m hm (Nat.succ (Nat.succ n))
              (Nat.succ n) hfuel = Nat.succ n :=
          divModGoReconstruct
            m hm (Nat.succ (Nat.succ n)) (Nat.succ n) hfuel
        have hcore :
            Nat.modCore (Nat.succ n) m =
              Nat.modCore.go m hm (Nat.succ (Nat.succ n))
                (Nat.succ n) hfuel := by
          unfold Nat.modCore
          exact dif_pos hm
        have hcoreCertificate :
            m * q + Nat.modCore (Nat.succ n) m = Nat.succ n :=
          calc
            m * q + Nat.modCore (Nat.succ n) m =
                m * q + Nat.modCore.go m hm (Nat.succ (Nat.succ n))
                  (Nat.succ n) hfuel :=
              congrArg (fun value => m * q + value) hcore
            _ = Nat.succ n := hworker
        have hmod :
            Nat.mod (Nat.succ n) m = Nat.modCore (Nat.succ n) m :=
          calc
            Nat.mod (Nat.succ n) m =
                if m ≤ Nat.succ n then Nat.modCore (Nat.succ n) m
                else Nat.succ n := Nat.mod.eq_2 m n
            _ = Nat.modCore (Nat.succ n) m := if_pos hle
        refine ⟨q, ?_⟩
        calc
          m * q + Nat.mod (Nat.succ n) m =
              m * q + Nat.modCore (Nat.succ n) m :=
            congrArg (fun value => m * q + value) hmod
          _ = Nat.succ n := hcoreCertificate
      · have hmod : Nat.mod (Nat.succ n) m = Nat.succ n :=
          calc
            Nat.mod (Nat.succ n) m =
                if m ≤ Nat.succ n then Nat.modCore (Nat.succ n) m
                else Nat.succ n := Nat.mod.eq_2 m n
            _ = Nat.succ n := if_neg hle
        refine ⟨0, ?_⟩
        calc
          m * 0 + Nat.mod (Nat.succ n) m =
              0 + Nat.mod (Nat.succ n) m :=
            congrArg (fun value => value + Nat.mod (Nat.succ n) m)
              (Nat.mul_zero m)
          _ = 0 + Nat.succ n := congrArg (fun value => 0 + value) hmod
          _ = Nat.succ n := Nat.zero_add (Nat.succ n)

end Axeyum.Autogenesis
