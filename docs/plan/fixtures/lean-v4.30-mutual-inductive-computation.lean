universe u

namespace AxeyumMutualInductiveComputation

inductive MiniNat : Type
  | zero
  | succ : MiniNat -> MiniNat

inductive Atom : Type
  | token

mutual
  inductive EvenTree (α : Type u) : Type u where
    | leaf : α -> EvenTree α
    | branch : OddTree α -> EvenTree α

  inductive OddTree (α : Type u) : Type u where
    | leaf : OddTree α
    | branch : EvenTree α -> OddTree α
end

noncomputable def evenHeight {α : Type u} : EvenTree α -> MiniNat :=
  @EvenTree.rec α
    (fun _ => MiniNat)
    (fun _ => MiniNat)
    (fun _ => MiniNat.zero)
    (fun _ ih => MiniNat.succ ih)
    MiniNat.zero
    (fun _ ih => MiniNat.succ ih)

theorem crossFamilyComputes :
    evenHeight
      (EvenTree.branch
        (OddTree.branch (EvenTree.leaf Atom.token))) =
      MiniNat.succ (MiniNat.succ MiniNat.zero) :=
  rfl

mutual
  inductive EvenVec (α : Type u) : MiniNat -> Type u where
    | nil : EvenVec α MiniNat.zero
    | step {n : MiniNat} : OddVec α n -> EvenVec α (MiniNat.succ n)

  inductive OddVec (α : Type u) : MiniNat -> Type u where
    | nil : OddVec α MiniNat.zero
    | step {n : MiniNat} : EvenVec α n -> OddVec α (MiniNat.succ n)
end

noncomputable def oddVecHeight {α : Type u} {n : MiniNat} :
    OddVec α n -> MiniNat :=
  @OddVec.rec α
    (fun _ _ => MiniNat)
    (fun _ _ => MiniNat)
    MiniNat.zero
    (fun _ ih => MiniNat.succ ih)
    MiniNat.zero
    (fun _ ih => MiniNat.succ ih)
    n

theorem indexedCrossFamilyComputes :
    oddVecHeight
      (OddVec.step
        (EvenVec.step (OddVec.nil : OddVec Atom MiniNat.zero))) =
      MiniNat.succ (MiniNat.succ MiniNat.zero) :=
  rfl

end AxeyumMutualInductiveComputation
