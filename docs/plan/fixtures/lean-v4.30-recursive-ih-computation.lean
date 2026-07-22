universe u

namespace AxeyumRecursiveIHComputation

inductive MiniNat : Type
  | zero : MiniNat
  | succ : MiniNat -> MiniNat

inductive Atom : Type
  | token : Atom

inductive MiniVector (alpha : Type u) : MiniNat -> Type u
  | nil : MiniVector alpha MiniNat.zero
  | cons {n : MiniNat} :
      alpha -> MiniVector alpha n -> MiniVector alpha (MiniNat.succ n)

noncomputable def vectorHeight {alpha : Type u} {n : MiniNat}
    (value : MiniVector alpha n) : MiniNat :=
  MiniVector.rec (motive := fun _ _ => MiniNat)
    MiniNat.zero
    (fun _ _ ih => MiniNat.succ ih)
    value

def vectorOne : MiniVector Atom (MiniNat.succ MiniNat.zero) :=
  MiniVector.cons Atom.token MiniVector.nil

theorem vectorHeightComputes :
    vectorHeight vectorOne = MiniNat.succ MiniNat.zero :=
  rfl

def EmptyRel {alpha : Sort u} (_ _ : alpha) : Prop := False

inductive MiniAcc {alpha : Sort u} (r : alpha -> alpha -> Prop) : alpha -> Prop where
  | intro (x : alpha) (h : (y : alpha) -> r y x -> MiniAcc r y) : MiniAcc r x

noncomputable def accProperty {alpha : Sort u} {r : alpha -> alpha -> Prop} {x : alpha}
    (value : MiniAcc r x) : Prop :=
  MiniAcc.rec (motive := fun _ _ => Prop)
    (fun _ _ _ => True)
    value

def emptyAcc : MiniAcc (@EmptyRel Atom) Atom.token :=
  MiniAcc.intro Atom.token (fun _ h => False.elim h)

theorem accPropertyComputes : accProperty emptyAcc = True :=
  rfl

end AxeyumRecursiveIHComputation
