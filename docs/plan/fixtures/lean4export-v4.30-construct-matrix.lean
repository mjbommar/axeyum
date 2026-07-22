import Init.WF

universe u

namespace AxeyumConstructMatrix

inductive MiniNat : Type
  | zero
  | succ : MiniNat -> MiniNat

inductive Atom : Type
  | token

inductive MiniVector (α : Type u) : MiniNat -> Type u
  | nil : MiniVector α MiniNat.zero
  | cons {n : MiniNat} : α -> MiniVector α n -> MiniVector α (MiniNat.succ n)

def recursiveIndexedWitness : MiniVector Atom (MiniNat.succ MiniNat.zero) :=
  MiniVector.cons Atom.token MiniVector.nil

def EmptyRel {α : Sort u} (_ _ : α) : Prop := False

inductive MiniAcc {α : Sort u} (r : α -> α -> Prop) : α -> Prop where
  | intro (x : α) (h : (y : α) -> r y x -> MiniAcc r y) : MiniAcc r x

def reflexiveWitness : MiniAcc (@EmptyRel Atom) Atom.token :=
  MiniAcc.intro Atom.token (fun _ h => False.elim h)

mutual
  inductive EvenTree (α : Type u) : Type u where
    | leaf : α -> EvenTree α
    | branch : OddTree α -> EvenTree α

  inductive OddTree (α : Type u) : Type u where
    | leaf : OddTree α
    | branch : EvenTree α -> OddTree α
end

def mutualTag : EvenTree Atom -> MiniNat
  | EvenTree.leaf _ => MiniNat.zero
  | EvenTree.branch _ => MiniNat.succ MiniNat.zero

theorem mutualWitness :
    mutualTag (EvenTree.branch (OddTree.leaf : OddTree Atom)) =
      MiniNat.succ MiniNat.zero :=
  rfl

inductive NestList (α : Type u) : Type u where
  | nil : NestList α
  | cons : α -> NestList α -> NestList α

inductive Rose (α : Type u) : Type u where
  | node : α -> NestList (Rose α) -> Rose α

def roseRoot : Rose α -> α
  | Rose.node root _ => root

theorem nestedWitness :
    roseRoot (Rose.node Atom.token NestList.nil) = Atom.token :=
  rfl

def atomEmptyRel (_ _ : Atom) : Prop := False

theorem atomEmptyWellFounded : WellFounded atomEmptyRel :=
  ⟨fun x => Acc.intro x (fun _ h => False.elim h)⟩

def wellFoundedLoop : Atom -> MiniNat :=
  atomEmptyWellFounded.fix fun _ _ => MiniNat.zero

theorem wellFoundedWitness : wellFoundedLoop Atom.token = MiniNat.zero :=
  by
    unfold wellFoundedLoop
    rw [WellFounded.fix_eq]

end AxeyumConstructMatrix
