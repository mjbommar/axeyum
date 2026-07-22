universe u

namespace AxeyumNestedInductiveComputation

inductive MiniNat : Type
  | zero
  | succ : MiniNat -> MiniNat

def MiniNat.add : MiniNat -> MiniNat -> MiniNat
  | MiniNat.zero, rhs => rhs
  | MiniNat.succ lhs, rhs => MiniNat.succ (MiniNat.add lhs rhs)

inductive Atom : Type
  | token

inductive NestList (α : Type u) : Type u where
  | nil : NestList α
  | cons : α -> NestList α -> NestList α

inductive Rose (α : Type u) : Type u where
  | node : α -> NestList (Rose α) -> Rose α

noncomputable def roseSize {α : Type u} : Rose α -> MiniNat :=
  @Rose.rec α
    (fun _ => MiniNat)
    (fun _ => MiniNat)
    (fun _ _ childrenSize => MiniNat.succ childrenSize)
    MiniNat.zero
    (fun _ _ headSize tailSize =>
      MiniNat.succ (MiniNat.add headSize tailSize))

theorem roseAuxiliaryRecursorComputes :
    roseSize
      (Rose.node Atom.token
        (NestList.cons (Rose.node Atom.token NestList.nil) NestList.nil)) =
      MiniNat.succ
        (MiniNat.succ (MiniNat.succ MiniNat.zero)) :=
  rfl

inductive NestVec (α : Type u) : MiniNat -> Type u where
  | nil : NestVec α MiniNat.zero
  | cons {n : MiniNat} : α -> NestVec α n -> NestVec α (MiniNat.succ n)

inductive IndexedRose (α : Type u) : Type u where
  | node {n : MiniNat} : α -> NestVec (IndexedRose α) n -> IndexedRose α

noncomputable def indexedRoseSize {α : Type u} : IndexedRose α -> MiniNat :=
  @IndexedRose.rec α
    (fun _ => MiniNat)
    (fun _ _ => MiniNat)
    (fun _ _ childrenSize => MiniNat.succ childrenSize)
    MiniNat.zero
    (fun _ _ headSize tailSize =>
      MiniNat.succ (MiniNat.add headSize tailSize))

theorem indexedAuxiliaryRecursorComputes :
    indexedRoseSize
      (IndexedRose.node Atom.token
        (NestVec.cons
          (IndexedRose.node Atom.token NestVec.nil)
          NestVec.nil)) =
      MiniNat.succ
        (MiniNat.succ (MiniNat.succ MiniNat.zero)) :=
  rfl

inductive RepeatRose (α : Type u) : Type u where
  | node : α ->
      NestList (RepeatRose α) ->
      NestList (RepeatRose α) ->
      RepeatRose α

noncomputable def repeatRoseSize {α : Type u} : RepeatRose α -> MiniNat :=
  @RepeatRose.rec α
    (fun _ => MiniNat)
    (fun _ => MiniNat)
    (fun _ _ _ leftSize rightSize =>
      MiniNat.succ (MiniNat.add leftSize rightSize))
    MiniNat.zero
    (fun _ _ headSize tailSize =>
      MiniNat.succ (MiniNat.add headSize tailSize))

theorem repeatedContainerReusesAuxiliaryRecursor :
    repeatRoseSize
      (RepeatRose.node Atom.token
        (NestList.cons
          (RepeatRose.node Atom.token NestList.nil NestList.nil)
          NestList.nil)
        (NestList.cons
          (RepeatRose.node Atom.token NestList.nil NestList.nil)
          NestList.nil)) =
      MiniNat.succ
        (MiniNat.succ
          (MiniNat.succ
            (MiniNat.succ
              (MiniNat.succ MiniNat.zero)))) :=
  rfl

end AxeyumNestedInductiveComputation
