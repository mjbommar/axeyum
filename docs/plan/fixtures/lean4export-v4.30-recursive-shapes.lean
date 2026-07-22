prelude

universe u

inductive MiniNat : Type
  | zero
  | succ : MiniNat -> MiniNat

def miniOne : MiniNat := MiniNat.succ MiniNat.zero

inductive MiniList (α : Type u) : Type u
  | nil
  | cons : α -> MiniList α -> MiniList α
