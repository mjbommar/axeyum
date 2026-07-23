prelude

universe u

axiom P : Prop

theorem identity (h : P) : P := h

inductive Two : Type
  | left
  | right

def chooseLeft : Two := Two.left
