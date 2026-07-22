universe u

namespace AxeyumNestedInductiveNegative

inductive Box (α : Type u) : Type u where
  | wrap : α -> Box α

inductive BadNested : Type (u + 1) where
  | node : (α : Type u) -> Box (BadNested -> α) -> BadNested

end AxeyumNestedInductiveNegative
