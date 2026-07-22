prelude

namespace AxeyumStrictPositivityDeep

inductive Atom : Type where
  | token

inductive NegativeDeep : Type where
  | mk : ((Atom -> NegativeDeep) -> Atom) -> NegativeDeep

end AxeyumStrictPositivityDeep
