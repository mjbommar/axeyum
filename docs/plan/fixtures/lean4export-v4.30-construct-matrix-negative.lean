prelude

namespace AxeyumConstructMatrixNegative

inductive Atom : Type
  | token

inductive NonPositive : Type where
  | mk : (NonPositive -> Atom) -> NonPositive

end AxeyumConstructMatrixNegative
