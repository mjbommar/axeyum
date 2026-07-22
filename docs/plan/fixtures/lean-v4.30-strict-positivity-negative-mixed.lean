prelude

namespace AxeyumStrictPositivityMixed

inductive NegativeMixed : Type where
  | mk : (NegativeMixed -> NegativeMixed) -> NegativeMixed

end AxeyumStrictPositivityMixed
