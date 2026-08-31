
- `Complex.hornerFromTop` -> `Complex.hornerFromTop_MUTATED`
  (`complex.rs:1713`): `kernel_declaration_projection --require-declaration
  Complex.hornerFromTop` count **0**, exit **1**. Control in the SAME rebuild,
  `Complex.polyMul`: count **1**, exit **0**.
- `CReal.negOnePowDouble` -> `CReal.negOnePowDouble_MUTATED`
  (`creal.rs:4715`): `theorem_dependency_inventory CReal.negOnePowDouble`
  count **0**, exit **1**. Control `CReal.alternatingELeO` (which depends on
  `negOnePowDouble` via the `NameId`, not the string, so it still builds and
  is found unaffected): count **1**, exit **0**.
- `Nat.succ_add` -> `Nat.succ_add_MUTATED` (`nat_prelude.rs:1909`, a
  pre-existing dependency fact `F:nat-succ-add` this batch cites, not a new
  registration — this batch has no NEW `Nat.*` fact since `Nat.even_or_odd`
  does not exist): `theorem_dependency_inventory Nat.succ_add` count **0**,
  exit **1**. Control `Nat.add_comm`: count **1**, exit **0**.
