# Lane: logic-excluded-middle — `F:excluded-middle-not-intuitionistic` scoping + first slice

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, logic-excluded-middle, 2026-08-29).** Task was
`F:excluded-middle-not-intuitionistic` (one of five open facts outside the
Mathlib-mirror population). Step 0 (mandatory) was to determine what this
kernel already has toward a syntactic underivability result, before building
anything, and report honestly if the fact needs a substantial new
development.

**What exists in the kernel toward this, confirmed by reading source and
`kernel.environment()`, not by inventory tool:**

- No inductive type of syntactic formulas or derivations existed anywhere in
  the kernel before this lane (confirmed by
  `ipc_heyting::tests::no_prior_derivation_relation_exists_before_this_file`,
  which greps `kernel.environment()` for `Provable`/`Derivation`/`.Deriv`
  after building this lane's own prelude, paired with a positive control —
  `Formula`, this lane's own new declaration — so the negative cannot pass
  vacuously).
- The inductive-type list a prior lane enumerated
  (`True/False/And/Or/Iff/Eq/Exists/Acc/Bool/Nat/Decidable` + `Nat.le` +
  `Nat.Fin` + `Char` + `Nat.Pair`) is still current as far as this lane's
  grep of `add_inductive`/`add_datatype_family`/`add_recursive_datatype_family`
  call sites showed; nothing landed since adds a formula/derivation/proof-
  system type.
- The logic prelude (`prelude.rs`) already carries a substantial, genuinely
  useful family of Prop-generic results **around** excluded middle —
  `not_not_em : ¬¬(p ∨ ¬p)`, and the equivalences `dne_of_em`, `em_of_dne`,
  `peirce_of_em`, `em_of_peirce` — but every one is either a double-negation
  of `p ∨ ¬p` or a conditional equivalence taking EM/DNE/Peirce as a
  hypothesis. None is an instance of EM itself, and none is a derivation
  relation. This is the closest existing analogue and is NOT what the fact
  needs.
- **Generic infrastructure that DOES help**: `Kernel::add_recursive_datatype_family`
  (`prelude.rs`, already exercised in production by `string_prelude`'s `Str`
  and by the `IntList` example in `prelude/prelude_tests.rs`) builds exactly
  the AST shape a `Formula` type needs — mixed opaque-carrier / self-
  referential fields, non-parametric, non-indexed.

**Decomposition** (recorded in full, with rationale, in the module docs of
`crates/axeyum-lean-kernel/src/ipc_heyting.rs`):

Detail moved to [`../notes/273-logic-excluded-middle.md`](../notes/273-logic-excluded-middle.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | logic-excluded-middle | `Formula` AST + 3-element Heyting-chain semantic countermodel (`ipc_heyting.rs`); new fact `F:heyting-3-chain-refutes-excluded-middle` (proved); `F:excluded-middle-not-intuitionistic` stays open with scoping notes recorded |
