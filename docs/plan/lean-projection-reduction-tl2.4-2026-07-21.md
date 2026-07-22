# Lean constructor projection reduction — TL2.4 result

Date: 2026-07-21
Status: **complete for constructor reduction and the exact official K1 projection root**

## Result

The independent Rust kernel now weak-head reduces a projection when its
projected value normalizes to a constructor application:

```text
Proj(I, field_index, C.{u} params... fields...)  -->  fields[field_index]
```

The reducer skips the constructor's checked parameter prefix, selects the field,
and re-applies any arguments outside the projection. It normalizes the projected
value through ordinary beta/zeta/delta/iota/projection reduction, so projections
through reducible definitions compute while opaque and neutral values remain
neutral.

This closes TL2.4 and enables format-3.1 `proj` translation in
`axeyum-lean-import`. The pinned official `importPairLeft` stream now translates
all 61 expressions, independently admits nine kernel declarations from four
declaration records, and computes `importPairLeft (ImportPair.mk 0 1)` to `0`.
Wrong structure-name and field-index mutations reach the trusted kernel gate and
reject.

## Reduction contract

The implementation follows the pinned Lean 4.30 `reduce_proj_core` boundary:

1. weak-head normalize the projected value;
2. require a constructor constant as its application head;
3. obtain that constructor's checked parameter count;
4. select argument `num_params + field_index`; and
5. re-apply an outer application spine and continue normalization.

Reduction intentionally follows the actual constructor rather than rechecking
the structure name stored in the projection node. Lean makes the same split:
inference validates structure identity, arity, field bounds, dependent types,
and Prop elimination; reduction is a computation rule over the constructor
payload. A dedicated control proves that a wrong-name projection can reduce as
an untyped term while `infer` still rejects it with `ProjectionTypeMismatch`.

No structure eta is added here. TL2.5 remains a separate definitional-equality
change and differential gate.

## Evidence

`projection_reduction.rs` adds four native integration families:

1. parameterized, universe-polymorphic field selection, including skipping the
   parameter and re-applying an outer function argument;
2. a dependent second field whose proof payload reduces while its inferred type
   remains definitionally equal to the first-field proposition;
3. reduction through a transparent definition, with opaque, axiom-neutral, and
   under/over-applied constructor controls; and
4. the exact reduction/inference separation for a malformed structure name.

The importer suite adds:

- complete admission and computation for the pinned official projection root;
- exact report counts: 21 names, two nonzero levels, 61 wire expressions, four
  declaration records, nine admitted declarations, and zero axioms;
- wire-shape controls for oversized indices and forward structure references;
- wrong-name and out-of-range mutations rejected at declaration line 83 by the
  independent kernel; and
- a refreshed Nat-literal root whose first decline moves from projection to
  `literal-nat-bignum-and-typing` at line 125.

Under the repository's hard 4 GiB wrapper, the final bounded gates record:

- `axeyum-lean-kernel`: 179 unit tests and 17 integration cases across seven
  integration binaries;
- `axeyum-lean-import`: 14 integration tests;
- kernel/import warning-denied all-target Clippy, package checks, kernel
  warning-denied rustdoc, and the kernel doctest; and
- the compatibility-contract tests, generated matrix checks, parity-document
  checks, and link validation.

The algorithm is cross-checked against the pinned upstream
[Lean 4.30 type checker](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/type_checker.cpp).
The committed stream is official-source/export evidence; this host still has no
Lean executable, so this slice does not claim a fresh local official-Lean
differential run.

## Credit boundary and next step

The exact structure-projection row advances from K1 decline to K1 pass. This does
not imply general `Init`, `Std`, mathlib, native-source, tactic, workflow, or
runtime compatibility. It also does not close generated projection/eta seam
fuzzing: the direct positive/mutation matrix is live, but TL2.15 remains partial
until the generated projection/reduction/eta family is added.

The next ordered kernel task is **TL2.5 structure eta**, kept separate from
constructor reduction. After that, TL2.6 must replace `Lit::Nat(u128)` with
arbitrary-precision storage before TL2.7 enables Nat literal typing. The
570,807-byte String stream was never committed locally; its old line-184
projection decline is retired but its new first blocker must remain unmeasured
until the exact bound artifact is retrieved or regenerated and retained.
