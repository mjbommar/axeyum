# Root-selected fresh-kernel foundation

Date: 2026-08-19

## Result

The kernel's canonical `lean4export` writer can now emit only the complete
declaration closure of explicit roots. Re-importing that stream creates the
fresh arena and minimal producer environment required by ADR-0484 without a
second serializer or cross-kernel handle copying.

The operation is deliberately semantic, not textual:

- it follows declaration types, values, and recursor reduction rules;
- selecting any inductive member retains the complete family, constructors,
  and generated recursors as one atomic unit;
- a quotient package remains atomic;
- dependency order is deterministic and root order or duplication does not
  change bytes;
- empty roots, absent roots, missing dependencies, cycles, incomplete packages,
  unclaimed constructors/recursors, free variables, and write failures are
  typed errors; and
- unrelated declarations are absent from the output and therefore unavailable
  after re-import.

An importer differential test selects only `True.intro` from the complete logic
prelude. The emitted stream independently re-admits exactly `True`, `True.rec`,
and `True.intro` in a fresh kernel; the unrelated `False` family is absent; and
selecting the same root from the new kernel reproduces identical bytes.

## Assurance boundary

This increment does **not** yet remove proof-bearing implementation closure. A
selected definition still pulls every constant referenced by its body, including
a theorem or axiom. That behavior is a required negative property: root
selection cannot masquerade as type slicing.

ADR-0484's next layer must first generalize eligible constants into explicit
non-`Prop` parameters in the validated source kernel. Only then may this root
export carry the generalized target and its retained proof-free dependencies
into a fresh producer kernel.

## Why this sequence

The fresh-kernel boundary is separable from abstraction policy and independently
useful. Freezing it first gives the slicer one canonical transport:

```text
validated broad kernel
        |
        | build generalized target (next increment)
        v
root-selected canonical export
        |
        | ordinary fail-closed importer
        v
fresh minimal producer kernel
```

The exporter and importer implement the same external format independently and
the comparison uses the canonical declaration identity manifest. A direct
in-memory clone would share more code and provide weaker evidence that the new
environment is complete.

## Reproduction

```sh
cargo test -p axeyum-lean-kernel lean_export::tests
cargo test -p axeyum-lean-import --test export_round_trip \
  root_selected_environment_round_trips_without_unrelated_declarations
```
