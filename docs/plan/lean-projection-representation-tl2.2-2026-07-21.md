# Lean projection representation — TL2.2 result

Status: **DONE; representation only, semantic admission still fail-closed**

Date: 2026-07-21

Parent plan:
[`lean-system-implementation-plan-2026-07-21.md`](lean-system-implementation-plan-2026-07-21.md)

## Result

TL2.2 adds first-class Lean structure-projection terms to the independent Rust
kernel as:

```text
Proj(structure_type_name, zero_based_field_index, structure)
```

The stored field index is `u32`, giving the same bounded representation on
native and WASM targets. The public constructor is `Kernel::proj`. Interning,
equality, hashing, metadata, level substitution, ordinary substitution,
abstraction, scoped-free-variable closure, loose-bound-variable lifting,
constant/dependency traversal, and both Lean renderers all preserve and recurse
through the new node. The renderer converts the zero-based kernel index to
Lean's one-based numeric field syntax: field index `1` renders as `.2`.

This is a structural representation milestone, not projection semantics.
`infer` returns the typed `KernelError::UnsupportedProj`; a neutral projection
stays neutral under weak-head normalization; declaration admission therefore
rejects any declaration whose type or body requires projection typing and
rolls back cleanly. Wire-format projection translation also remains declined as
`expr-projection`. TL2.3 must validate structure metadata and infer dependent
field types; TL2.4 must implement constructor projection reduction before the
committed official projection closure can receive translated or independently
admitted credit. TL2.5 owns structure eta separately.

## Design alignment

The representation follows the pinned Lean 4.30 kernel and the independent
nanoda checker: a structure type name, a field index excluding constructor
parameters, and the projected expression. The type name is environment
metadata, not an extra term child. Dependency closure records it, while
term-occurrence traversal recurses through the child.

The representation slice deliberately does not guess at malformed structure
names, field bounds, parameter counts, constructor telescopes, or dependent
substitutions. Those checks require the structure metadata and inference
algorithm in TL2.3. Keeping inference fail-closed makes the intermediate commit
reviewable without creating a partial admission path.

## Test boundary

The new `proj_representation` integration suite has four tests:

1. interning and independent name/index/child mutations, including exact child
   metadata propagation;
2. level substitution, free-variable abstraction/instantiation, and loose
   bound-variable lifting through the child;
3. scoped free-variable closure through a projection;
4. neutral normalization and definitional equality, explicit unsupported
   inference, and rollback-clean declaration rejection.

The `lean_pp` unit suite additionally checks ordinary and streaming rendering,
one-based numeric field syntax, dependency collection, and expression
postorder. The complete package result is 178 unit tests plus nine tests across
five integration binaries, all passing under the repository's 4 GiB process
cap. Warning-denied all-target Clippy and all-target package checking pass.

## Explicit non-credit

This result does **not** claim:

- projection type inference or constructor reduction;
- structure eta or new TL2.15 semantic fuzz coverage;
- translation or admission of the official projection fixture;
- Nat/String literal progress merely because projection is their first wire
  decline;
- an official-Lean differential result on this host.

The next unblocked task is TL2.3: preserve and validate single-constructor
structure metadata, then infer parameterized and dependent projection types
with malformed-name/index/telescope mutations.
