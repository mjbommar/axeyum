# Lean nested-inductive elimination: M1 diagnostic preflight

Status: complete; M2 native expansion and restoration is next

Date: 2026-07-22

Parent:
[TL2.14 execution plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md)

Decision gate:
[proposed ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)

Baseline: `48fece10d1c93cf8cf8df7c2d4875ea18cdafa8e`

Implementation: `893afc1f0de3ca60972b3eaf4d84ff0b3d6c66e7`

## Result

M1 fixes only the importer diagnostic boundary registered before semantic
nested-inductive work. `import_inductive` now reads every source family's
`numNested` value before applying ordinary recursor-count policy. It requires
one consistent auxiliary count across an exported group and computes the
claimed wire population as:

```text
source family count + numNested = exported recursor count
```

A self-consistent nonzero shape returns exactly
`ImportError::Unsupported { code: "inductive-nested", ... }` before family,
constructor, or recursor translation and before the kernel admission call. The
frozen official `Rose` row therefore moves from the accidental line-248
`Malformed("single-family inductive must export one recursor")` result to the
registered line-248 `Unsupported("inductive-nested")` boundary.

This preflight does not make exporter metadata trusted admission evidence.
`numNested` is used only to distinguish a well-shaped unsupported wire record
from malformed recursor cardinality. M4 remains responsible for deriving the
auxiliary population structurally and comparing it with exporter metadata
after M2 native semantics and M3 generated coverage exist.

## Preserved malformed boundaries

The new preflight rejects, without a completed import:

- a nested singleton missing its auxiliary recursor;
- a nested singleton with an extra auxiliary recursor;
- a mutual group whose families report different `numNested` values; and
- a claimed nested mutual group whose main-plus-auxiliary count is not exact.

The established non-nested policy remains byte-for-byte stable: a singleton
with `numNested == 0` and either zero or two recursors still returns
`Malformed("single-family inductive must export one recursor")`. Multi-family
groups with no nested auxiliaries still require one recursor per family.

One additional positive policy control gives both families in the existing
mutual fixture the same `numNested = 1` value and adds exactly one claimed
auxiliary recursor. It reaches `Unsupported("inductive-nested")`, proving the
count is group-wide rather than accidentally singleton-specific. It does not
admit or validate that synthetic auxiliary record.

## Frozen controls and publication boundary

The official construct-matrix binary repeats every row twice with the direct-
recursive control before each row. The exact outcomes are retained except for
the preregistered nested diagnostic correction:

- recursive-indexed: 12 declarations complete;
- reflexive/higher-order: 11 declarations complete;
- mutual: 26 declarations complete;
- nested: line-248 `Unsupported("inductive-nested")`, no `CompletedImport`;
- well-founded: 35 declarations and zero axioms complete.

The complete importer suite retains completion-only publication, canonical
declaration identity, official mutual and recursive computation, positivity
error propagation, and the 226-case wire mutation corpus. The deterministic
720 mutual-group, 768 recursive-IH, and 840 positivity populations remain
byte-identical.

No M0 computation stream was added to an importer test or passed to the Rust
product. Their first product observation remains owned by M4. The historical
construct-matrix row and M0 registration remain unchanged; M5 still owns the
append-only assurance overlay and removal of the live nested decline.

## Bounded evidence

All Rust commands used one build job and one test thread under the registered
4 GiB user scope with repository-local temporary storage.

| Gate | Result |
|---|---|
| focused official construct-matrix binary | 4 tests passed, including repeated nested/control runs and recursor-count mutations |
| complete `axeyum-lean-import` all-target suite | 41 integration tests passed |
| retained kernel grammars | 720 mutual + 768 recursive + 840 positivity cases repeated byte-identically |
| importer Clippy | all targets, warnings denied; passed |
| importer rustdoc | warnings denied; passed |
| M0 source/wire contract | checker plus 13 mutation tests passed; hashes and no-product registration unchanged |
| parity, compatibility, foundational-resource, and link gates | passed |
| formatting and staged diff audit | passed |

No process exceeded the resource envelope or received a signal. No limit was
raised. No generated assurance artifact changed.

## Claim boundary

M1 proves a correctly typed, completion-only diagnostic boundary for the exact
official nested construct and preserves ordinary malformed cardinality. It
does **not** prove structural nested discovery, auxiliary-family copying,
fixed-point expansion, positivity or recursor semantics for expanded groups,
surface restoration, `.rec_N` publication, official nested import,
cross-nested computation, source elaboration, ADR acceptance, or Lean parity.

## Next gate

M2 implements private structural discovery, complete auxiliary-container group
copying, fixed-point queuing, final-surface restoration, deterministic
`.rec_N` publication, and transaction-wide rollback through the existing
TL2.13 atomic group checker. It closes the registered native positive/negative
matrix without passing any M0 computation stream to the importer.
