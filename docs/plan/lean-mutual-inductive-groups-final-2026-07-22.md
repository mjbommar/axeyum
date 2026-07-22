# Lean mutual inductive groups: M5 final result and handoff

Status: complete; ADR-0354 accepted; TL2.13 DONE

Date: 2026-07-22

Decision: [accepted ADR-0354](../research/09-decisions/adr-0354-preregister-lean-mutual-inductive-groups.md)

Prior checkpoints:

- [M0 source/wire freeze](lean-mutual-inductive-groups-m0-2026-07-22.md);
- [M1 ordered representation](lean-mutual-inductive-groups-m1-2026-07-22.md);
- [M2 native semantics](lean-mutual-inductive-groups-m2-2026-07-22.md);
- [M3 deterministic group grammar](lean-mutual-inductive-groups-m3-2026-07-22.md);
- [M4 importer and official groups](lean-mutual-inductive-groups-m4-2026-07-22.md).

## Final result

Axeyum now admits an ordered mutual-inductive group as one trusted transaction.
All families share checked parameters and equivalent result universes;
positivity ranges over the complete group; motives follow family order; minors
follow family then constructor order; and every recursive field selects the
motive and recursor of its terminal family. Every generated family,
constructor, recursor type, and closed computation rule is inferred before one
atomic commit. The existing single-family API delegates through this path
without changing its registered identities or behavior.

The importer reconstructs the complete group from checked declarations and
invokes the kernel gate once. It does not trust exporter grouping metadata as
admission authority. Official recursor arrays are matched by checked name and
owned rules because their dependency order (`Odd.rec`, `Even.rec`) differs from
the semantic family order (`Even`, `Odd`). The construct, non-indexed
computation, and indexed computation streams each complete twice. Both selected
cross-family recursor applications normalize independently to
`MiniNat.succ (MiniNat.succ MiniNat.zero)`.

## Accepted evidence

All twelve ADR-0354 exit gates are met:

1. M0 froze the exact Lean 4.30 algorithm, source and wire artifacts, baseline,
   cases, mutations, resource envelope, and stop conditions before admission
   changed.
2. `add_inductive` is a singleton wrapper over the group implementation; the
   registered singleton declarations, recursors, computations, identities,
   errors, rollback, and retry behavior remain exact.
3. Preflight checks shared parameters and universes, family order and names,
   per-family indices, result universes, constructors, and ownership before
   publication.
4. Complete-group positivity rejects cross-family negative, nested,
   bad-parameter, and recursive-index occurrences transactionally.
5. One implementation covers self, cross, mixed self/cross, indexed cross,
   higher-order cross, empty-constructor, and mutual-`Prop` groups.
6. Generated recursors bind all group motives and minors in the registered
   order, and their rules use the checked owner and recursive target families.
7. Mutual propositions eliminate only into `Prop`; mutual K-like reduction is
   rejected.
8. Every recursor and closed rule infer-checks before commit. Native and
   importer late-failure tests expose neither partial declarations nor a
   `CompletedImport`.
9. All three official streams import twice with exact declaration comparison;
   pinned Lean and Axeyum agree on both registered cross-family computations.
10. Native and importer mutation suites reject the registered group, order,
    target, parameter, universe, index, owner, type, count, rule, field, and
    publication corruptions.
11. The 720-case mutual grammar repeats byte-identically at descriptor
    `2ea6769fa45ea159`, with 432 positive contracts and 288 typed rollbacks.
    The 768-case recursive and 840-case positivity controls remain exact.
12. Every final bounded code, official-Lean, contract, generated-document,
    foundational-resource, link, staged-file, and remote-ref gate passes.

## Assurance update

The append-only TL2.13 assurance overlay preserves the original ADR-0351
product measurement and TL2.12 update. The generated seven-row construct
matrix now reports five admitted rows, three independently computation-checked
rows, and one current typed decline. The mutual row is
`dual-admitted-computation-checked` and requires both the non-indexed and
indexed computation streams; it is not promoted from construct admission
alone.

The live compatibility contract no longer registers `inductive-mutual` as an
unsupported feature. Historical M0 and TL2.11 validators hash their original
view of the append-only matrix, while the current matrix validator checks the
TL2.13 overlay. This retains the preregistered evidence rather than rewriting
past observations.

## Final bounded gates

The final pass used one Rust build job under `MemoryHigh=3G`, `MemoryMax=4G`,
and `MemorySwapMax=512M`, with repository-local temporary output because the
system `/tmp` filesystem was saturated.

| gate | result |
|---|---|
| kernel tests | 184 unit + 61 integration passed |
| importer tests | 40 integration passed |
| doctests | kernel and importer passed |
| mutual grammar | 720 unique cases, byte-identical repeat |
| retained grammars | 768 recursive + 840 positivity cases passed |
| official differential | exact pinned Lean 4.30 source and three imported streams passed twice |
| importer mutation boundary | 22 rejecting classes + 2 non-authority controls passed |
| focused clippy | all kernel/importer targets and features, warnings denied, passed |
| focused rustdoc | kernel/importer all features, warnings denied, passed |
| focused rustfmt | every milestone-owned Rust file passed |
| parity/document contracts | 77 Python tests plus every registered generator/checker passed; `DISAGREE=0` |
| construct assurance | 7 rows; 5 admitted; 3 computation-checked; 1 current decline |
| foundational resources | 137 concept rows and 174 packs validated |
| documentation links | passed |
| `git diff --check` | passed |

Workspace-wide `cargo fmt --all --check` remains outside this milestone's
credit because unrelated concurrent solver/FP work is dirty. No unrelated file
was reformatted, staged, or claimed by TL2.13.

## Scope and non-claims

TL2.13 establishes a bounded mutual-inductive kernel/import profile. It does
not claim:

- native Lean mutual syntax, elaboration, pattern compilation, or termination;
- frontend lowering for nested or well-founded definitions;
- every inductive universe/elimination or unsafe-inductive profile;
- broad `Init`, `Std`, or mathlib admission;
- native parser, macros, tactics, compiler, Lake, LSP, or `.olean` support;
- full Lean-kernel parity, consistency, or replacement of official Lean.

## Handoff

The primary Lean compatibility path is TL2.14: preregister frontend lowering
for nested and well-founded source definitions into the already checked
mutual/reflexive core forms. Keep that adapter outside the trusted kernel, prove
the lowered and official declarations definitionally equivalent, and preserve
all TL2.11-TL2.13 positivity, recursive, group-order, computation, mutation,
completion-only-publication, and 4 GiB controls. A smaller independent path may
advance TL1.5 importer property fuzzing without changing TL2.14 semantics.
