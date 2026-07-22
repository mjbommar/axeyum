# Lean mutual inductive groups: M4 importer and official computation result

Status: complete; M5 assurance update and closure are next

Date: 2026-07-22

Parent:
[TL2.13 execution plan](lean-mutual-inductive-groups-tl2.13-plan-2026-07-22.md)

Decision gate:
[proposed ADR-0354](../research/09-decisions/adr-0354-preregister-lean-mutual-inductive-groups.md)

Baseline: `6ba7e8a18cc56f21a85cfe1d55b5fc0c4a366b77`

## Result

M4 removes only the importer's blanket multi-family policy decline. One
official `inductive` record is now parsed as one ordered group, passed once to
`Kernel::add_mutual_inductive`, and published only if the complete stream and
every generated/exported comparison succeed.

The importer independently validates:

- a nonempty, duplicate-free ordered family list;
- exact ordered `all` arrays on every family and recursor;
- common universe parameters and parameter counts;
- every family's type, parameter/index counts, recursive metadata, and ordered
  constructor-name list;
- every constructor's owner, family-local `cidx`, universe parameters,
  parameter count, type, field count, and global family/constructor wire order;
- one named recursor per family, including type after universe-binder alpha
  renaming, parameter/index/motive/minor counts, owned constructor rules, rule
  right-hand sides, and `nfields`;
- the mutual restriction that no recursor is exported as a K target.

Official recursor array position is deliberately non-authoritative. Both M0
computation streams export `Odd.rec, Even.rec` while the semantic group order is
`Even, Odd`; M4 indexes recursor records by checked name and then compares each
family's owned rules. Reversing that wire array preserves the completed report,
while reordering either ordered `all` array rejects.

## Exact official imports

Each frozen stream imports twice to an identical `ImportReport` and canonical
declaration-identity manifest:

| Stream | N/L/E/D | admitted | axioms | checked result |
|---|---:|---:|---:|---|
| construct-matrix mutual | 75/4/305/10 | 26 | 0 | both families, four constructors, both recursors, and `mutualWitness` present |
| non-indexed cross-family computation | 60/4/246/7 | 21 | 0 | `crossFamilyComputes` normalizes to `succ (succ zero)` |
| indexed cross-family computation | 72/4/290/7 | 21 | 0 | `indexedCrossFamilyComputes` normalizes to `succ (succ zero)` |

For the non-indexed group, both recursors have one parameter, zero indices, two
motives, and four global minors. Their owned rule field counts are `[1, 1]` for
`EvenTree.rec` and `[0, 1]` for `OddTree.rec`. For the indexed group, both
recursors have one parameter, one index, two motives, four global minors, and
owned rule field counts `[0, 2]`. These values are read from the independently
generated declarations after exact comparison with the official records.

Both theorem checks infer the imported proof, require the theorem type to be an
`Eq`, require its two sides to be definitionally equal, require the right side
to equal the registered normal form, and recursively normalize the left
application spine. The observed reductions therefore cross the family boundary
rather than receiving constructor-only admission credit.

## Mutation and publication teeth

The focused official-wire test closes 22 rejecting mutation classes plus two
non-authoritative/descriptive positive controls:

- family and recursor `all` order, mutual K metadata, duplicate recursor name,
  and recursor wire order;
- family universe parameters, parameter/index counts, `isRec`, and descriptive
  `isReflexive`;
- constructor owner, `cidx`, parameter count, field count, type, and wire order;
- recursor type, all four counts, rule right-hand side, and rule field count;
- a theorem failure after the complete mutual record.

Every rejecting mutation returns an error rather than `CompletedImport`. The
late theorem mutation additionally proves that a successfully checked group in
the private staging kernel is still not published when a later declaration
fails. Flipping `isReflexive` and reversing only the recursor record array leave
the completed result unchanged, proving that neither descriptive metadata nor
dependency-ordered wire position grants semantic authority.

## Retained controls and bounded evidence

All Rust build/test commands use one Cargo job and a 4 GiB physical-memory
scope or the existing 4 GiB bounded runner.

| Gate | Result |
|---|---:|
| official mutual product tests | 6 tests passed; three streams x two exact imports plus computation and 24 mutation/control classes |
| complete importer all-target/all-feature suite | 40 integration tests passed |
| complete kernel all-target/all-feature suite | 184 unit tests plus all integration targets passed |
| mutual grammar | 720 cases x 2; descriptor `2ea6769fa45ea159` |
| retained recursive grammar | 768 cases; descriptor `0d245921566be735` |
| retained positivity grammar | 840 cases; descriptor `02985687422aa0ff` |
| kernel/importer Clippy | all targets/features, warnings denied; passed |
| kernel/importer rustdoc | all features, warnings denied; passed |
| kernel/importer doctests | two passed |
| owned Rust formatting and diff check | passed |

The host's `/tmp` is a 62 GiB tmpfs with 50 GiB already occupied by unrelated
artifacts. The kernel doctest linker first failed there with `SIGBUS`; forcing
GNU `ld` exposed `No space left on device`. The same unchanged doctest passed
inside the registered 4 GiB systemd scope when `TMPDIR` was placed on the normal
filesystem, and that unique empty temporary directory was removed afterward.
`dmesg` access was unavailable to the unprivileged session and the kernel
journal had no matching entry. This was a temporary-storage infrastructure
failure, not an OOM, source failure, or relaxed gate.

Workspace-wide `cargo fmt --all --check` remains red on unrelated existing CAS/
bench files. All three owned Rust files pass direct edition-2024 rustfmt, and
the complete owned diff passes `git diff --check`.

## Historical evidence boundary

M0 and the official construct-matrix product freeze remain immutable historical
observations: at their recorded revisions the importer declined mutual groups.
M4 changes the current product and adds current exact evidence; it does not edit
those old observations in place. M5 owns the generated assurance overlay and
must preserve the distinction between historical pre-widening outcome and
current post-widening capability.

## Claim boundary

M4 establishes exact import and selected cross-family computation for the three
frozen official Lean 4.30 streams. Together with M1-M3 it supports one bounded
atomic mutual-group kernel/import profile.

It does **not** establish native mutual syntax or elaboration, pattern-match or
termination compilation, nested/well-founded frontend lowering, every mutual
universe/elimination profile, broad `Init`/`Std`/mathlib admission, a direct
`.olean` reader, ADR-0354 acceptance, or Lean parity.

## Next gate

M5 regenerates the machine assurance matrix without rewriting historical
observations, runs every bounded final gate, decides ADR-0354 strictly from its
registered exits, synchronizes PLAN/STATUS/project state/roadmaps/P6.0/research
questions, and hands the semantic path to TL2.14 only if all exits pass.
