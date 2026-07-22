# Lean nested-inductive elimination M4: exact official import

Date: 2026-07-22

Status: complete

Semantic commit: `f03dfcdf2b3e49d86a5bb9ad00aeef20c99926ee`

Decision gate:
[proposed ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)

Execution contract:
[TL2.14 P0--M6 plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md)

Frozen design:
[M4 exact importer plan](lean-nested-inductive-elimination-m4-plan-2026-07-22.md)

## Result

M4 removes only the importer's structural
`Unsupported("inductive-nested")` admission boundary. The importer now passes
translated source families and constructors through the native M2/M3 kernel
gate, derives the generated auxiliary population from checked main-recursor
metadata, and compares every official main and auxiliary recursor by exact
kernel-derived name before the private staging kernel may become a
`CompletedImport`.

The construct-matrix nested stream and all three M0 computation streams import
twice with exact full-report equality and zero axioms. Their source families,
constructors, main recursors, auxiliary `.rec_N` recursors, types, universe
parameters, indices, motives, minors, restored rule constructors, field counts,
and closed rule right-hand sides agree with the independent kernel output.

This is exact official declaration-import credit. M4 deliberately does not
extract or compare a selected theorem's normal form, append an assurance
overlay, remove the live nested decline from generated compatibility state, or
accept ADR-0355. M5 owns those computation and assurance transitions.

## Kernel-derived authority

`numNested` remains descriptive wire metadata. The importer now:

1. parses the complete source group without using `numNested` for admission;
2. calls `Kernel::add_mutual_inductive` once with the translated source surface;
3. reads the checked first main recursor and derives
   `N = num_motives - source_family_count`;
4. compares every exported family `numNested` value to `N` before recursor
   count or name parsing;
5. constructs the exact expected set of source `Family.rec` names plus
   `First.rec_1` through `First.rec_N`; and
6. maps wire records by those names, independent of array position.

No environment-size delta, suffix probing, exporter count, display order, or
hash-map order authorizes the result. Native admission already guarantees the
deterministic gap-free public suffixes.

The frozen diagnostic order is preserved. A false but self-consistent
`numNested` receives `generated/exported numNested differs`; a correct nested
count with missing/extra records receives the historical nested-count error;
and derived ordinary groups retain the singleton/mutual count diagnostics from
M1.

## Exact recursor comparison

The former source-main-only comparison is generalized over the complete
kernel-derived name set. Every main and auxiliary record must have:

- exact name membership, uniqueness, and source-group `all` names;
- `isUnsafe = false`;
- exact universe-parameter arity and alpha-renamed type definitional equality;
- exact parameter, index, motive, and minor counts;
- exact rule count/order, restored constructor, field count, and alpha-renamed
  right-hand-side definitional equality; and
- a generated public `Declaration::Recursor` of the same name.

Source-main index counts are additionally tied to the exported source family.
Auxiliary index counts are compared directly with the generated auxiliary
recursor, which closes the indexed `NestVec` case without copying the source
family's zero-index shape.

Axeyum does not add a wire K flag to trusted recursor state. Pinned Lean 4.30
allows K only when the checked expanded group has one type former, is `Prop`,
has one constructor, and has zero nonparameter fields. A derived `N > 0`
proves the expanded group had `source_family_count + N > 1` motives/type
formers, so every restored nested main/auxiliary recursor is non-K. Wire
`k = true` therefore rejects without a kernel API change.

## Exact official imports

The following full reports repeat exactly twice:

| Stream | Names | Levels | Expressions | Declaration records | Admitted | Axioms |
|---|---:|---:|---:|---:|---:|---:|
| construct-matrix nested | 70 | 6 | 322 | 10 | 22 | 0 |
| auxiliary recursion | 122 | 8 | 494 | 17 | 34 | 0 |
| indexed container | 134 | 8 | 554 | 17 | 34 | 0 |
| repeated container | 122 | 8 | 518 | 17 | 34 | 0 |

Every report has one declaration identity per admitted declaration under
`axeyum-lean-declaration-identity-v1`.

The exact public recursor observations match M0:

- each source main and auxiliary recursor has two motives and three minors;
- `Rose.rec_1` owns `NestList.nil/cons` rules with `[0, 2]` fields;
- `IndexedRose.rec_1` has one index and owns `NestVec.nil/cons [0, 3]`;
- `RepeatRose.rec_1` is published once for two structurally identical fields
  and owns `NestList.nil/cons [0, 2]`; and
- each source main recursor owns its source constructor with the registered
  two- or three-field rule.

All four nested records also import after reversing their recursor arrays and
produce the same complete report and identity manifest. This covers both
official order shapes: auxiliary-before-main in the construct, Rose, and
IndexedRose streams, and main-before-auxiliary in the RepeatRose stream.

The well-founded control remains 160 names, 5 levels, 731 expressions, 23
declaration records, 35 admitted declarations, and zero axioms, twice with
equal reports.

## Mutation evidence

The M4 suite closes the 20 preregistered rejecting classes:

1. false zero `numNested`;
2. false count two with a count-matching third record;
3. missing exact `rec_1`;
4. extra recursor;
5. duplicate recursor name;
6. foreign recursor name;
7. wrong `all` group;
8. wrong type;
9. wrong parameter count;
10. wrong source-main and auxiliary index counts;
11. wrong motive count;
12. wrong minor count;
13. wrong universe-parameter arity;
14. missing and extra rules;
15. wrong restored rule constructor;
16. wrong rule field count;
17. wrong rule right-hand side;
18. unsafe recursor flag;
19. K flag on both main and auxiliary recursors; and
20. a valid nested group followed by a line-642 theorem renamed to the already
    admitted `Eq` declaration.

Every mutation checks the exact registered `ImportError` line/message/code or
kernel `DeclarationExists` payload. A direct-recursive control completes before
every rejection. The late collision returns no completed kernel or report,
confirming that post-admission comparison and later-record failures remain
inside the importer-owned staging kernel.

## Validation

All Rust commands used one Cargo job and one test thread under
`MemoryHigh=3G`, `MemoryMax=4G`, and `MemorySwapMax=512M`, with this worktree's
own target and repository-local temporary directory.

- six focused official nested tests passed;
- the four historical construct-matrix tests passed with the nested row now
  complete and the ordinary malformed controls unchanged;
- complete `axeyum-lean-import --all-targets --all-features` passed 47
  integration tests across all binaries;
- complete `axeyum-lean-kernel --all-targets --all-features` passed 188 unit
  tests and every integration target;
- the M2 23-case native matrix and M3 exact 640-case digest remained green;
- retained 720 mutual, 768 recursive-IH, and 840 positivity populations passed
  byte-identically;
- warning-denied importer Clippy and rustdoc passed;
- the importer compile-fail doctest passed;
- the historical M0 source/wire freeze checker and all 13 checker tests passed;
- parity documentation, foundational resources, shell syntax, and relative
  links passed;
- direct formatting and `git diff --check` passed; and
- local, tracking, and remote semantic refs all resolved to
  `f03dfcdf2b3e49d86a5bb9ad00aeef20c99926ee` after push.

This intermediate M4 checkpoint is deliberately not merge-ready. The
compatibility generator reports exactly
`LEAN_COMPATIBILITY_ERROR|inductive-nested: crates/axeyum-lean-import/src/lib.rs missing marker '"inductive-nested"'`
because M4 removed the implemented importer decline while its live assurance
registration remains frozen for M5. Relocating the marker to historical
evidence or reintroducing a dead source literal would falsely claim a live
decline. M5 must restore the aggregate green state by first proving the three
registered normal forms and then removing the obsolete live registry entry.

An independent read-only agent audited the frozen design and completed Rust
diff. Its final pass found no semantic blocker, confirmed all 20 mutation
classes and named variants, verified derived-count/name/K authority and
completion-only publication, and found no kernel/fixture/identity or M5
boundary breach.

## Historical and live state

M0's machine registration remains an immutable pre-product snapshot: it still
records that no M0 computation stream had been observed at the source/wire
freeze. M4 is the explicitly planned first product import of those streams and
does not rewrite that history.

The live generated compatibility/assurance state still retains its nested
decline because M5 has not yet reproduced the selected registered normal forms
as explicit Axeyum observations or appended the history-preserving TL2.14
overlay.

## What remains

M5 is next. It must repeat the pinned Lean source computations, explicitly
extract and normalize the selected theorem sides in each completed Axeyum
import, require the three registered cross-nested normal forms, append the
TL2.14 assurance overlay without rewriting prior stages, and remove the live
nested decline only after every computation/mutation/retention gate passes.

M6 still owns the final aggregate gates, ADR-0355 disposition, and complete
planning/generated-document reconciliation.
