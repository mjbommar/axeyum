# Lean U2 TL0.6.4 M2.2 R1 plan — effective imports and ordered `.olean` parts

Status: **preregistered correction only; no M2.2 input authority, helper,
process, evidence root, or credit exists**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[M2 program](lean-u2-native-surface-classification-tl0.6.4-m2-plan-2026-07-23.md),
[accepted M2.0 result](lean-u2-native-surface-classification-tl0.6.4-m2.0-result-2026-07-23.md),
[M2.2 semantics plan](lean-u2-native-dependency-tl0.6.4-m2.2-plan-2026-07-23.md),
and [M2.1 pre-execution result](lean-u2-native-dependency-tl0.6.4-m2.1-pre-execution-2026-07-23.md).

## 1. Why R1 is required

The M2.2 semantics plan correctly separates header occurrences, candidate
paths, existing files, content identities, raw module-data imports, and
transitive closure. A second source audit found two narrower rules that must be
frozen before implementation:

1. Lean does not load the unqualified graph-theoretic transitive closure. It
   computes a least fixed point whose state depends on the root's `module`
   mode, command-line/server level, and every `public`, `meta`, and `all`
   modifier. Multiple paths to one module can upgrade its state and force its
   descendants to be revisited.
2. A module-system `.olean`, `.olean.server`, and `.olean.private` family is
   one ordered incremental serialization. Later parts can share objects with
   earlier parts and cannot be treated as independently readable module files.

Without R1, an implementation could preserve every raw import occurrence yet
still over-credit a private edge, miss a transitive meta-phase `.ir` input,
read a private part independently, erase a fixed-point upgrade, or call a raw
cycle an executable closure. This correction supersedes only the affected
closure/part-loading rules in M2.2.0. Its path-resolution, inventory, process,
evidence, authorization, acceptance-order, and zero-credit rules remain in
force.

## 2. Exact upstream proof surface

The later implementation must bind and validate these exact files before using
the corrected rules:

| Pinned source | SHA-256 | R1 rule |
|---|---|---|
| `src/Lean/Setup.lean` | `452c19cab80687c56fbf90c3b9ee2627d66c40a49c15bab710d507dd4453df5a` | import fields, IR phases, module headers, and explicit `ImportArtifacts` ordering |
| `src/Lean/Elab/Import.lean` | `43dee2c40840f9efc6abb4d41f428f4383911249f9b70be1169298fbc0026fb3` | implicit `Init` occurrences and root `exported`/`server`/`private` level selection |
| `src/Lean/Elab/ParseImportsFast.lean` | `119ddfbd5e6b7dbe1847bfe5094c87c65e330669966b3a76de02dc12087abcb3` | M2.1 fast-header fields that seed the later effective projection |
| `src/Lean/Environment.lean` | `54f6ca1b7a49a52ff2d9fadb4ef544745584961d5e091ce6dd998228dbd2b253` | incremental part serialization, default discovery, fixed-point import state, IR loading, final module order, and selected data levels |

Primary online context is the official
[Source Files and Modules reference](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/),
the pinned
[`Environment.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Environment.lean),
and the official
[Lean 4.30.0 release note](https://lean-lang.org/doc/reference/latest/releases/v4.30.0/).
The release note's fix for transitive meta-import IR in Lake is corroborating
context; the pinned implementation is authoritative for the target.

Pinned upstream module tests provide control shapes, not U2 observations:

| Test source | SHA-256 | Required shape |
|---|---|---|
| `tests/pkg/module/Module.lean` | `98fcf3be4b423350a9ca08613b21ec4ce674c904da5ae519dfcb43fb1b8c193c` | exported versus server data |
| `tests/pkg/module/Module/Basic.lean` | `67c6235fd4c5e71c39367839b68ff180563da800d37e7b9f417941d439802270` | duplicate ordinary/meta reachability |
| `tests/pkg/module/Module/ImportedAll.lean` | `ad5788911ab4585556ba56e63dcfd0827ce2105fc8e0b1093500e8687cfe87b6` | public plus `import all` upgrade |
| `tests/pkg/module/Module/ImportedAllPrivateImported.lean` | `89acfc44142153f4fe1cff375e447002face37120f99ca5d7b56c3dda81bc99a` | `import all` activates a nested private import |
| `tests/pkg/module/Module/ImportedImportedAll.lean` | `f07204f755c2e59c459607526c211ead10b3e857d14499b6220468a23b678465` | private `all` data is not automatically re-exported |
| `tests/pkg/module/Module/ImportedPrivateImported.lean` | `1405cfc4796aec3cfdb42477d8ec1cbe77681c1759cd90ad7ad18b72398bc5dd` | an ordinary private import is not public transitive closure |
| `tests/pkg/module/Module/MetaImported.lean` | `5979cb7c690c267cdc45e811dc3c2100f1b5472aecdce1d04441ffd3c3e6adfa` | meta-phase access differs from runtime/public access |
| `tests/pkg/module/Module/NonModule.lean` | `f665225589ddffdfb4e1d9511bed3e0a4fa40842deff776bf451acd4417f4ec7` | a non-module root imports private data |

M2.2.1 must revalidate every listed identity. It may derive new committed
synthetic controls from these rules, but it must not present upstream test
files or this read-only audit as executed M2.2 evidence.

## 3. Two closures, never one blended graph

Every accepted M2.1 source has two distinct projections:

- **raw declared closure** preserves every ordered `Import` occurrence from the
  root and decoded module data, including duplicates and the exact
  `module`/`importAll`/`isExported`/`isMeta` fields;
- **effective load closure** computes which module identities and artifact
  parts Lean would load for one exact root mode, global level, option set,
  provider, and artifact map.

The raw projection answers what was declared. The effective projection answers
what the pinned loader reaches and at which data/IR state. Neither may replace
the other:

- deduplicating raw occurrences loses syntax and modifier evidence;
- taking the raw transitive union overstates actual data reachability;
- keeping only the final effective row loses the path that upgraded it; and
- one provider/profile's effective state cannot close another provider whose
  options, wrapper, setup, or explicit artifacts differ.

`transitive-import` remains the M2.0 edge class for raw module-data adjacency.
Physical `.olean*` and `.ir` loads use the existing `reads`/`artifact-input`
classes plus the effective-state pointer; R1 adds no unreviewed edge type.

## 4. Exact effective-import state machine

### 4.1 Root level

`processHeaderCore` chooses the global `OLeanLevel` from the accepted header
and exact options:

| Root state | Global level |
|---|---|
| non-`module` file | `private` |
| `module` file outside server mode | `exported` |
| `module` file with `Elab.inServer = true` | `server` |

The initial traversal state is `importAll=true`,
`isExported=(globalLevel < private)`, `needsData=true`, and
`needsIRTrans=false`. The two implicit `Init` occurrences added to a
non-`prelude` header remain separate raw occurrences even when their effective
module identity later coalesces.

### 4.2 Per-edge transition

For current state `(a, e, d, t)` and import occurrence `i`, the helper must
reproduce the pinned transition in this order:

```text
d' = d && (i.isExported || a)
a' = (globalLevel == private) || (a && i.importAll)
e' = e && i.isExported
t' = t || (d' && i.isMeta)
needsIR = t' || a' || (globalLevel > exported)
irPhases = all if a'; comptime if !a' && t'; runtime otherwise
```

If both `d'` and `needsIR` are false, the occurrence has no effective child
visit, but the raw edge remains. Otherwise, the loader may need `.olean*`,
`.ir`, or both. Meta propagation is directional: a meta edge can make the
child's descendants IR-reachable, while a meta edge encountered only inside a
non-meta child does not retroactively make its parent meta-reachable.

### 4.3 Join, revisit, and output order

A module identity appears at most once in the final effective module array,
but it may be encountered repeatedly. On a repeated path Lean joins
`importAll`, `isExported`, `needsData`, and `needsIRTrans` with logical OR;
different `irPhases` join to `all`. Newly required data/IR is loaded, and any
state change revisits the module's descendants. R1 therefore requires:

- every encounter and predecessor edge;
- the pre-state, candidate transition, joined post-state, and whether it
  triggered data load, IR load, or recursive revisit;
- the first-discovery and finalization ordinals;
- the final unique module order and `ModuleIdx` mapping;
- final effective modifiers/IR phase and selected data sources; and
- a deterministic event-stream digest as well as a final-state digest.

Sorting a set of module names, stopping at the first visit, or deriving final
state from only one path is invalid. The source algorithm assumes an import
DAG and descends before inserting a newly discovered module. A nontrivial raw
SCC is retained as exact diagnostic evidence but must become a bounded
`cyclic-module-import` decline before simulation; it is not an executable
fixed point and must never recurse without a bound.

## 5. Ordered `.olean` and IR loading

For module-system output, `writeModule` calls `saveModuleDataParts` once with
this exact ordered family:

1. primary `.olean` (`exported` data);
2. `.olean.server` (`server` data); and
3. `.olean.private` (`private` data).

Objects shared with earlier parts are not duplicated. `readModuleDataParts`
therefore accepts only a prefix of the file array produced by that one save;
calling `readModuleData` independently on `.olean.server` or
`.olean.private`, reordering parts, skipping the middle part, or combining
same-named parts from different builds is invalid even when every file exists.

The default non-Lake discovery route:

- requires the primary candidate to exist;
- appends server when it exists;
- probes/appends private only when server exists; and
- passes the complete discovered prefix to `readModuleDataParts`.

Thus a private file without server is an inventoried orphan ignored by the
default loader, not proof of private-data reachability and not necessarily a
Lean rejection. A server file without private yields a valid two-part prefix.
A legacy/non-module single primary part is valid. Independent inventory still
records every neighboring file so absence, orphaning, and unexpected extra
parts cannot disappear.

`.ir` is a separate one-part module-data file with a distinct serialization
base. It may be loaded even when `.olean*` data is not needed, and transitive
meta reachability can require it. M2.2 must resolve and content-identify that
input and record effective IR reads. M2.5 remains responsible for compiler,
native runtime, FFI, and behavioral outcomes; an M2.2 IR-read edge is not a
runtime-support claim.

Lake-provided `ImportArtifacts` may intentionally limit parts and uses its own
conditional `oleanParts` selection. Exact configured arrays remain M2.4
evidence. M2.2 may record the default route and an unbound configured residual,
but it may not substitute default neighbor discovery for a Lake setup array.

## 6. R1 schema amendment

The post-M2.1 authority and helper schemas must add these sealed fields without
removing any M2.2.0 field:

### Per source/provider/profile projection

- root `isModule`, `prelude`, exact options, `Elab.inServer`, global level,
  provider, setup/artifact-map state, and their identities;
- raw occurrence count, raw unique module count, raw SCC partition, raw closure
  digest, and exact cyclic/unreadable residuals;
- effective event count, final module count, data-loaded count, IR-loaded
  count, revisit/upgrade count, final module-order digest, event digest, and
  effective closure digest; and
- zero outcome, pair, performance, population, axis, gate, and parity fields.

### Per effective encounter/final module

- root/source identity, event ordinal, predecessor module/event, raw occurrence
  pointer, and module identity;
- incoming/current/candidate/joined values for `importAll`, `isExported`,
  `needsData`, `needsIRTrans`, and `irPhases`;
- skipped/data/IR/revisit decisions and exact reason;
- resolved primary/server/private/IR family identity, discovered prefix,
  decoded part count/order, part-level `isModule` and import-array identities,
  selected main/server/interpreter data level, and raw evidence pointers;
- final unique module ordinal/`ModuleIdx`, effective modifier row, adjacency and
  closure digests, assurance, provider owners, and residual owner; and
- record/list/projection/aggregate/top-level seals.

Decoded compacted data must be normalized structurally without pointer or mmap
address identity. The raw bytes, filenames, modes, and SHA-256 values remain
authoritative inputs.

## 7. Added control families

R1 adds at least these twelve families to M2.2.0's existing eighteen; M2.2.1
must freeze exact files, expected rows, limits, and process accounting:

1. identical import graph under non-module/private, module/exported, and
   module/server roots;
2. ordinary private import omitted from public transitive data while the raw
   edge remains;
3. public import propagation;
4. `import all` activation of a nested private import without accidental
   re-export;
5. meta import with transitive IR reachability and the inverse non-propagating
   shape;
6. one module reached by ordinary, public, meta, and all paths, forcing at
   least one state upgrade and descendant revisit;
7. the two implicit `Init` raw occurrences coalescing to one final effective
   module row;
8. an IR-only effective child plus missing-required-IR failure;
9. valid one-, two-, and three-part `.olean` prefixes;
10. independently read, reordered, skipped-middle, cross-build, truncated, and
    appended-garbage part failures;
11. private-without-server orphan and server-without-private valid-prefix
    behavior; and
12. raw acyclic diamond versus bounded cyclic-module-import decline.

Controls remain synthetic. They cannot become U2 case nodes, provider
completions, native outcomes, or parity evidence. Existing control family 15
(`private-without-server`) is clarified by R1: the expected default-loader
result is primary-only plus an orphan inventory row, not an invented process
failure.

## 8. Source-first checkpoint sequence

1. **R1 plan:** this document freezes the correction before implementation.
   It derives no M2.1 denominator and runs no Lean/helper process.
2. **M2.2.1 authority:** only after accepted M2.1, bind exact roots, raw
   occurrences, universe, control bytes, global-level variants, process
   formula inputs, limits, evidence root, and authorization digest. All
   observed/effective/credit fields remain zero.
3. **M2.2.2 implementation:** implement the bounded raw-graph decoder,
   cycle detector, ordered part reader, effective fixed-point helper, CLI
   comparator, evidence verifier, and semantic mutation tests. Commit and push
   before rendering authorization.
4. **M2.2.3 attempt:** only an exact later user authorization may run the
   frozen process program. Validate immutable evidence before a separate
   offline promotion.

The original M2.2 process formula remains deferred until M2.1 supplies `S`,
`E`, and the exact output/resource floor. R1 control and helper processes must
be counted explicitly in `helper_controls`/`C`; no new process is hidden behind
the phrase “offline fixed point.” Pure normalization after captured bytes does
not grant permission to invoke Lean again.

## 9. Fail-closed additions

Focused tests must reject at least:

- root `module`/server/global-level drift or use of one level for every source;
- raw/effective closure conflation, raw occurrence loss, or effective module
  duplication;
- incorrect transition order, meta direction, join, phase, revisit, skip, or
  final module ordering;
- first-visit-wins, name-sorted closure, unbounded cycle traversal, or SCC
  erasure;
- an effective data/IR load without exact existing content-addressed inputs;
- independent later-part reads, wrong prefix order/count, missing middle part,
  cross-build mixing, or decoded-part count drift;
- treating an orphan private part as loaded, treating missing private as
  missing exported data, or treating default discovery as configured Lake
  artifacts;
- dropping an IR-only node, laundering missing required IR into success, or
  converting IR reachability into compiler/runtime/native credit;
- pointer/address-sensitive decoded identities or a mutation that changes raw
  bytes without changing normalized evidence; and
- any process/evidence/credit field becoming nonzero at this plan checkpoint.

Every semantic mutation reseals all enclosing rows and lists so the intended
invariant, not a stale hash, causes rejection.

## 10. Acceptance and nonclaims

R1 is accepted as a preregistered correction only when:

1. the exact pinned sources and upstream test identities above reproduce from
   the clean target checkout;
2. M2.2.0 and R1 are both registered in the terminal parity evidence surface;
3. live status/roadmap prose distinguishes raw closure, effective closure,
   ordered part loading, and the downstream configured-provider boundary;
4. complete-parity generation, semantic tests, prose checks, links, JSON,
   whitespace, and relevant documentation gates pass; and
5. M2.1/M2.2 evidence roots remain absent and all M2.2 observation and parity
   counters remain zero.

This plan does not claim that any U2 header parsed, any module resolved, any
`.olean*`/`.ir` file loaded, any fixed point computed, any provider configured,
or any official/Axeyum behavior matched. It does not authorize M2.1 or M2.2.
Complete Lean parity remains at the terminal registry's current zero state and
still requires M2.1 acceptance, M2.2.1-M2.7, M3, every U0-U9 population, every
A0-A11 axis, and every G1-G10 gate at one published revision.
