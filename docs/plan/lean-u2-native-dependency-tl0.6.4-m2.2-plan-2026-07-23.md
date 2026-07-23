# Lean U2 TL0.6.4 M2.2 plan — exact module/source/artifact resolution

Status: **preregistered semantics only; no M2.2 input authority or process is
authorized before accepted M2.1 evidence**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[M2 program](lean-u2-native-surface-classification-tl0.6.4-m2-plan-2026-07-23.md),
[accepted M2.0 result](lean-u2-native-surface-classification-tl0.6.4-m2.0-result-2026-07-23.md),
[M2.1 plan](lean-u2-native-dependency-tl0.6.4-m2.1-plan-2026-07-23.md),
and [M2.1 pre-execution result](lean-u2-native-dependency-tl0.6.4-m2.1-pre-execution-2026-07-23.md).

## 1. Objective and dependency boundary

M2.2 will replace every accepted M2.1 declared-only module stub with an exact,
provider-owned source and artifact resolution row or a typed unresolved/
declined row. It will then derive the complete transitive import graph of the
bound module universe without treating a printed candidate filename as proof
that a file exists.

This document freezes resolver semantics, schemas, controls, process formulas,
evidence, and non-credit rules before M2.1 executes. It cannot freeze M2.2's
exact import-occurrence denominator or process count yet because those values
must be derived from accepted fast/full M2.1 rows. After M2.1 is accepted, a
separate input-authority checkpoint must bind the exact ordered occurrences,
unique module names, parse/error partitions, search roots, universe rows,
controls, process count, resource limits, and authorization digest before any
M2.2 process runs.

M2.2 closes only:

- module-name to candidate-path behavior under exact search paths;
- independently verified source/primary `.olean` existence and identity;
- optional `.olean.server`, `.olean.private`, `.ir`, and `.ilean` identities;
- the direct and transitive imports stored in the content-addressed module
  universe; and
- exact failures, shadows, aliases, source-only, artifact-only, and
  provider-unbound residuals.

M2.2 does not configure the test wrapper, infer Lake package/facet ownership,
build a missing artifact, execute a test, load a plugin/library, observe
runtime/FFI reachability, send a server request, establish native support, or
create an official/Axeyum pair. Those remain M2.3-M2.7 and M3 work.

## 2. Pinned upstream semantics

The implementation must bind and revalidate these exact Lean 4.30 sources:

| Source | SHA-256 | Frozen rule |
|---|---|---|
| `src/Init/System/FilePath.lean` | `23e96ff67d94c86193b6ef6345a01c5b45dbc4bb68984c8b6bbeef06ea09d937` | search-path parsing preserves order, duplicates, relative paths, and empty components |
| `src/Lean/Util/Path.lean` | `59fd27c802b78cd156d7463a2568d1fd73e24d73f0e1ec7035532a632437217e` | module-to-path conversion, first-prefix selection, builtin/env path order, source path, and error text |
| `src/Lean/Elab/Import.lean` | `43dee2c40840f9efc6abb4d41f428f4383911249f9b70be1169298fbc0026fb3` | `--deps` uses `findOLean`; `--src-deps` uses `getSrcSearchPath` plus `findLean` |
| `src/Lean/Environment.lean` | `54f6ca1b7a49a52ff2d9fadb4ef544745584961d5e091ce6dd998228dbd2b253` | actual import requires the primary `.olean`, opportunistically loads server/private parts, and reads transitive module data |
| `src/Lean/Setup.lean` | `452c19cab80687c56fbf90c3b9ee2627d66c40a49c15bab710d507dd4453df5a` | ordered import/module artifact schemas and `.olean` part ordering |
| `src/Lean/Shell.lean` | `0de8cdbadedf418ccfb051ec8cb2c7bcd3bb6fef524c16962c72e4acfbf64d54` | dependency modes consume exactly one source filename and print direct rows only |

Primary online references are the pinned
[`Lean/Util/Path.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Util/Path.lean),
[`Lean/Elab/Import.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Elab/Import.lean),
[`Lean/Environment.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Environment.lean),
and the official
[Source Files and Modules reference](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/).
The reference explains the user-facing dot-to-directory rule. The pinned
implementation remains authoritative for this exact target when current
documentation differs.

### 2.1 Candidate selection is not existence

For extension `ext` and module `A.B.C`, `SearchPath.findWithExt` scans roots in
order and selects the first root `p` for which either `p/A` is a directory or
`p/A.ext` exists. It then returns `p/A/B/C.ext`. It does **not** check whether
that full returned path exists. Consequently:

- `lean --deps` can print a nonexistent nested `.olean` and exit successfully;
- `lean --src-deps` can print a nonexistent nested `.lean` and exit
  successfully;
- an early root containing only the top-level prefix shadows a later root that
  contains the complete target; and
- an unknown-prefix error differs from a selected-prefix/missing-leaf row.

M2.2 therefore records `prefix-selected-candidate` separately from
`existing-regular-file`. A `resolved-source` or `resolved-olean` edge requires
the latter plus exact content identity. CLI stdout alone cannot satisfy it.

### 2.2 Search-path order and environment states

For the released-toolchain route with no setup file:

- artifact search uses initial roots, then parsed `LEAN_PATH`, then the builtin
  `<prefix>/lib/lean` root;
- source search uses parsed `LEAN_SRC_PATH`, then
  `<prefix>/src/lean/lake`, then `<prefix>/src/lean`;
- `LEAN_PATH`/`LEAN_SRC_PATH` **absent** differs from present-but-empty: the
  latter parses to one empty relative root and can expose the working
  directory;
- duplicate, relative, dot/dot-dot, and symlinked roots are not normalized away
  by search-path parsing; and
- Linux case sensitivity, filesystem type, working directory, and every raw
  and resolved root identity are provider facts.

The M2.2 input authority must use an exact environment allowlist and represent
absence explicitly. It may not serialize absent variables as empty strings.

### 2.3 Actual import artifact behavior

`findOLeanParts` first requires the selected primary `.olean` to exist. It then
loads `.olean.server` if present and `.olean.private` only after a server part
is present. Lake may instead provide an explicit ordered `ImportArtifacts`
array, but that is configured evidence deferred to M2.4. M2.2 records all
available parts and the default-import sequence; it does not pretend that
`--deps` printed those parts.

The transitive graph comes from independently read and validated module data,
not recursive filename guessing. Import order, duplicates, `public`, `meta`,
and `all` modifiers remain distinct occurrences throughout direct and
transitive projections.

## 3. Released-toolchain research floor

Read-only pre-plan inspection of the exact released prefix
`/tmp/axeyum-codex-lean-20260722/elan-home/toolchains/leanprover--lean4---v4.30.0`
found:

| Universe fact | Research value |
|---|---:|
| primary `.olean` files | 2,302 / 338,308,776 bytes |
| `.olean.server` files | 2,300 / 29,806,176 bytes |
| `.olean.private` files | 2,300 / 1,256,385,352 bytes |
| `.ilean` files | 2,302 / 81,186,861 bytes |
| released `.lean` source files | 2,302 / 26,823,285 bytes |
| `src/lean/lake` source files | 158 / 1,008,180 bytes |
| source/artifact module-name set | 2,302 each; zero duplicates or one-sided names |
| primary artifacts without server/private parts | `LeanChecker`, `Leanc` |
| symlinks among the listed file classes | 0 |

These values are a preregistration floor, not M2.2 evidence. The later input
authority must rederive each count, mode, byte size, path, realpath, and SHA-256
from the exact prefix and fail closed on drift. Equal module-name sets do not
prove that source and artifact semantics agree or that any U2 case reaches a
module.

## 4. Resolver and universe records

Every accepted M2.1 import occurrence gets a sealed resolver row containing:

- M2.1 source/header-edge identity, occurrence index, raw-record pointer,
  module name, origin, and modifiers;
- provider, executable, target, prefix, working directory, platform, search
  kind, extension, and resolver-source identities;
- exact ordered search roots with raw spelling, origin (`initial`, environment,
  or builtin), existence, lstat type/mode, symlink target, normalized path,
  realpath where defined, and record digest;
- for every root, the top-level prefix probe and full candidate path rather
  than only the selected root;
- selected-root ordinal/reason, candidate path, normalized path, full-path
  existence/type, and all later shadowed candidates;
- primary file mode, bytes, SHA-256, Git/toolchain ownership, or exact failure
  class;
- optional server/private/IR/ILEAN part identities and the default import-part
  sequence;
- source/artifact agreement state, including one-sided, different-root,
  different-module-name, and provider-unbound states;
- assurance (`resolved-static` only after full file validation), evidence
  pointer, owner variants, residual/decline owner, and row seal; and
- zero outcome, pair, performance, population, axis, gate, and parity fields.

Stable resolution classes are:

1. `resolved-existing-regular`;
2. `unknown-prefix`;
3. `prefix-selected-leaf-missing`;
4. `prefix-selected-nonregular`;
5. `source-only`;
6. `artifact-only`;
7. `source-artifact-root-disagreement`;
8. `shadowed-by-earlier-prefix`;
9. `ambiguous-provider-or-package`;
10. `module-data-invalid-or-unreadable`; and
11. `provider-unbound`.

Classes 2-11 remain unresolved or reviewed declines. They cannot silently
disappear from closure totals.

The module-universe row additionally retains module name, source and all
artifact identities, ordered direct imports from validated module data,
module-system state, package identity when known, adjacency digest, strongly
connected-component identity, and transitive-closure digest. Cycles are
retained and reviewed; a topological algorithm must not erase them.

## 5. Exact control matrix

The post-M2.1 input authority must freeze control bytes and expected rows for:

1. top-level source and artifact success;
2. nested source and artifact success;
3. unknown top-level prefix;
4. known directory prefix with missing nested leaf;
5. known `Prefix.ext` file with missing nested leaf;
6. source-only module;
7. artifact-only module;
8. an early prefix-only root shadowing a later complete target;
9. duplicate roots and two complete shadowed targets with different bytes;
10. absent versus present-empty `LEAN_PATH` and `LEAN_SRC_PATH`;
11. relative, dot, dot-dot, and symlinked roots;
12. regular-file, directory, symlink, FIFO/nonregular, unreadable, and dangling
    candidate boundaries without blocking the test harness;
13. primary `.olean` with both server/private parts;
14. primary `.olean` with no optional parts, using the released `LeanChecker`
    or `Leanc` legacy shape;
15. server part without private, and private-without-server negative shapes;
16. source/artifact module-set or root disagreement;
17. ordered duplicate imports with distinct modifiers; and
18. malformed/unreadable module-data and transitive-cycle fixtures.

Controls live under a temporary or committed synthetic root and cannot become
U2 module nodes, case dependencies, declines, or outcomes. Expected CLI
candidate behavior and independent existence behavior are asserted separately.

## 6. Source-first implementation sequence

M2.2 is split into non-overlapping checkpoints:

### M2.2.0 — this semantics plan

Freeze the upstream rules, schemas, controls, process formula, acceptance, and
nonclaims. No M2.2 input is derived and no resolver process runs.

### M2.2.1 — post-M2.1 input authority

After accepted M2.1 only, publish:

- the exact ordered successful/error header rows and import occurrences;
- the unique module-name denominator and ownership multiplicities;
- exact source/artifact roots and the content-addressed released universe;
- exact controls and expected results;
- process specs, counts, limits, evidence root, retry budget zero, and logical
  authorization digest; and
- all observed/resolved/transitive/credit counters at zero.

This checkpoint performs filesystem inventory and offline derivation only. It
does not invoke Lean or read module data through an executable.

### M2.2.2 — runner and verifier

Implement and test:

- a bounded helper that reproduces the pinned resolver per occurrence and
  reads module metadata per content-addressed universe row;
- exact `lean --deps` and `lean --src-deps` observations for every M2.1
  successfully parsed corpus source, not only a sample;
- the full synthetic control matrix;
- completion-last evidence, typed expected semantic failures, and offline
  comparison/promotion; and
- mutation tests that reseal enclosing structures.

The implementation and tests must be committed and pushed before rendering a
new exact authorization digest. No process is authorized by this plan.

### M2.2.3 — one authorized attempt and offline promotion

After explicit user authorization for the exact rendered command, execute the
frozen process program once, validate immutable evidence, and stop. Promotion
is a later offline checkpoint; it must not modify the evidence runner whose
bytes were authorized.

## 7. Process formula and failure semantics

Let `S` be the exact count of accepted M2.1 corpus sources with agreed fast/full
headers, `E` the retained paired-error rows, `U` the content-addressed module
universe size, `B` the frozen helper batch size, and `C` the exact CLI control
process count. M2.2.1 freezes their values and the process total:

`P = identity_preflights + 2*S + ceil(U/B) + helper_controls + C`

The `2*S` term is one `--deps` and one `--src-deps` process per successful
source. Paired M2.1 errors remain explicit `header-unavailable` rows and do not
receive invented resolution processes. Every process is sequential and has no
retry.

A CLI nonzero exit caused by a registered resolution failure is a typed row,
not permission to abort or retry the remaining denominator. Preflight,
identity, resource, evidence-store, unexpected signal/exit, schema, inventory,
or helper/CLI disagreement failures stop the attempt without completion.

Each process binds exact command, cwd, environment including absent variables,
stdin, limits, start/end/terminal state, raw streams, resource counters, and
inventory. Stdout/stderr are streamed to bounded retained files. Whole process
groups are reaped. The evidence root is new, completion is last, and network
access is forbidden.

Resource values and the exact process count are intentionally deferred to the
post-M2.1 authority; choosing them before `S`, output sizes, and helper memory
are known would be guesswork. They may not be selected adaptively after an
attempt starts.

## 8. Evidence normalization and transitive closure

For each CLI row, normalization retains stdout line order and multiplicity,
stderr, exit class, and the corresponding M2.1 occurrence mapping. A line count
or candidate path is compared with helper output but never used as existence
proof.

For each universe module, the helper retains exact raw module metadata and
ordered imports. Offline promotion:

1. validates every raw pointer and file identity;
2. joins each direct occurrence to a resolver row without deduplication;
3. creates `resolved-source`/`resolved-olean` edges only for existing regular
   content-addressed files;
4. creates ordered `transitive-import` edges from validated module metadata;
5. computes closure over module identities while preserving occurrence and SCC
   records;
6. keeps optional parts and explicit Lake artifacts separate from the primary
   `.olean`; and
7. publishes every residual and provider owner with zero native/parity credit.

The released default route cannot close official provider variants whose
configured wrapper/search roots differ. Those rows remain provider-unbound for
M2.3/M2.4 rather than borrowing the local result.

## 9. Fail-closed tests

Focused tests must reject at least:

- drift in M1, M2.0, accepted M2.1, this plan, target sources, toolchain,
  prefix, executable, platform, filesystem, environment, cwd, or roots;
- absent/empty environment collapse, root reordering/deduplication,
  normalization before selection, or symlink/relative-path erasure;
- treating a prefix-selected candidate as an existing file;
- fallback to a later complete root after an earlier prefix-only match;
- missing/nonregular/unreadable primary files or invalid part ordering;
- source/artifact/universe module-name mismatch or duplicate collapse;
- CLI/helper line, order, multiplicity, candidate, error, or raw-pointer drift;
- malformed/unreadable module metadata, dropped modifiers, missing transitive
  rows, erased cycles, or unstable SCC/closure digests;
- a control row promoted into a case graph;
- a local released route used to close an unbound official provider;
- an expected resolution failure laundered into an empty success or an
  unexpected process failure accepted as data;
- process count/order, command, limit, retry, completion, inventory, or
  post-completion mutation drift; and
- any native outcome, pair, performance, complete population/axis/gate, or
  parity credit.

Mutation tests reseal the row, containing list, evidence projection, graph,
aggregate, and top-level authority so semantic checks—not stale hashes—fail.

## 10. Acceptance and stop conditions

M2.2 is accepted only if:

1. M2.1 is accepted first with a complete exact header denominator;
2. plan, input authority, runner, attempt, and promotion are separate pushed
   checkpoints with local/tracking/remote equality;
3. every accepted M2.1 occurrence has exact source/artifact resolution or a
   typed unresolved/reviewed decline, with no dropped row;
4. every universe module and direct/transitive edge has exact immutable
   evidence and deterministic closure;
5. CLI candidate behavior, helper behavior, and independent filesystem checks
   agree under the frozen semantics, including expected missing-leaf controls;
6. official provider variants remain unclosed unless their exact search/setup
   identity is independently bound;
7. focused, aggregate, complete-parity, parity-prose, link, Python/Lean, shell,
   whitespace, and relevant CI gates pass; and
8. all outcome/pair/performance/population/axis/gate/parity counters remain
   zero.

Stop before execution if M2.1 is not accepted, any denominator/root/provider/
limit is provisional, refs differ, a source/prefix is dirty, the evidence root
exists, network policy is not closed, or tests fail. Stop without promotion on
unexpected process behavior, raw/schema/inventory drift, helper/CLI
disagreement, missing module data, or any guessed resolution.

## 11. Nonclaims and continuation

This plan records no M2.2 process, source/artifact resolution, transitive edge,
configured provider, official/Axeyum outcome, pair, performance row, completed
population/axis/gate, or parity credit. The research inventory and official
documentation do not change those zeros.

After accepted M2.2, M2.3 must bind configured wrappers and generated
artifacts; M2.4 must bind Lake packages, targets, facets, manifests, caches,
explicit `ImportArtifacts`, libraries, and plugins. M2.5-M2.7 and M3 remain
mandatory. Complete Lean parity remains disabled until every U0-U9, A0-A11,
and G1-G10 requirement is evidenced at one published revision.
