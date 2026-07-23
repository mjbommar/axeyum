# Lean U2 TL0.6.4 M2 plan — exact dependency and reachability closure

Status: **preregistered; no M2 resolver, dependency edge, configured provider
run, completed case closure, native outcome, pair, or parity credit exists**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[accepted M1 result](lean-u2-native-surface-classification-tl0.6.4-m1-result-2026-07-23.md),
[M1 authority](lean-u2-native-surface-content-v1.json),
[official CI profiles](lean-u2-official-ci-profiles-tl0.6.2-2026-07-22.md),
[execution-evidence policy](lean-execution-evidence-tl0.7.1-2026-07-22.md),
and [complete-parity contract](lean4-complete-parity-contract-2026-07-22.md).

## 1. Decision boundary

M2 must replace source-level signals with exact dependency and reachability
evidence for every one of the 3,723 U2 cases. “Dependency” is not a single
lexical import list. A complete case closure must distinguish:

- parsed Lean header imports and modifiers;
- concrete source and `.olean` resolution under an exact search path;
- transitive imports and extra module uses;
- configured wrapper, runner, hook, and script reachability;
- Lake packages, targets, facets, manifests, caches, generated artifacts,
  external libraries, dynamic libraries, and plugins;
- compiler/interpreter inputs and runtime executables, libraries, files, and
  effects;
- server/RPC requests, documents, versions, edits, cancellation, and project
  setup;
- platform/profile conditionals and branch coverage; and
- unresolved, unavailable, intentionally online, or provider-specific edges.

M2 is complete only when every case/profile variant has a closed typed graph or
an exact reviewed decline. A direct import scan, successful `lean --deps`, one
local Lake build, one runtime trace, or the union of guessed filenames cannot
close M2.

M2 changes no Axeyum parser, kernel, elaborator, tactic, Lake, server, compiler,
runtime, or FFI behavior. It is an evidence-contract step under accepted
[ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md)
and requires no new semantic ADR.

## 2. Frozen inputs

The first implementation must reject drift in:

| Input | SHA-256 | Required validation |
|---|---|---|
| `docs/plan/lean-u2-native-surface-content-v1.json` | `c83d10ce0f0619d4327dbbd7544bd584360cb080d35778ca7798a5f7da17560f` | M1 validator returns no failures |
| `scripts/gen-lean-u2-native-surface-content.py` | `107d699e3ab372ee78e686affcb7cbd940d6ff4ae3446dc29f90d1cd6927fb05` | loaded from exact bytes |
| `docs/plan/lean-u2-native-surface-classification-v1.json` | `89b29bc6820d1d948d5cd4defdd28eb59ddb55a5924a3cf770c0b21282959959` | M0 validator returns no failures |
| `docs/plan/lean-u2-test-authority-v1.json` | `d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e` | U2 registration validator returns no failures |
| `docs/plan/lean-u2-official-ci-profiles-v1.json` | `4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548` | official-profile validator returns no failures |
| `scripts/gen-lean-u2-official-ci-profiles.py` | `4b4b2d0fca8acaee1f90e8a7f143067db6596e6aa7d558e9a877639db878e246` | loaded from exact bytes |
| `docs/plan/lean-execution-evidence-v1.json` | `83fbfeaf6baa4c1bd747ce80bba87a15aaf159bb164a7647cc8e3155282fa05a` | execution-evidence validator returns no failures |
| `scripts/gen-lean-execution-evidence.py` | `025f935111b83e1a3bbc78af50a4ad5671baa370bda02fe94756481e54f55418` | loaded from exact bytes |

The parent logical seals include M1 record
`d10f350d2c01d116538c9b52dcef71f38c473c81a36b3b41f75da4f39b889887`,
file rows
`c52e4c465adbbbcd56577647be14c01bd3364779240661c0dbcfa138a17de13c`,
and case rows
`40190bb4aa7ea1160d5789ff4a98bc81716a51d6ea72f36839e0a43a3268b415`.

Every provider must identify the pinned source checkout, executable, Lake,
toolchain prefix/lib/source roots, platform/architecture, environment, resource
lane, build configuration, and working directory. The observed local released
binary is useful only after a source-first attempt binds it; research
introspection does not create authority or credit.

## 3. Pinned upstream semantics

The dependency contract is grounded in exact upstream sources:

- [`Lean/Shell.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Shell.lean)
  distinguishes `--deps-json`, `--deps`, and `--src-deps`;
- [`Lean/Elab/ParseImportsFast.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Elab/ParseImportsFast.lean)
  shows that `--deps-json` parses headers and preserves module/prelude plus
  `public`, `meta`, and `all` modifiers without resolving artifacts;
- [`Lean/Elab/Import.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Elab/Import.lean)
  shows that `--deps`/`--src-deps` parse direct imports and resolve `.olean` or
  source paths through the active search path;
- [`tests/CMakeLists.txt`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/CMakeLists.txt)
  configures `with_stage${STAGE}_test_env.sh` from `with_env.sh.in` and binds
  stage, source, test, build, script, path, compiler, and linker variables;
- [`Lake/CLI/Help.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/lake/Lake/CLI/Help.lean)
  defines `lake query`, module `deps`, artifact facets, and JSON output; and
- [`Lake/Build/Module.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/lake/Lake/Build/Module.lean)
  constructs module setup from direct import artifacts, transitive precompile
  imports, external libraries, dynamic libraries, plugins, options, and
  platform traces.

These sources prohibit collapsing header parsing, path resolution, Lake setup,
or observed runtime behavior into one undifferentiated “dependency” field.

## 4. Typed graph contract

M2 freezes these node classes:

| Node class | Required identity |
|---|---|
| source | normalized path, mode, blob, bytes, SHA-256, source universe |
| Lean module | canonical module name, package, source and artifact identities |
| generated file | generator/configuration, substitutions, output bytes/mode/hash |
| build artifact | facet, path, bytes/hash, producer command and inputs |
| package/project | root, config language/file, manifest/lock, package ID/revision |
| executable/tool | realpath, bytes/hash, version, commit, target, dynamic identity |
| library/plugin | logical name, resolved path, bytes/hash, linkage/load role |
| request/document | method, normalized payload, document URI/version/content identity |
| runtime file/effect | path or normalized effect class, before/after identity |
| external/network | endpoint/protocol/pin/cache policy and observed/unobserved state |
| platform/profile | official context, provider, OS/arch/tier, configuration and lane |

Edges use stable classes:

1. `header-import` — module name and exact `public/meta/all/exported` modifiers;
2. `resolved-source` and `resolved-olean` — direct search-path resolution;
3. `transitive-import` and `extra-module-use`;
4. `configures`, `sources`, `executes`, `reads`, `writes`, and `generates`;
5. `package-dependency`, `target-facet`, `artifact-input`, and `cache-input`;
6. `links-static`, `links-dynamic`, `loads-dynlib`, `loads-plugin`, and `ffi-abi`;
7. `request-document`, `request-project`, `edit-version`, and `cancels`;
8. `runtime-input`, `runtime-output`, `runtime-effect`, and `network-edge`; and
9. `conditional-on-profile`, `conditional-on-platform`, and
   `conditional-on-branch`.

Every edge records origin node, destination node, edge class, case/profile
owners, direct versus transitive status, resolver ID/version, evidence route,
raw evidence span/record, assurance, observed branch state, and record seal.
Graphs must be deterministic, acyclic where the edge class requires it, and
cycle-preserving for legitimate package/module strongly connected components.

## 5. Evidence and assurance states

An edge has exactly one evidence state:

- `declared-static` — exact syntax/config declaration, not reachability;
- `resolved-static` — exact resolver under a bound search/configuration path;
- `configured` — retained configured/generated artifact or Lake setup output;
- `observed-runtime` — retained process evidence shows the edge was exercised;
- `conditional-not-taken` — branch registered and retained but not observed;
- `provider-unavailable` — required official provider/profile has no valid run;
- `intentionally-online` — network dependency is part of the test contract but
  no unauthorized access occurred;
- `declined` — reviewed stable reason and owner; or
- `unresolved` — provisional and M2-incomplete.

Static declarations cannot become observed runtime edges. One provider cannot
close another provider's platform-specific library or path. An aggregate union
must retain variant ownership; an intersection must not erase conditional
requirements.

## 6. Dependency-resolution program

M2 is divided into separately source-first submilestones.

### M2.0 — provider and graph contract

Implement the schema, sealed registries, parent projections, provider/attempt
contract, empty graph, mutation tests, and zero-credit generated summary. No
external process runs. Exit: all 3,723 cases exist with every closure
`not-run`, and the next attempt identity is frozen.

### M2.1 — exact Lean header graph

Run the pinned released binary's `--deps-json` in bounded batches over every
applicable tracked `.lean` source. Retain command, input order, raw JSON,
per-file parse errors, module/prelude status, and modifiers. Cross-check a
frozen control matrix with the full parser and M1 active-token evidence.

This closes only direct header declarations. It creates no path, artifact,
transitive, Lake, runtime, or native-support claim.

### M2.2 — source/artifact resolution and transitive import graph

Bind the exact `LEAN_PATH`, source search path, released prefix/lib/source
trees, configured wrapper, working directory, and provider. Use `--deps` and
`--src-deps` for direct path resolution, then derive transitive closure from a
complete content-addressed module universe. Preserve duplicate imports with
different modifiers and distinguish source-absent/artifact-only modules.

Extra module uses, private/server artifacts, precompiled imports, and package
boundaries remain separate. Resolution failure is a row, not disappearance.

### M2.3 — runner and generated-artifact closure

Materialize the configured stage wrapper through the exact pinned CMake inputs
or consume a retained official build artifact. Bind all substitutions and
source/includes. Derive runner/hook/control-marker/script edges. Shell semantics
that cannot be proven statically require a registered observed trace; lexical
command candidates cannot become `executes` edges.

### M2.4 — Lake/project closure

For every directory/project case, freeze an isolated source copy, offline/
online policy, package overrides, configuration options, manifest/cache state,
and provider. Use pinned `lake query ...:deps --json`, `lake setup-file`, or an
equivalent retained Lake API result to capture module import artifacts,
external/dynamic libraries, plugins, options, targets, and facets. Query/build
effects use TL0.7 completion-last evidence and never mutate the pinned source
checkout.

Tests whose purpose is online resolution retain network edges but do not access
the network without a separately authorized source-first attempt.

### M2.5 — compiler/runtime/FFI closure

Combine compile/interpreter commands, generated C/LLVM/native artifacts,
linker inputs, load paths, plugins, `@[extern]`/`@[implemented_by]` declarations,
foreign sources, and observed process/file effects. A provisional M1 FFI signal
becomes reachable only through a complete case/profile path. Platform library
variants stay separate.

### M2.6 — editor/RPC closure

Bind request harness, normalized payloads, documents, versions, edits,
cancellation, project setup, server executable, and observed transcript order.
Expected-output sidecars are observables, not request evidence unless the
request harness binds them.

### M2.7 — full merge and review handoff

Merge all case/profile graphs, compute exact direct/transitive surface
requirements, classify every residual, and publish a deterministic M3 review
queue. M2 closes only when every required variant is `resolved-static`,
`configured`, `observed-runtime`, `conditional-not-taken` with complete branch
registration, or reviewed `declined`; `unresolved` and `provider-unavailable`
prevent completion.

## 7. Process and evidence policy

No broad command may run before its attempt plan and implementation are
committed and pushed with local/tracking/remote equality. Each process attempt
binds:

- exact executable and recursive dynamic identity;
- source/work/evidence roots and clean-state hashes;
- command, cwd, environment allowlist, search paths, configuration, provider,
  platform, resource lane, timeout, and network policy;
- selected case/file/profile denominator and no-retry identity;
- raw stdout/stderr/JSON/traces and generated artifacts;
- typed terminal state and completion-last manifest; and
- zero execution/pair/performance/parity credit unless a later authority
  explicitly satisfies its independent gates.

Read-only dependency tools are still external processes. A `--deps-json` batch
is not a Lean test outcome. A Lake query may build targets and therefore must
use an isolated worktree/copy and qualified artifact store. Runtime tracing
must account for tracer perturbation and cannot replace the uninstrumented
official outcome.

## 8. Canonical authority

The planned authority family is:

- `docs/plan/lean-u2-native-dependency-v1.json` — registries, providers,
  attempts, nodes, edges, closures, case/profile rows, residuals, and seals;
- `docs/plan/generated/lean-u2-native-dependency.json` and `.md` — bounded
  summaries;
- `scripts/gen-lean-u2-native-dependency.py` — offline validator and optional
  reproducer; and
- focused tests under `scripts/tests/`.

Large raw process evidence belongs under completion-last evidence roots, not in
the summary authority. The authority stores exact identities and retained
pointers. Canonical JSON remains ordinary Git-trackable data; any representation
above 50,000,000 bytes requires a preregistered lossless compaction rather than
silent omission or history rewriting.

Per-case/profile rows retain M0/M1 identities, provider variants, direct graph
roots, graph closure digest, exact surfaces, edge/evidence state counts,
declines, unresolved residuals, and non-crediting outcome fields.

## 9. Fail-closed invariants

Focused tests must reject at least:

- drift in any parent authority, validator, target, population, case/file row,
  surface registry, official profile, or execution lane;
- missing, duplicate, reordered, or extra case/profile/provider variants;
- unbound executable/search path/configuration/provider/platform identity;
- a `--deps-json` row presented as source/artifact or transitive resolution;
- lost import modifiers, implicit prelude/Init mistakes, duplicate collapse,
  module-name/path aliasing, or source/`.olean` disagreement;
- a generated wrapper substituted for its template, or a template presented as
  configured bytes;
- a shared-support, lexical candidate, expected output, or filename promoted
  without reachability;
- a Lake target/facet/library/plugin/cache edge omitted or credited across a
  different package/profile/platform;
- an FFI signal promoted without a reachable declaration/build/link/load path;
- a request/response sidecar treated as an executed RPC request;
- a conditional branch silently treated as absent, or one provider used to
  close another provider's variant;
- an unauthorized network edge, source-tree mutation, unregistered process,
  retry, incomplete evidence root, or post-completion mutation;
- any native support/decline, official/Axeyum outcome, pair, performance,
  complete population/axis/gate, or parity credit not independently earned;
  and
- node, edge, graph, case, aggregate, record, or generated-report seal drift.

Mutation tests must reseal enclosing structures so the intended invariant is
exercised.

## 10. Acceptance and stop conditions

M2 as a whole is accepted only after:

1. each submilestone is separately source-first, implemented, tested, pushed,
   executed where authorized, and documented;
2. every 3,723-case/profile variant has complete typed closure or reviewed
   decline with no `unresolved` or `provider-unavailable` row;
3. all generated/configured/runtime evidence validates under TL0.7;
4. all local/CI authority, complete-parity, parity-doc, link, Python/shell, and
   whitespace gates pass, with unrelated historical failures named exactly;
5. M1 signal counts and evidence remain unchanged except through an explicit
   correction; and
6. all outcome, pair, performance, population, axis, gate, and parity counters
   remain zero unless separately supported by their own authorities.

Stop before a process if executable/search/configuration identity is unclear,
the source tree is dirty, the evidence root exists, the network policy is not
closed, or local/tracking/remote refs differ. Stop a submilestone without
promotion if any required edge needs guessing, a provider is unavailable, or a
branch cannot be registered.

## 11. Nonclaims and continuation

This plan and every partial M2 result do not claim that Axeyum implements or
runs any dependency, Lean case, project, server request, compiler path, runtime,
or FFI edge. They do not convert 66 local official outcomes into native pairs.

After accepted M2, M3 must review all 3,723 rows, resolve owner/decline policy,
and accept TL0.6.4. Only accepted TL0.6.4 plus matching complete official and
native execution may allow TL0.6.5 to form paired semantic rows. The unqualified
Lean parity switch remains closed until every U0-U9, A0-A11, and G1-G10 gate is
satisfied at one published revision.
