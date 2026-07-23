# Lean U2 TL0.6.4 M0 plan — native-surface contract and harness-floor census

Status: **preregistered; no classifier, classification authority, native
execution, paired outcome, or parity credit exists**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[complete-parity contract](lean4-complete-parity-contract-2026-07-22.md),
[system implementation plan](lean-system-implementation-plan-2026-07-21.md),
and accepted [U2 registration authority](lean-u2-test-authority-2026-07-22.md).

## 1. Decision boundary

TL0.6.4 must classify **all 3,723 registered U2 cases**, not a convenient
sample, by the native Axeyum surfaces needed to reproduce each official
observable. It must retain stable owners and decline codes without silently
delegating a missing surface to official Lean or crediting a lower K/A profile.

M0 establishes the complete case-indexed contract and derives a conservative
**harness floor** from the already content-bound registration authority. It
does not inspect source tokens, resolve Lean imports, execute a binary, or
decide whether Axeyum supports a case. Every M0 case remains:

- `classification_state = harness-floor`;
- `content_refinement = not-run`;
- `module_dependency_closure = not-run`;
- `native_outcome = not-run`; and
- ineligible for paired, performance, population, axis, gate, or parity credit.

The floor is useful because it prevents category loss immediately: a compiler
case cannot be counted as elaboration-only, a server case cannot be counted as
batch elaboration, and an expected rejection cannot be counted as an ordinary
positive. It is deliberately insufficient for TL0.6.4 completion. M1 must
inspect every pinned source/support closure; M2 must derive exact module and
runtime dependencies; M3 must review the resulting full-population authority
before TL0.6.5 may form native pairs.

This is an evidence-contract step under accepted
[ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md).
It changes no Lean parser, importer, kernel, tactic, compiler, server, Lake, or
public solver behavior, so it requires no new semantic ADR.

## 2. Frozen inputs and upstream interpretation

The implementation must reject physical or semantic drift in these committed
inputs before deriving a row:

| Input | SHA-256 | Required validation |
|---|---|---|
| `docs/plan/lean-u2-test-authority-v1.json` | `d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e` | `gen-lean-u2-test-authority.py::validate_manifest` returns no failures |
| `scripts/gen-lean-u2-test-authority.py` | `2c173c2621c374179ee346aa8cc710a84e8c37792b2ead25d4e80f8144ad34ba` | loaded from the frozen bytes, not a substitute module |

The authority binds:

- case-list digest
  `37050cfb25f0ecfa2256ccb9516124092fc611af5d7be94cce1e9e0745745cd3`;
- 7,004-file content-list digest
  `f2c8b9c9276ac85dfef7d8e4fc32abe2350a3ae9e659a9a5795cba7f0390631f`;
- 3,678 default and 3,723 full-Lake registrations; and
- sixteen observed `(family, kind)` pairs with normalized commands,
  properties, primary files, sidecars, output policies, and support scopes.

The interpretation is grounded in pinned upstream sources:

- [`tests/README.md`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/README.md)
  defines test directories versus piles and the compile, elaboration,
  expected-failure, server, Lake, miscellaneous, and package families;
- [`tests/CMakeLists.txt`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/CMakeLists.txt)
  registers those piles/directories and the conditional full-Lake population;
- [`tests/compile/run_test.sh`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/compile/run_test.sh)
  shows that compile cases may compile, link, execute, and interpret;
- [`tests/elab/run_test.sh`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/elab/run_test.sh)
  defines successful elaboration/output behavior;
- [`tests/elab_fail/run_test.sh`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/elab_fail/run_test.sh)
  requires a failing Lean exit; and
- [`tests/server_interactive/run_test.sh`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/server_interactive/run_test.sh)
  routes interactive cases through the pinned request harness.

These sources justify only the M0 family floor. They do not prove the exact
constructs, tactics, imports, FFI calls, runtime effects, or RPC methods used by
an individual case.

## 3. Surface registry and dependency DAG

M0 freezes ten stable surface IDs. Each surface record carries its owner,
complete-parity axes, current capability state, and a decline code suitable for
a future explicit Axeyum decline. A decline code is metadata, not an observed
case outcome.

| Surface ID | Direct meaning | Owner | Axes | Stable decline code |
|---|---|---|---|---|
| `kernel-import` | checked core declarations, reductions, imports, serialization | TL1/TL2 | A1/A2/A9 | `native-surface/kernel-import` |
| `parser-macro` | source parsing, syntax extensions, macro expansion | TL6 | A3 | `native-surface/parser-macro` |
| `elaborator` | elaboration, unification, commands, diagnostics | TL4 | A4 | `native-surface/elaborator` |
| `tactic-meta` | goals, tactics, metaprograms, generated proof terms | TL5/TL9.11 | A5/A9 | `native-surface/tactic-meta` |
| `modules-lake` | modules, artifacts, packages, dependency/cache behavior, Lake | TL7 | A2/A6/A11 | `native-surface/modules-lake` |
| `editor-rpc` | server snapshots, LSP/RPC requests, cancellation, stale-state behavior | TL8 | A7 | `native-surface/editor-rpc` |
| `compiler-runtime` | evaluation, code generation, linking, execution, effects | TL9 | A8/A11 | `native-surface/compiler-runtime` |
| `ffi` | extern declarations, ABI/linkage, native library interaction | TL9.10 | A8/A11 | `native-surface/ffi` |
| `toolchain-cli` | native command/install/package workflow behavior not reducible to one semantic layer | TL0/TL7/TL9/TL10 | A11 | `native-surface/toolchain-cli` |
| `adversarial` | expected rejection, malformed input, resource, or stale-state dimension layered on another surface | U8/component owner | A0-A11 as applicable | `native-surface/adversarial` |

The direct-to-closure DAG is:

```text
kernel-import
parser-macro
elaborator       -> parser-macro, kernel-import
tactic-meta      -> elaborator
modules-lake     -> elaborator
editor-rpc       -> modules-lake, elaborator
compiler-runtime -> elaborator
ffi              -> compiler-runtime
toolchain-cli
adversarial
```

Closure is transitive, deterministic, duplicate-free, and reported in registry
order. `adversarial` is an orthogonal requirement marker, not evidence that the
input is malicious or that a security campaign ran. `toolchain-cli` exists
because A11 behavior would otherwise disappear from the TL0.6.4 denominator.

Current capability states are descriptive and non-crediting:
`kernel-import = partial`, `adversarial = partial-cross-cutting`, and every
other surface is `not-implemented-native`. M0 must not infer a case-specific
support or decline result from these states.

## 4. Frozen family floor

Rules match exact `(family, kind)` pairs, with the two named directory
overrides below. Unknown families, kinds, IDs, or uncovered cases fail closed.

| Family/kind | Direct required surfaces | Rationale |
|---|---|---|
| `bench/directory` | `tactic-meta` | MVCGen symbolic benchmark exercises meta/tactic execution |
| `compile/pile` | `compiler-runtime` | compile, link, execute, and optional interpreter path |
| `compile_bench/pile` | `compiler-runtime` | same semantic floor as compile; timing is separate |
| `doc-examples/pile` | `elaborator` | ordinary source acceptance/output |
| `docparse/pile` | `parser-macro`, `compiler-runtime` | doc parser input consumed by a Lean runtime harness |
| `elab/pile` | `elaborator` | successful elaboration/output |
| `elab_bench/pile` | `elaborator` | elaboration floor; performance remains unmeasured |
| `elab_fail/pile` | `elaborator`, `adversarial` | expected rejection rather than success |
| `lake/lake-directory` | `modules-lake` | script-defined Lake/project behavior |
| `lint/lint` | `toolchain-cli` | repository/test-suite lint command behavior |
| `misc/pile` | `toolchain-cli` | heterogeneous CLI scripts; M1 must refine individually |
| `pkg/directory` | `modules-lake` | package/module script behavior |
| `server/pile` | `editor-rpc` | server request workflow |
| `server_interactive/pile` | `editor-rpc` | interactive request/transcript workflow |

Exact overrides:

| Case ID | Direct required surfaces |
|---|---|
| `../doc/examples/compiler` | `compiler-runtime` |
| `misc_dir/plugin` | `modules-lake`, `tactic-meta` |
| `misc_dir/server_project` | `modules-lake`, `editor-rpc` |

The authority contains eight `doc-examples` cases, two `misc_dir` cases, and no
other IDs eligible for override. An override may replace the family floor only
when its exact ID, family, kind, and case seal match the frozen parent.

## 5. Canonical authority and generated reports

The implementation commit will add:

- `scripts/gen-lean-u2-native-surface-classification.py`;
- `scripts/tests/test_lean_u2_native_surface_classification.py`;
- `docs/plan/lean-u2-native-surface-classification-v1.json`;
- `docs/plan/generated/lean-u2-native-surface-classification.json`; and
- `docs/plan/generated/lean-u2-native-surface-classification.md`.

The canonical authority must retain:

1. exact target and parent source/validator identities;
2. the ordered surface registry and dependency edges;
3. exact family rules and case overrides;
4. one row for every parent case, in parent order, containing parent case ID,
   seal, family, kind, profiles, primary/support identities, output policy,
   direct surfaces, transitive closure, rule identity, and non-crediting state;
5. per-family, per-kind, per-direct-surface, per-closure-surface, per-profile,
   and classification-state counts;
6. explicit claims and residuals; and
7. domain-separated per-record/list/top-level SHA-256 seals over canonical JSON
   (UTF-8, sorted keys, compact separators, no NaN/infinity).

The generated JSON and Markdown are summaries, not alternate authorities. The
generator supports ordinary regeneration and `--check`. Ordinary CI reads no
network, external checkout, local evidence directory, or official execution
artifact.

## 6. Fail-closed invariants and mutation teeth

Validation and focused tests must reject at least:

- target, parent physical hash, parent schema/seal, validator-source, case-list,
  or content-list drift;
- any parent semantic validation failure;
- duplicate, missing, extra, or reordered case rows;
- a case ID, parent seal, family, kind, profile, source/support identity, or
  output-policy mismatch;
- duplicate, missing, reordered, cyclic, or unknown surface definitions;
- owner, axis, current-state, or decline-code drift;
- an uncovered or overlapping exact family rule;
- an override with the wrong ID/family/kind/seal or an unused override;
- wrong direct surfaces, incomplete/extra/misordered transitive closure, or a
  rule ID inconsistent with the row;
- any M0 source/content/import/execution claim other than `not-run`;
- any native outcome, case support/decline, pair, performance, U2 completion,
  complete axis/population, terminal gate, or parity credit;
- aggregate or record/list/top-level seal mismatch; or
- stale generated JSON or Markdown.

Tests that mutate inner semantics must reseal outer records where necessary so
the intended validator—not merely the first checksum—rejects the mutation.

## 7. Acceptance, stop conditions, and next milestones

M0 is accepted only after:

1. this plan is committed and pushed alone before implementation;
2. implementation/tests are committed and pushed from that source-first
   boundary;
3. all 3,723 parent cases are classified exactly once at harness-floor state;
4. focused positive/mutation tests, regeneration/`--check`, complete-parity
   generation, documentation parity checks, and link checks pass, with any
   unrelated pre-existing failure named exactly; and
5. the contract, roadmap, implementation plan, plan index, `PLAN.md`, and
   `STATUS.md` link the accepted bounded result without promoting TL0.6.4.

Stop without publication if the parent authority no longer validates, the
family floor does not cover the exact population, the surface DAG is cyclic,
or any row would require guessing from a filename. M0 runs no Lean, Axeyum,
CTest, Lake, server, compiler, runtime, or provider process.

The required continuation is not optional:

- **M1 — pinned-content refinement:** inspect every exact primary, sidecar,
  runner, initialization hook, and directory support closure; add source-level
  construct/tactic/meta/runtime/FFI/RPC evidence with reviewed false-positive
  and false-negative controls.
- **M2 — exact dependency closure:** derive and content-bind module imports,
  generated artifacts, runtime/library/FFI dependencies, and request/project
  closures; lexical scanning alone cannot satisfy this milestone.
- **M3 — full authority review:** resolve every provisional/unclassified field,
  publish stable per-case owners/decline routes, and accept TL0.6.4 only when no
  case is silently delegated or credited below its required native surface.
- **TL0.6.5:** only after TL0.6.3 and accepted TL0.6.4 evidence may matched
  native execution form terminal comparison rows.

## 8. Non-claims

M0 does not claim that Axeyum parses, elaborates, checks, proves, builds, serves,
compiles, runs, or links any U2 case. It does not claim exact Lean import or
runtime dependency closure. It does not reinterpret the accepted local R6
64/64 official shard as native support. It cannot complete U2, any A0-A11 axis,
or Lean 4 parity.
