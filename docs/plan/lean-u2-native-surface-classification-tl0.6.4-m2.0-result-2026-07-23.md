# Lean U2 TL0.6.4 M2.0 result — typed dependency and provider contract

Status: **accepted bounded M2.0; M2.1-M2.7 and TL0.6.4 remain open**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[M2 source-first plan](lean-u2-native-surface-classification-tl0.6.4-m2-plan-2026-07-23.md),
[accepted M1 result](lean-u2-native-surface-classification-tl0.6.4-m1-result-2026-07-23.md),
[official CI profiles](lean-u2-official-ci-profiles-v1.json), and
[execution-evidence contract](lean-execution-evidence-v1.json).

## 1. Verdict

M2.0 is accepted for its offline schema boundary. The canonical
[dependency authority](lean-u2-native-dependency-v1.json) freezes typed node,
edge, evidence-state, resolver, official-variant, selection, and per-case graph
records for all 3,723 U2 registrations. It projects all eight exact official
selection sets and all 111 official CTest attempt variants without expanding
408,374 case/variant occurrences into duplicate rows.

This is an empty graph contract, not dependency closure. Every official
provider identity is `unbound`; all seven resolver milestones are `not-run`;
all 3,723 case closures are `not-run`; and the canonical node and edge lists
are empty. M2.0 ran no external Lean, Lake, build, test, editor, compiler,
runtime, or tracing process. It establishes no exact import, generated-file,
artifact, library, FFI, request, runtime, native-support, pair, performance,
population, axis, gate, or parity fact.

## 2. Source-first checkpoint sequence

The work was committed and pushed in reviewable order:

1. `39028ec2` preregistered the M2.0-M2.7 graph and resolver program before an
   M2 authority, resolver, or dependency process existed.
2. `527a3062` implemented the offline M2.0 generator and focused contract/
   mutation tests while the committed authority was still absent.
3. `a4100d7d` published the canonical empty authority and generated summaries
   only after the pre-authority contract tests passed.
4. `749d2d04` made M2.0 a required local/CI parity gate and added its bounded,
   zero-credit snapshot to the terminal complete-parity scoreboard.

No native dependency process was executed in this sequence. The earlier
read-only command introspection used to design the plan is not represented as
M2 authority or closure credit.

## 3. Frozen denominator and factoring

| Dimension | Retained count/state |
|---|---:|
| U2 case rows | 3,723 |
| exact official selection sets | 8 |
| official provider/attempt variants | 111 |
| factored case/variant occurrences | 408,374 |
| typed node classes | 11 |
| typed edge classes | 31 |
| evidence/assurance states | 9 |
| resolver milestones | 7 |
| bound provider variants | 0 |
| resolved nodes | 0 |
| resolved edges | 0 |
| complete case closures | 0 |
| external processes | 0 |
| native outcomes / paired cells / parity credit | 0 / 0 / 0 |

Case applicability is retained by exact selection-set reference. Each case row
stores the applicable selection IDs and resulting provider-variant count;
their sum is exactly 408,374. Each variant retains its official context, job,
phase, stage, preset, options, selection identity, and command, but no provider,
platform, configuration, executable, search path, or resource lane may be
invented before the source-first resolver milestone that binds it.

## 4. Typed graph and assurance boundary

The eleven node classes distinguish source, Lean module, generated file,
build artifact, package/project, executable/tool, library/plugin,
request/document, runtime file/effect, external/network, and platform/profile
identities. The 31 edge classes keep header declarations, source/`.olean`
resolution, transitive imports, generated runners, Lake facets, linking and
loading, FFI, requests, runtime effects, network use, and conditional variants
separate.

An edge must carry exactly one of nine states: `declared-static`,
`resolved-static`, `configured`, `observed-runtime`,
`conditional-not-taken`, `provider-unavailable`, `intentionally-online`,
`declined`, or `unresolved`. A syntax declaration cannot become runtime
observation, and one provider or platform cannot close another variant. M2.0
contains no edge, so none of these assurance states has yet earned closure.

## 5. Resolver handoff

The seven frozen resolver milestones are:

1. M2.1 exact `--deps-json` header declarations and modifiers;
2. M2.2 bound source/`.olean` path resolution and transitive module closure;
3. M2.3 configured generated wrapper/runner materialization;
4. M2.4 Lake package, target, facet, artifact, cache, library, and plugin setup;
5. M2.5 compiler, interpreter, runtime, library, and FFI evidence;
6. M2.6 editor/server request and project evidence; and
7. M2.7 deterministic variant merge and residual review projection.

Every resolver remains `not-run`. Before M2.1, its own source-first attempt
plan must bind the exact binary, source/search paths, input ordering, retained
raw evidence, process budget, mutation rules, output root, and stop conditions.

## 6. Retained artifact identities

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| canonical authority | 6,533,887 | `46d2c17363bf8e4097d12df20f8ee9ffb86acf647642068d3eacc72e711dd4d6` |
| generated JSON | 2,907 | `7de7eea409dc2ab59f5224838e324e783a10341b09910452451932bd6ecd7390` |
| generated Markdown | 1,602 | `999dc0d1b9685be5ba36aab5f9758abbb42cad12aeda013ccc0d647ccf6eae4c` |
| generator | 31,061 | `e5f835bf4a0dbd4e59e82068b1e57b073f484153333962d1c85e0c308de90b19` |
| focused tests | 8,985 | `6f6e157077f7dcd854fdaea998e73aff6b99de30aa23a310129d5ef034c44c93` |

Canonical logical seals:

- record: `250b662691af5d71e375f3643454f94585bc51ff6f28aff69091b0f3956fdc86`;
- node registry: `5a6eae97dd988807745fde4ddcfca3c19ca377985c6e3809c1f015ab3b8cb469`;
- edge registry: `2fc8251dd20b93a18501be7630ec1400da334bce00962d1974bc41c055356106`;
- evidence states: `efc4380b876925d2bcb6e0a9c2e494054dc7a1bde5b72aaf6b9c040f6b05f94f`;
- resolvers: `50b9c7c4d1684bdbc4a088ad801281ddc9d0af7dda413c404288e4c410c65e2c`;
- selections: `9eaeee1e4750290600794ab5bd1da1c5c3a79c92c5695349e4f48dd75d49b736`;
- provider variants: `55c7d4a7f0bcb9bda74ca69dc2887bea4f85429ce8a85b2b200aa6a89c35f9bf`;
- empty nodes: `709fa8d5889850ceb13a1ea91e63c9b00de840e2e9d6f0d5f2d09c26a492b20d`;
- empty edges: `892f4671b47c45a0eb477f26799bcf602633d3f5961e6d463619b908d583938c`;
  and
- cases: `951043917d66b164bc034f4f88965e7ebf5724b840930e79f08b9b292d9f4df1`.

## 7. Validation

Accepted task-owned gates include:

- 12 focused contract/authority/mutation tests, including mutations resealed at
  the row, list, and top-level boundaries;
- deterministic offline authority and generated-report validation;
- nine complete-parity registry/mutation tests;
- complete-parity regeneration with 0/10 complete populations, 0/12 complete
  axes, zero pairs, zero satisfied gates, and `terminal_ready=false`;
- Python compilation, shell syntax, and whitespace checks; and
- required M2.0 local/CI wiring in `just parity-docs`, `scripts/check.sh`, the
  docs workflow, and the main workflow.

The focused suite rejects registry, selection, provider binding, process
outcome, case closure, node/edge, parent, claim, credit, summary, list-seal,
and record-seal mutations. These are schema and non-credit controls; they do
not substitute for the M2.1-M2.7 process-specific mutation suites.

## 8. Nonclaims and required continuation

M2.0 does not claim that `--deps-json` resolves paths; that a template is a
configured wrapper; that a lexical reference is reachable; that Lake setup is
a build; that a linked library was loaded; that an FFI declaration was called;
that a sidecar is an RPC request; or that any official case can execute
natively in Axeyum.

TL0.6.4 remains PARTIAL until M2.1-M2.7 populate complete typed closures for
every required case/provider variant or retain a reviewed decline, and M3
reviews all 3,723 rows with no provisional, unresolved, or silently delegated
field. TL0.6.5 may form matched native rows only after that boundary and exact
official/native execution evidence.
