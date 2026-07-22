# Lean compatibility assurance matrix

> **Generated; do not edit by hand.** Source: [`docs/plan/lean-compatibility-v1.json`](../lean-compatibility-v1.json). Regenerate with `python3 scripts/gen-lean-compatibility.py`; use `--check` in validation.

This matrix refuses to collapse parsing, translation, independent kernel admission, official admission, source elaboration, proof checking, workflow reproduction, and runtime reproduction into one word such as `supported`.

## Pinned target

- Lean `4.30.0` at `d024af099ca4bf2c86f649261ebf59565dc8c622`.
- `lean4export` `3.1.0` at `a3e35a584f59b390667db7269cd37fca8575e4bf`.
- 12 exact artifact/profile rows and 9 registered unsupported-construct codes.

## Profile gates

A row satisfies its target profile only when every listed field is `succeeded`; lower-profile evidence never fills a higher-profile field.

| Profile | Meaning | Required assurance | Satisfied rows | Total rows |
|---|---|---|---:|---:|
| `K0-checker` | Independent checker | `admitted` | 1 | 1 |
| `K1-import` | Versioned declaration import | `parsed`, `translated`, `admitted` | 3 | 5 |
| `K2-source` | Native source | `parsed`, `source_elaborated`, `admitted` | 0 | 2 |
| `K3-proof` | Goals and checked tactics | `admitted`, `proof_checked` | 0 | 1 |
| `K4-workflow` | Project and editor workflow | `workflow_reproduced` | 0 | 1 |
| `K5-runtime` | Native runtime | `runtime_reproduced` | 0 | 1 |
| `K6-ecosystem` | Pinned ecosystem | `admitted`, `proof_checked`, `workflow_reproduced`, `runtime_reproduced` | 0 | 1 |

## Assurance-state snapshot

| Assurance field | Passed | Declined | Failed | Not attempted | N/A |
|---|---:|---:|---:|---:|---:|
| `parsed` | 6 | 0 | 0 | 5 | 1 |
| `translated` | 3 | 2 | 0 | 5 | 2 |
| `admitted` | 4 | 0 | 0 | 8 | 0 |
| `official_admitted` | 6 | 0 | 0 | 6 | 0 |
| `source_elaborated` | 6 | 0 | 0 | 5 | 1 |
| `proof_checked` | 3 | 0 | 0 | 9 | 0 |
| `workflow_reproduced` | 0 | 0 | 0 | 11 | 1 |
| `runtime_reproduced` | 0 | 0 | 0 | 11 | 1 |

## Artifact matrix

| Subject | Target | Gate | Parsed | Translated | Admitted | Official | Source elaborated | Proof checked | Workflow | Runtime | Declines | Evidence | Residual |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Native kernel regression profile | K0-checker | pass | n/a | n/a | passed | not attempted | n/a | passed | n/a | n/a | - | [test](../../../crates/axeyum-lean-kernel/tests/prop_large_elim_soundness.rs); [test](../../../crates/axeyum-lean-kernel/tests/prop_large_elim_derives_false.rs); [test](../../../crates/axeyum-lean-kernel/tests/proj_representation.rs); [test](../../../crates/axeyum-lean-kernel/tests/projection_inference.rs); [test](../../../crates/axeyum-lean-kernel/tests/projection_reduction.rs); [test](../../../crates/axeyum-lean-kernel/tests/structure_eta.rs); [test](../../../crates/axeyum-lean-kernel/tests/real_lean_structure_eta_crosscheck.rs) | K0 includes native projection inference, reduction, and structure eta but does not imply native source support or broader kernel compatibility. |
| Official direct-recursive MiniNat/MiniList fixture | K1-import | pass | passed | passed | passed | passed | passed | passed | not attempted | not attempted | - | [fixture](../../../docs/plan/fixtures/lean4export-v4.30-recursive-shapes.ndjson); [test](../../../crates/axeyum-lean-import/tests/lean4export_v31.rs) | Recursive-indexed, reflexive, nested, and mutual families remain outside this exact fixture. |
| Official flat declaration fixture | K1-import | pass | passed | passed | passed | passed | passed | passed | not attempted | not attempted | - | [fixture](../../../docs/plan/fixtures/lean4export-v4.30-axeyum-probe.ndjson); [test](../../../crates/axeyum-lean-import/tests/lean4export_v31.rs) | The retained axiom P is explicit; this fixture is not dependency-closed Init or mathlib evidence. |
| Official Nat-literal dependency root | K1-import | open | passed | declined | not attempted | passed | passed | not attempted | not attempted | not attempted | `literal-nat-typing` | [fixture](../../../docs/plan/fixtures/lean4export-v4.30-nat-literal.ndjson); [test](../../../crates/axeyum-lean-import/tests/lean4export_v31.rs) | Projection and arbitrary-precision Nat storage are cleared; literal typing is now the exact first blocker. |
| Official structure-projection dependency root | K1-import | pass | passed | passed | passed | passed | passed | not attempted | not attempted | not attempted | - | [fixture](../../../docs/plan/fixtures/lean4export-v4.30-projection.ndjson); [test](../../../crates/axeyum-lean-import/tests/lean4export_v31.rs) | This exact K1 projection root passes; TL2.5 structure eta is separately live at K0 and does not broaden this K1 import population. |
| Official quotient dependency root | K1-import | open | passed | declined | not attempted | passed | passed | not attempted | not attempted | not attempted | `quotient-package` | [fixture](../../../docs/plan/fixtures/lean4export-v4.30-quotient.ndjson); [test](../../../crates/axeyum-lean-import/tests/lean4export_v31.rs) | TL2.10 owns the fixed quotient package and reductions. |
| Selected 71-module official-source reconstruction gate | K2-source | open | passed | n/a | not attempted | passed | passed | not attempted | not attempted | not attempted | - | [document](../../../docs/plan/official-lean-ci-gate-audit-2026-07-21.md) | Official elaboration is oracle evidence only; no native-source or independent-admission credit follows. |
| Native goal, hole, unification, and tactic profile | K3-proof | open | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | - | [plan](../../../docs/prover-track/plan/README.md) | P6.2/P6.3 and TL5 remain implementation work. |
| Native evaluator, compiler, runtime, and metaprogram profile | K5-runtime | open | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | - | [plan](../../../docs/plan/lean-system-implementation-plan-2026-07-21.md) | No native Lean runtime profile is implemented today. |
| Native parser, macros, and elaborator profile | K2-source | open | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | - | [plan](../../../docs/plan/lean-system-implementation-plan-2026-07-21.md) | Official source acceptance does not implement this profile. |
| Native modules, packages, Lake, cache, and editor profile | K4-workflow | open | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | - | [plan](../../../docs/plan/lean-system-implementation-plan-2026-07-21.md) | No native project/editor compatibility result exists today. |
| Full pinned mathlib build and compatibility profile | K6-ecosystem | open | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | not attempted | - | [plan](../../../docs/plan/lean-system-implementation-plan-2026-07-21.md) | The pinned 8,606-file inventory is not a build or compatibility result. |

## Registered decline codes

These are fail-closed unsupported-construct results, not failed proofs and not permission to convert a decline into `unknown` or admission.

| Code | Owner | Meaning | Source |
|---|---|---|---|
| `declaration-unsafe` | `axeyum-lean-import` | The exported declaration is marked unsafe. | [source](../../../crates/axeyum-lean-import/src/lib.rs) |
| `declaration-unsafe-or-partial` | `axeyum-lean-import` | The exported definition is unsafe or partial. | [source](../../../crates/axeyum-lean-import/src/lib.rs) |
| `format-version` | `axeyum-lean-import` | The export stream is not the pinned format version. | [source](../../../crates/axeyum-lean-import/src/lib.rs) |
| `inductive-mutual` | `axeyum-lean-kernel` | A mutual inductive group is outside the current admission profile. | [source](../../../crates/axeyum-lean-import/src/lib.rs) |
| `inductive-nested` | `axeyum-lean-kernel` | Nested recursion is outside the current admission profile. | [source](../../../crates/axeyum-lean-import/src/lib.rs) |
| `inductive-reflexive` | `axeyum-lean-kernel` | Reflexive or higher-order recursion is outside the current admission profile. | [source](../../../crates/axeyum-lean-import/src/lib.rs) |
| `literal-nat-typing` | `axeyum-lean-kernel` | Natural literals have arbitrary-precision storage but await kernel typing and reduction. | [source](../../../crates/axeyum-lean-import/src/lib.rs) |
| `literal-string-typing` | `axeyum-lean-kernel` | String literals await kernel typing and reduction support. | [source](../../../crates/axeyum-lean-import/src/lib.rs) |
| `quotient-package` | `axeyum-lean-kernel` | The fixed quotient package is outside the current admission profile. | [source](../../../crates/axeyum-lean-import/src/lib.rs) |

## Enforced implications

- Translation success, decline, or failure requires successful parsing.
- Independent admission requires successful translation, except for a native-core artifact that starts inside the kernel boundary.
- Official admission requires successful source elaboration; it never implies independent admission.
- Proof checking requires independent admission.
- Workflow reproduction requires source elaboration and independent admission; runtime reproduction requires source elaboration.
- Every declined assurance names at least one registered code, and codes cannot appear on a row with no decline.
- Every row carries a retained evidence path and an explicit residual.
