# SMT-COMP repaired P0 v1 layout incident

Status: retained negative; no result credit
Date: 2026-07-23
Repair plan: [runtime-layout repair](smtcomp-repaired-p0-runtime-layout-repair-plan-2026-07-23.md)

## Bounded finding

The first Axeyum cell published all 1,810 expected records and all three shard
completions, with zero contradictions of official known statuses. It is still
an invalid E3/P0 run: initial allocation 0 exited 2 after shard completion
because aggregate validation rejected the preparation input
`run-manifest.json` inside the runtime evidence root.

No resource or multi-host aggregate completion, adjudication, or raw export was
published. The root receives no correctness, coverage, timing, or P0 credit.
No retry was attempted and no evidence was rewritten.

## Retained identity

| Item | Value |
|---|---|
| Preparation root | `/nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-da679e1429de-v1` |
| Cell root | `cells/axeyum` below that root |
| Run identity SHA-256 | `03966268266c31fceee7e9eb8d8c5610b137462a5d62bb24a432c00bd828efd8` |
| Records | 1,810 |
| Digest of sorted record SHA-256 list | `8f6900038e787d621200a13c4461a59e8528ba5963293bdc2411ca656f579319` |
| Shard 0 result set / records | `45a542ca9b82f850db70cbb81e488c207f02192fe438e929048654d89e5a4934` / 604 |
| Shard 1 result set / records | `534dd4a3177f93daddec3932d6ffbd5c713e18aedbf3b4514ea15ac984246faa` / 603 |
| Shard 2 result set / records | `4ffdee4939f0fb22d0db515673b75ad1e1d7127ad83fd0391343049c3ad06390` / 603 |
| Known-status contradictions | 0 |
| Active leases/processes after stop | 0 / 0 |

Allocation 0 retained failed terminal record SHA-256
`5e843bfc6fac95097cf2660ebd8c07f22d5a69db2fe2d78b6bd092f17e222325`.
Its exact stderr sidecar SHA-256 is
`4693a50bbdfe29b42809367dd43a5cfe92034a05d46ae673bdcd107d10023d1e`
and contains:

```text
resumable run rejected: unexpected run artifact: run-manifest.json
```

Allocations 1 and 2 completed with terminal-record SHA-256 values
`931ccb4c35fa66ee32cfcdff3a481203388fa311771f86f154aebafccd97cd4c`
and `450a9286811c9417f98ab7a9ed306fe825b85ab074dc369cf49872baccea8cdd`.

## Diagnostic-only outcome inventory

These counts describe retained bug-diagnosis evidence only:

| Logic | `sat` | `unsat` | `unknown` | no verdict | Total |
|---|---:|---:|---:|---:|---:|
| QF_ABVFP | 58 | 136 | 62 | 269 | 525 |
| QF_AUFLIA | 128 | 125 | 134 | 118 | 505 |
| QF_BVFP | 203 | 172 | 44 | 86 | 505 |
| QF_FP | 61 | 33 | 40 | 141 | 275 |
| **Total** | **450** | **466** | **280** | **614** | **1,810** |

There are 1,195 completed-process records and 615 wall-timeout records. One
timeout retained a verdict under the registered response-after-timeout policy,
which is why no-verdict count is 614 rather than 615.

## Repair evidence to date

The bounded layout repair commit `de91aff0` moves run manifests under the
preparation `inputs/` namespace and leaves the runtime allowlist unchanged. Its
portable and mandatory local E2 suites pass 62 tests. The refreshed mandatory
live E3 gate also passes 62 tests with no skips:

```text
evidence root:
  /nas3/data/axeyum/harness/e3-gate/live-1784818789442898698-de91aff06216
control completion:
  3a6461063accc4407a6b39b88d3087980e0cb7049b83bc29b48abd8b26f6c765
loss/retry completion:
  6e4872a05c733aa8c5579dae0f43a0493ab0a92adb0438ab9d6dbc7f72f39ce7
```

A new preparation and solver run remain forbidden until the repair is
integrated, all preregistered gates are fresh from that integrated commit, and
a new immutable preparation result is committed.
