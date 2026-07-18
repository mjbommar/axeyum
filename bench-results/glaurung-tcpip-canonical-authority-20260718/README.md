# Glaurung tcpip canonical-authority control — 2026-07-18

This artifact records the first stable Glaurung finding-output divergence that
requires an explicit model-selection policy, then repeats the same fixed work
with backend-independent unsigned-minimum choices. The before/after cells use
the same source revisions, binaries, tcpip input, 15-function prefix, 250 ms
per-check wall, and three order-balanced repetitions.

| Policy | Z3 findings / solves | Axeyum findings / solves | Stable intersection | Z3-only | Axeyum-only | Exact parity |
|---|---:|---:|---:|---:|---:|---|
| Any satisfying model | 128 / 3,079 | 126 / 2,991 | 126 | 2 | 0 | no |
| Least unsigned value | 110 / 80,563 | 110 / 80,563 | 110 | 0 | 0 | yes |

Every population is byte-stable across its three repetitions. The two
any-model Z3-only rows are double-fetch reports at `0x1c000830d` and
`0x1c000832e`; the complete strings and set partitions remain in
[`any-model-report.json`](any-model-report.json). Under policy
`glaurung-min-unsigned-v1`, both authorities emit the same ordered 110-row
finding list with SHA-256
`e657ea6be385ba32b2aec6e49f2a780ec7f80850eb3105dc750fce74810d438e`.

The canonical telemetry is also identical by authority: 1,206 attempts, 1,204
completed selections, two already-infeasible paths, 79,466 total probes, and
zero unknown, unavailable-solver, backend-error, unsupported-width,
unexpected-final-UNSAT, or other inconclusive choices. This equality is
stronger than output parity for the measured prefix: the two authorities also
execute the same number of checks and model-choice probes under the policy.

## Exact identities and controls

- Axeyum runner source: `23b9caef2d822aa430b0090ab75636ea0012eb8e`.
- Glaurung experiment source: `fb051de7294dfa57396e1184dc1f9ba86ef0ec5d`,
  based on `4fce79fccd167c898fa5acad24f4b8b947ba7daa`.
- tcpip input SHA-256:
  `ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`.
- Z3-authority binary SHA-256:
  `01a97e6319c07c5d40d79d5d58053a9a3e7fbc5be4b520028b4c4ca25fbcc4c7`.
- Axeyum-authority binary SHA-256:
  `f7f2a66a7145429492be4a6a3d3264df836a7198867b28bb27cea13670373ed0`.
- [`any-model-report.json`](any-model-report.json) SHA-256:
  `eda63a9372f159ff0b0909aecdfe87929a69a6695a838f4f0554bfd1f1feeaa6`.
- [`canonical-report.json`](canonical-report.json) SHA-256:
  `fc5181eb8699055b37a0fda7c742db677e5d733bc8d24d284fed7e5246d0f118`.
- [`glaurung-canonical-model-selection.mbox.gz`](glaurung-canonical-model-selection.mbox.gz)
  SHA-256:
  `e1e8c20bc785689be00f0118b9044531e9587b73921d9a4acfc0122185c27f43`.

Both reports use schema `axeyum.glaurung-authoritative-finding-parity.v3`.
The runner requires exact source identity before and after execution, an
explicit shared check timeout, stable coverage/work summaries, stable output
within each authority, and exact ordered-list parity for acceptance. Canonical
acceptance additionally requires the named policy, nonzero exercise, complete
attempt/reason accounting, stable per-authority telemetry, and zero
inconclusive choice. The any-model report is intentionally retained with
`accepted: false` because its exact parity gate fails.

The four Glaurung commits are preserved as the reproducible compressed mbox
[`glaurung-canonical-model-selection.mbox.gz`](glaurung-canonical-model-selection.mbox.gz).
They add the opt-in model policy, make the common native check wall explicit
for both backends, partition every failure reason, and distinguish an already-
infeasible path from an inconclusive model choice. The default any-model
behavior remains unchanged.

## Claim boundary

This experiment establishes exact Z3/Axeyum finding-output and exploration-
counter parity for one fixed 15-function tcpip prefix when both use the same
unsigned-minimum concretization policy. It also establishes that unrestricted
backend model choice does **not** preserve exact output on that prefix.

Canonicalization is not finding-preserving relative to the any-model cells:
the shared result changes from 126 sinks to 110. It therefore defines a
reproducible exploration policy; it is not a proof that it retains the union
of bugs reachable under arbitrary model choices, and it remains opt-in rather
than becoming Glaurung's default. Wider prefixes, other timeout-sensitive
drivers, path-enumeration coverage, and multi-model exploration remain open.

The process times and RSS values are retained for auditability only. The
canonical policy performs roughly 80,000 checks per process versus roughly
3,000 in the any-model control, so these standalone values are neither a fair
solver-speed comparison nor evidence for a production performance claim.
