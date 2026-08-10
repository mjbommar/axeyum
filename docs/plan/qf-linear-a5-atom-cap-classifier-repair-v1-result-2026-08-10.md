# QF linear A5 atom-cap classifier repair v1 result — 2026-08-10

## Outcome

The [preregistered](qf-linear-a5-atom-cap-classifier-repair-v1-preregistration-2026-08-10.md)
exact-phrase repair is implemented and pushed at
`d646382e7422ba60faae7bb5795a1174f8ad4a34`. It is not fully gated and does not
authorize a census restart. A user-requested wrap-up interrupted the required
full gate; the next session must rerun that gate from the beginning.

## Repair

Route-trace schema v1 serializes timeout and deterministic resource kinds as
the same `reason: budget` variant. The census classifier now recognizes only
the production phrase `atom cap exceeded` as a deterministic
`normalization-resource` boundary before applying its coarser bucket rules.
The real `sc-39` route/reason/detail spelling replaces the synthetic control
fixture. A broad `round cap exceeded` negative fixture remains
`search-budget`. No solver, route, verdict, cap, timeout, memory limit, evidence
policy, or public API changed.

## Focused evidence

- `scripts/tests/test_qf_linear_a5_census.py`: 23/23 pass;
- Python compilation, Rust formatting, and `git diff --check` pass; and
- the exhaustive diagnostic over the retained non-credited 200-row QF_LRA
  stream changes exactly 24 reference-only traces: 21
  `search-budget -> normalization-resource` and three
  `unsupported-dl-shape -> normalization-resource`. Every changed trace has
  the exact atom-cap phrase; no other trace changes.

With the candidate classifier, the diagnostic join has 90 current decisions
versus 86 historical, four agreeing gains, zero losses, zero wrong verdicts,
56 reference-only rows, and the required `sc-39` resource control. Bucket
counts are 24 normalization-resource, 26 search-budget, four model-replay, and
two explanation-core. These numbers validate the classifier only; the input
stream remains non-credited. The focused log has SHA-256
`cc05378f0981a7d4883abde9a4c51d2b04b35c2ad9e51dce073bc4ccc240d667`.

## Interrupted full gate

The exact pushed source, upstream, and remote topic ref were all
`d646382e7422ba60faae7bb5795a1174f8ad4a34`. Its external-frontier
`CARGO_BUILD_JOBS=2 CARGO_INCREMENTAL=0 just check` ran from
`2026-08-10T11:35:32Z` to `2026-08-10T11:40:26Z`, when it was interrupted for
the requested wrap-up. The wrapper exited 101 after 294 seconds. Formatting,
strict all-feature Clippy, and the visible workspace tests were green; the log
contains no failure marker, but an interrupted run proves no complete gate.
The 137,239-byte log has SHA-256
`6c1f723fc50778f144f81e010b627edd734c069001d378baa36b5d9db773e3d0`.

## Resume boundary

Start one fresh uninterrupted external-frontier `just check` at the exact
pushed repair. Only exit 0 authorizes rebuilding/fingerprinting the release
binary and restarting V2 from QF_LRA row 1 at one-minute load at most 12. The
invalid `775446932` stream authorizes neither reuse nor QF_IDL.
