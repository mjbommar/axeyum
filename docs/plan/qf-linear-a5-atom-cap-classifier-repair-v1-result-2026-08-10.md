# QF linear A5 atom-cap classifier repair v1 result — 2026-08-10

## Outcome

The [preregistered](qf-linear-a5-atom-cap-classifier-repair-v1-preregistration-2026-08-10.md)
exact-phrase repair is implemented and pushed at
`d646382e7422ba60faae7bb5795a1174f8ad4a34`. Exact pushed documentation
descendant `b9938576bce50b80c4525d48cddacdf1ac5cb266` passed the complete release
gate. The repair now authorizes rebuilding and fingerprinting a fresh release
binary; the invalid capture remains non-credited and cannot be reused.

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

## Completed full gate

Local HEAD, upstream, and the remote topic ref were all exact
`b9938576bce50b80c4525d48cddacdf1ac5cb266` before the rerun. This checkpoint
is a documentation-only descendant of classifier code `d646382e7`. One fresh
uninterrupted
`AXEYUM_PROGRESS_FRONTIER_ARTIFACT_DIR=<external> CARGO_BUILD_JOBS=2 CARGO_INCREMENTAL=0 just check`
ran from `2026-08-11T17:39:19Z` through `2026-08-11T19:24:54Z`: 6,335 seconds,
exit 0. The tracked tree remained clean.

The gate passed formatting, strict all-feature Clippy, every workspace test and
doctest, the 1,091-test solver library, 9/9 externally stored frontier tests in
205.11 seconds, both order-255 CAS moment proofs in 1,105.06 seconds,
warning-denied rustdoc, QF_BV/reflection policies, both 162-file Glaurung
policies with zero disagreement, foundational resources, rules-as-code, the
165-test SMT-COMP resume aggregate with one expected skip, every Lean/process
contract, parity docs with zero disagreement, plan authority, and links.

The 582,472-byte, 10,414-line gate log has SHA-256
`ad3ddbf2d84e6578a6809d358be37656311cf98cbb42ba51b2487362cbaceb91`.
The five external frontier artifacts were retained outside the repository:

- `bv_reduction.json`: 2,988 bytes,
  `74dabc83eee6a694f0e1eebba7e62fdfd85c67f68d4ee55519627612f6a1fb0b`;
- `lia_cuts.json`: 2,608 bytes,
  `ffed6fa273836abc2ac56653e36ed83cde6adaef63328bd6f3582d5b8a024b0c`;
- `nia_unsat.json`: 2,999 bytes,
  `a6e2bb3897fba8478f465d9fa1b6e3d1b0ea58893a7cb9e358dec5fffdcae5df`;
- `nra_degree.json`: 2,894 bytes,
  `5b473e66956140b664209bc51dd71ac1a751bf8b4121c1582aa6074265a5ae17`;
- `string_bound.json`: 2,791 bytes,
  `64ce75f853bc420e60e849b07c7d8429a926f2c019d86e611c7a85c8a4ba3181`.

## Resume boundary

Build and fingerprint one fresh release binary from the next exact pushed
documentation checkpoint. Restart V2 from QF_LRA row 1 only when one-minute
load is at most 12 and bind every row to that exact source/binary identity. The
invalid `775446932` stream authorizes neither reuse nor QF_IDL. Run the strict
QF_LRA join before permitting QF_IDL.
