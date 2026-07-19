# Glaurung joint-triplet census — 2026-07-19

ADR-0275 Phase A accepts the exact common-stream triplet; Phase B rejects the
full census. Raw artifacts are retained at
`/nas4/data/workspace-infosec/.axeyum-joint-triplet-census-20260719.42ERHm`.

## Phase A: accepted

All 3/3 processes and traces validate. Every Z3, Axeyum, and Bitwuzla cold/warm
cell decides and agrees on 4,846/4,846 checks with direct warm execution. The
authority query/outcome and 235-row diagnostic finding hashes reproduce
ADR-0274 exactly. Campaign/report hashes are
`ec1e15f3664f85887c67e758d93770a263536ce3057f1e6fb4e60e26364ed05b`
and `f1d0d74ca95f669e6403137f4ca2c6cf14b492516efc9e27cb8f8b604794af4a`.

## Phase B: rejected

All 3/3 processes exit successfully and produce validator-clean v4 traces, but
the committed analyzer rejects immediately with `coverage is not 338/338`.
Every repetition identically records:

- 210/338 analyzed functions;
- 3,266 findings: 16 high-confidence and 3,250 diagnostic;
- 243 exploration runs: 216 complete and 27 state-budget stops;
- 97,112/97,112 shadow verdict agreements;
- 97,010 direct Axeyum warm checks plus 102 assertion-cap fallbacks; and
- zero solve-budget, timeout-budget, deadline, path-cap, or decided-disagreement
  rows.

Annotated stdout is byte-identical across N=3 at SHA-256
`4f518c2605d76334853a80a5f2b523518b65452426df613668854a4bba7f96fd`.
The retained Phase B campaign hashes to
`00928a7a2dc975d82a539836e548a50182f56a6fa7bf3c370559520b7ece06d2`;
the fail-closed analyzer stderr hashes to
`4522bd0e29c3991d7f5f10cf51f8f80d43f7b97507ccf7e8d2a2e7cf769fc303`.

The 16 high-confidence rows are deterministic cold-Z3-authoritative census
output on an unlabeled and incomplete population. They do not establish recall,
precision, full-census coverage, cross-authority finding parity, or solver
performance. The assertion-cap fallback also independently violates the
registered six-cell topology gate.
