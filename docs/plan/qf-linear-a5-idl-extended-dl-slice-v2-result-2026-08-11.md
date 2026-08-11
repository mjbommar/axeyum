# QF linear A5 IDL extended DL slice v2 result — 2026-08-11

## Outcome

The [preregistered corrected candidate](qf-linear-a5-idl-extended-dl-slice-v2-preregistration-2026-08-11.md)
passes its targets, immediate controls, allocation controls, complete retained-
decision comparison, and focused solver gates. It recovers exactly the two lost
QF_IDL decisions through the existing checked DL route and preserves every
other retained verdict. The exact-pushed complete repository gate remains the
last release condition; no V2 census is yet authorized.

## Identity

Candidate source is exact local commit
`46edad8bac7e193303871d601914fef2115bf721`, descended from pushed telemetry and
preregistration `8a3f0566c00a`. Its 11,873,352-byte release binary has SHA-256
`30a45e5a67963d1111d6ca69dd58dcae0129085ebbdf31db5c5f13752c2a4db2`.
The immediate group started at `2026-08-11T22:37:54Z` with loads 4.38, 6.00,
and 6.71. Every worker inherited the 8 GiB limit, exited 0, and emitted zero
stderr.

## Immediate matrix

| Case | Required result | 3/3 wall range | Peak RSS range | Stable JSONL SHA-256 |
|---|---|---:|---:|---|
| BubbleSort | UNSAT / `dl-online` | 16.95--17.13 s | 147,968--148,332 KiB | `0e3fa1c99033d47e6ab97d9101110a12fa4f83564dfb2765a115af71c1f1258d` |
| GraphPartitioning | SAT / `dl-online` | 18.78--18.85 s | 30,452--30,764 KiB | `a274e2785023fcb6c8d4305a22c2f4a43c289fa4c8d5e22fceaa36f98a1fb1c4` |
| `lpsat-goal-18` | UNSAT / `lia-dpll` | 22.88--22.94 s | 63,376--64,280 KiB | `13652b5e67c9777c4450fbd5a6797f3c3c91c7a8fe78ad7d65f74f230b414f39` |
| maze gain | UNSAT / `lia-dpll` | 19.13--19.18 s | 44,784--45,332 KiB | `2a90fe18f0f21ee29d0c1adfa746f1a2c6742fc65f27121802ecdb14ea7c8275` |

The protected moderate equality class remains on its 12-second DL slice; the
maze retains standard 18-second behavior. The two measured large equality
targets alone receive the structural 21-second maximum in this matrix.

## Allocation controls

The original `pursuit` and `tgc` controls and the 31,944-variable Maze control
all retained typed pre-SAT declines with zero SAT rounds, zero stderr, and exit
0. Their exact counts remain 1,447/4,733, 1,411/6,774, and 1,084/31,944
arithmetic atoms/CNF variables. JSONL SHA-256 values are respectively
`4e8ce39ccaf529b4234026ff6542484845b5f7c7b7159c565940180fa2925a94`,
`9a60c6076f2c5e5bb94ff8d5641879d6da14ae31a6a5215c80c8737d00828368`,
and `d567fbb9bc4fbc259b3b194af292c20723523e6df19a31b2b175910574ff4034`.

## Complete retained-decision gate

The exact candidate ran all 68 committed QF_IDL decisions in 2:14.31 with
148,080 KiB peak RSS. Against the exact `d0e0d6cea` V2 capture, 66 verdicts are
identical and the only differences are the preregistered BubbleSort
`unknown -> unsat` and GraphPartitioning `unknown -> sat` recoveries. Candidate
JSONL SHA-256 is
`795f41ea03c507324fa61e3ddf33ae449291f6b22bf017dd530e654d045b71a2`.

All 105 QF_RDL decisions are byte-identical between a fresh exact-`d0e0d6cea`
run and the candidate, including traces. Baseline/candidate wall times were
2:37.93/2:38.32, peak RSS 56,296/56,452 KiB, and both JSONL streams have SHA-256
`2b25379ac30f0c247fd1ad8cbc2a75b74c0ec58286965db94bef246a3ac856c0`.
All four retained runs exited 0 with zero stderr.

## Focused gates

- format and strict all-target/all-feature solver Clippy pass;
- structural budget, telemetry, zero-budget, and route tests pass with nonzero
  counts;
- all 1,093 full-feature solver-library tests pass;
- deep-input no-abort passes 16/16;
- online LIA/LRA/CDCL(T) integrations pass 40/40;
- QF_LRA/Z3 differential passes 5/5 over 1,500 cases with zero disagreement;
  and
- simplex/Z3 fallback differential passes 1/1 over 1,200 cases with zero
  disagreement in 107.33 seconds.

## Release boundary

Commit and push the documentation descendant, verify the remote ref, and run
one uninterrupted external-frontier `CARGO_BUILD_JOBS=2 just check` on that
exact clean checkpoint. Until it exits 0, the candidate is not release-qualified
and QF_LRA row 1 must not start. All measurement files remain outside the
repository under the corresponding `a5-idl-dl-slice-v2-*` directories.
