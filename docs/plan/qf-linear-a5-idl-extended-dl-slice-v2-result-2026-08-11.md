# QF linear A5 IDL extended DL slice v2 result — 2026-08-11

## Outcome

The [preregistered corrected candidate](qf-linear-a5-idl-extended-dl-slice-v2-preregistration-2026-08-11.md)
passes its targets, immediate controls, allocation controls, complete retained-
decision comparison, and focused solver gates. It recovers exactly the two lost
QF_IDL decisions through the existing checked DL route and preserves every
other retained verdict. Its exact-pushed documentation descendant also passes
the complete repository gate. The repair is release-qualified, and the frozen
V2 census may restart at QF_LRA row 1 under its existing atomic protocol.

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

Exact local and remote checkpoint
`d1b570f91c27f83ef55127ea3d1c8baf700f05a5` passed one uninterrupted
external-frontier `CARGO_BUILD_JOBS=2 just check` from
`2026-08-11T23:08:32Z` through `2026-08-12T00:53:09Z`: 6,277 seconds, exit 0.
The 605,612-byte log has SHA-256
`2b0d456dbe2b8164bc6e5b1d68f2455ec889b334b12432ab71482982e0ae5666`.
The nine frontier tests passed in 194.09 seconds and wrote five external
artifacts with SHA-256 values:

- `bv_reduction.json`: `21318348865ff49d68d5de300fa799eac722350b35dd67d9c70ac45c8aa25f69`;
- `lia_cuts.json`: `06a8c8a788b199294c586364fa63d10a8030decdd2048da0e4bb9b07ce1a66bc`;
- `nia_unsat.json`: `642cc783904947f42ee6037da0a77fbca5684e0208d88e1880fae8e46733137a`;
- `nra_degree.json`: `885acd0e79dad5e828435a0b6896523205fda64343842b19ef5d25b309ac840c`;
  and
- `string_bound.json`: `13b44485963ea428df199989e80d46808c0808b2d880789e71694a5b9baf7e8d`.

The tracked tree was clean before and after the run, and local HEAD, upstream,
and the remote branch ref matched exactly. The gate also retained 1,093/1,093
solver-library tests, zero-disagreement differential suites, checked CAS proof
families, documentation, foundational resources, Glaurung 162/162 QF_BV
decisions with zero disagreement, resume/Lean authorities, parity docs, plan
authority, and links. All measurement files remain outside the repository under
the corresponding `a5-idl-dl-slice-v2-*` directories.

## V2 restart checkpoint

The exact-pushed documentation checkpoint
`6d4718e139d457c9a6e55608b8734bae166e5864` rebuilt the same 11,873,352-byte
release binary with the same SHA-256
`30a45e5a67963d1111d6ca69dd58dcae0129085ebbdf31db5c5f13752c2a4db2`.
Two fresh atomic captures then passed the frozen sequential-isolated protocol:

| Division | Rows | Elapsed | Solved | Historical | Gains / losses / wrongs | JSONL SHA-256 |
|---|---:|---:|---:|---:|---:|---|
| QF_LRA | 200 | 1,021,796 ms | 90 | 86 | 4 / 0 / 0 | `9bd45cc580884350cdd576eff6dcccd1f75fbae8b7d81244d6381f12d9bdad8c` |
| QF_IDL | 200 | 3,707,577 ms | 70 | 68 | 2 / 0 / 0 | `6aa63173b5dc00bd34e4dcfb028947a84caf997e407eeb7688f8a0b577a65c8f` |

Both captures used one worker at a time, inherited the 8 GiB limit, emitted
zero stderr, exited 0, and retained exact local/upstream identity. QF_LRA kept
`sc-39` as a typed normalization-resource `unknown` and gained four agreeing
UNSAT decisions. QF_IDL retained the formerly lost
`BubbleSort_safe_blmc016` UNSAT and GraphPartitioning SAT decisions through
`dl-online`, retained `lpsat-goal-18` UNSAT through `lia-dpll`, and added two
agreeing UNSAT decisions on MazeGeneration width 16 and `FISCHER14-9`.

Join artifact SHA-256 values are
`ea98f6ddafcf198e18e985b4599c7180957fa5ec9b39bdb0a944a6610649ae40`
for QF_LRA and
`ce43953b63b858124ccf2f199f19979bab15e6de8ed79f21e200988eb7c609e9`
for QF_IDL. Their strict zero-loss joins authorize QF_RDL next; QF_RDL was not
started in this wrap-up, and the three-division derivation remains forbidden
until its own atomic capture and join pass.
