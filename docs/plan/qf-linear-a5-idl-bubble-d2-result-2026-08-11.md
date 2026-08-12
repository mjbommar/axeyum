# QF linear A5 IDL BubbleSort D2 result — 2026-08-11

## Outcome

The [preregistered unchanged-binary ladder](qf-linear-a5-idl-dl-boundary-v2-preregistration-2026-08-11.md)
stopped successfully at its first rung. BubbleSort returned byte-identical,
replay-checked UNSAT through `dl-online` in all three observations at the
32,000 ms query setting. No fallback route ran. This establishes a nearby
existing-route boundary; it does not authorize a production budget change.

## Identity and observations

Source was exact clean
`d0e0d6ceac779b5cc3e2c1b5f3096c77780aecf9`. The retained 11,859,344-byte
release binary had SHA-256
`eec4813b557165ec95afc43912ad9fc2b5400ec94db5b7134ecacd50b100867d`.
The group started at `2026-08-11T22:03:55Z` with one-, five-, and fifteen-minute
loads 5.38, 7.33, and 6.71. Every fresh worker inherited the 8 GiB limit,
exited 0, and emitted zero stderr.

| Run | Verdict / terminal route | Wall time | Peak RSS | JSONL SHA-256 |
|---:|---|---:|---:|---|
| 1 | UNSAT / `dl-online` | 20.52 s | 147,580 KiB | `0e3fa1c99033d47e6ab97d9101110a12fa4f83564dfb2765a115af71c1f1258d` |
| 2 | UNSAT / `dl-online` | 17.83 s | 147,800 KiB | `0e3fa1c99033d47e6ab97d9101110a12fa4f83564dfb2765a115af71c1f1258d` |
| 3 | UNSAT / `dl-online` | 17.42 s | 147,936 KiB | `0e3fa1c99033d47e6ab97d9101110a12fa4f83564dfb2765a115af71c1f1258d` |

The 48,000 ms rung was not run. Full stdout, stderr, and `time -v` files remain
outside the repository under
`/home/mjbommar/.cache/axeyum/a5-idl-d2-d0e0d6cea` and are not mixed with the
failed V2 census.

## Interpretation

G1 and D2 now place both historical QF_IDL losses on the existing DL route:
GraphPartitioning decided in 18.82--19.19 seconds and BubbleSort in
17.42--20.52 seconds when the route received more than the shipped 18-second
maximum. B1 separately showed that removing per-atom fallback feasibility did
not recover BubbleSort. The evidence supports one structural extended-slice
candidate with complete fallback controls; it does not support weakening the
pre-SAT boundary or globally committing the whole query budget to DL.

Proceed only under the separately frozen
[extended-slice preregistration](qf-linear-a5-idl-extended-dl-slice-v1-preregistration-2026-08-11.md).
