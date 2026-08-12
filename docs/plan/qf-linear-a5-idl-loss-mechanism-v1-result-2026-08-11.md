# QF linear A5 IDL loss-mechanism v1 result — 2026-08-11

## Outcome

The [preregistered](qf-linear-a5-idl-loss-mechanism-v1-preregistration-2026-08-11.md)
discriminators closed one proposed mechanism negatively and located one nearby
existing-route boundary:

- B1's search-free atom validator did not recover BubbleSort. All three target
  observations remained typed `unknown`, so the target gate failed before the
  other matrix cases. The candidate code was removed.
- G1's unchanged solver returned replay-checked SAT through `dl-online` in all
  three 32-second observations. This is diagnostic evidence only; no production
  timeout or route changed.

Neither result authorizes QF_RDL, a 200-row run, a production timeout change, or
census credit.

## B1 — rejected atom-admission candidate

The candidate was built from base
`8c1d3655cfd77d3a19b523b2be8e1a5c1dea8a15`. It replaced only per-atom
single-constraint feasibility calls with the same Int/Real linearizers and
added a focused fragment-boundary test. Before measurement, both focused tests
passed with nonzero counts, strict full-feature solver-library Clippy passed,
and the complete solver library passed 1,092/1,092 tests.

The 11,865,240-byte candidate binary had SHA-256
`20a64e7d21a7bdc376c2c74d1d5a94e79b425b69552de695cf889681f936285e`.
The group started at load 4.04. Under the inherited 8 GiB limit and 24,000 ms
query setting, BubbleSort returned `unknown` in 3/3 observations, each with zero
stderr and exit 0:

| Run | Wall time | Peak RSS | Terminal admitted atoms | JSONL SHA-256 |
|---:|---:|---:|---:|---|
| 1 | 42.95 s | 182,668 KiB | 4,779 | `435ab7ed74ed390894c34e8d242559cfbcce2c0f826b5a9f50b63b0fd082e892` |
| 2 | 42.94 s | 184,868 KiB | 4,777 | `c58634fbd4f9f5c4c0eb7191e925e81fd5c83ae4037658b23933de4b279e415a` |
| 3 | 42.94 s | 185,228 KiB | 4,825 | `e598fe9dbea73ef4637e7e3e56468125e807542254f56c532a87417ad460d1d4` |

The target required UNSAT in 3/3. The remaining GraphPartitioning, maze, and
`lpsat-goal-18` observations were therefore unnecessary and were stopped. The
candidate did not materially move the construction boundary and is rejected.
Its production diff is absent from the committed tree. Full per-run files
remain under `/home/mjbommar/.cache/axeyum/a5-idl-b1-matrix`.

## G1 — accepted diagnostic, no production change

G1 used the unchanged exact `d0e0d6ceac779b5cc3e2c1b5f3096c77780aecf9`
source and its 11,859,344-byte release binary with SHA-256
`eec4813b557165ec95afc43912ad9fc2b5400ec94db5b7134ecacd50b100867d`.
The group started at load 5.15. All three fresh 32,000 ms observations returned
the same replay-checked SAT record through `dl-online` with SHA-256
`a274e2785023fcb6c8d4305a22c2f4a43c289fa4c8d5e22fceaa36f98a1fb1c4`,
zero stderr, and exit 0:

| Run | Wall time | Peak RSS |
|---:|---:|---:|
| 1 | 19.19 s | 30,516 KiB |
| 2 | 19.13 s | 30,432 KiB |
| 3 | 18.82 s | 30,376 KiB |

The shipped 24-second query gives the DL probe an 18-second slice, while this
diagnostic supplied a larger slice and decided just beyond that boundary. Any
production response requires a new preregistration with the original
allocation-abort controls and the complete retained QF_IDL/QF_RDL decision set.
The full diagnostic files remain under
`/home/mjbommar/.cache/axeyum/a5-idl-g1-d0e0d6cea`.

## Next boundary

Preregister, but do not yet implement, two separate bounded follow-ups: a
BubbleSort front-end discriminator based on the still-observed construction
boundary, and a GraphPartitioning DL-slice candidate whose control set can
detect fallback starvation. Keep their target and retention gates separate.
