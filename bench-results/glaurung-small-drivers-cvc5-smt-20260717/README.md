# Glaurung small-driver ordered cvc5 SMT baselines

- Date: 2026-07-17
- Source: the first accepted ADR-0217 trace for each driver
- Solver: cvc5 1.3.4 official Linux x86_64 libc++ static release, `f3b21c4`
- Solver binary SHA-256:
  `4a93548398445cf1a774655583f5465b156c26f63f2cdfb94f4728fdf7adde46`
- Repetitions: one unreported warm-up plus five measured runs per driver,
  pinned to CPU 3
- Per-check timeout: 250 ms
- Method: one process per repetition, full `(reset)` after every standalone
  query, model output enabled

ADR-0222 established the same cold-reset external-SMT point on Dptf. This
artifact widens that exact fail-closed runner to vwififlt, IntcSST, and
SurfacePen. Together the four artifacts cover every one of the 9,526 checks in
the accepted fair performance map.

| Driver | Checks | SAT / UNSAT | Median batch | Sample CV | Report SHA-256 |
|---|---:|---:|---:|---:|---|
| DptfDevGen | 561 | 317 / 244 | 2.593056 s | 0.4222% | `ce59b17cbba7f96aea005112f03118aad0eb94037cab27b7c5e2bcda2c8e0505` |
| vwififlt | 4,742 | 2,932 / 1,810 | 64.637115 s | 0.2162% | `3da5711407c306293f87a779e1fad167e91908fd19e3271cfd748779d5a92541` |
| IntcSST | 1,672 | 1,270 / 402 | 6.217003 s | 0.1639% | `2216dec3388ec77101a360f1cf74885da5ab8981d8ae6d10d0d587701e9714a8` |
| SurfacePen | 2,551 | 2,282 / 269 | 11.179779 s | 0.3899% | `c36c7e1335a09bd2066bb15be97c5becaa47be74e6d0b6a0e096551afcc8c483` |

Every measured repetition returns its exact expected verdict population with
zero Unknown. The complete stdout hash is byte-identical across all five runs
within each driver. Across the four-driver map cvc5 therefore agrees on 6,801
SAT and 2,725 UNSAT outcomes, and emits all 6,162 requested SAT value responses
plus only the 2,608 expected post-UNSAT `get-value` diagnostics.

## Interpretation

This closes neutral cvc5 verdict parity and cold-reset external-SMT breadth for
the accepted four-driver workload. It does not create a cross-boundary speed
ratio: the cvc5 batches include textual parsing and model printing, whereas the
accepted Z3/Axeyum cells are in-process and analyzed as paired per-occurrence
latencies.

The neutral timing order is itself useful regime evidence. vwififlt is by far
cvc5's slowest batch per check, while the Axeyum/Z3 warm map classified it as
parity; IntcSST is cvc5's cheapest per check while warm Axeyum wins there. A
single lexical-size or FFI story therefore does not explain cross-solver
behavior. Solver, outcome/purpose mix, exact reuse, and integration boundary
must remain explicit covariates.

Neutral warm/topology-equivalent performance is still open because cvc5 is
fully reset between checks. Standing generated multi-oracle fuzzing,
timeout-sensitive evidence, and authoritative finding parity also remain
publication blockers.
