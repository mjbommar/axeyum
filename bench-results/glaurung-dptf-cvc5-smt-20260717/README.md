# Dptf ordered cvc5 SMT baseline

- Date: 2026-07-17
- Source trace: first accepted ADR-0215 Dptf repetition, Glaurung
  `4ae96cfd06a1abb72d1c3977f2dfd878680a9739`
- Driver SHA-256:
  `074be1b90deb21897538a6b093af9826e62610ffd878c92289af31c5ca3f724b`
- Solver: cvc5 1.3.4, official Linux x86_64 libc++ static release,
  `f3b21c4`
- Solver binary SHA-256:
  `4a93548398445cf1a774655583f5465b156c26f63f2cdfb94f4728fdf7adde46`
- Official archive SHA-256:
  `6cbc48ad8812b72abed32418a9f8b928c56c776d67377e63bc6b8f6bb2e40ac5`
- Repetitions: one unreported warm-up plus five measured runs, pinned to CPU 3
- Per-check timeout: 250 ms
- Report SHA-256:
  `ce59b17cbba7f96aea005112f03118aad0eb94037cab27b7c5e2bcda2c8e0505`

This is the first neutral word-level solver point on the exact Glaurung Dptf
stream. The runner validates the clean trace manifest, events and query-index
hashes, every query's content hash, every occurrence identity, and all four
source-cell verdicts before execution. It then reconstructs the exact 561-check
order from 377 unique SMT-LIB scripts.

One cvc5 process is used per repetition to amortize process startup. A full
SMT-LIB `(reset)` follows every check, so declarations, assertions, solver
state, and learned clauses do not cross query boundaries. The process receives
`--incremental --produce-models --tlimit-per=250`. This makes the cell a
**cold-reset external SMT integration** point: it includes SMT-LIB parsing,
solving, and textual model output, but not per-query process creation.

Every repetition returns the exact expected 317 SAT / 244 UNSAT / 0 Unknown
split. All 206 requested SAT value responses are present; the 216 scripts that
request values after UNSAT emit only cvc5's expected post-UNSAT diagnostic.
The complete stdout SHA-256 is identical in all five runs:
`29600f8079ba2c6b7a5a648a3629c5ac59d79799980ab3f875b274a31df6c5c8`.

The 5.63 MB batch has SHA-256
`3955ce0ba0d6ebd76e8299babcf2d23e0d36789b6a9bfb1672cfcf2e59ef3ead`.
Measured wall times are 2.594976, 2.588175, 2.609810, 2.579961, and 2.593056
seconds. The median is **2.593056 seconds**; the mean is 2.593196 seconds with
0.4222% sample CV.

## Interpretation

This closes a narrow but important reviewer gap: Z3 is no longer the sole
oracle on the real Dptf stream, and the artifact now contains a neutral
third-party cold-reset performance point. It does not produce a new speed
headline. The accepted Z3/Axeyum four-cell statistics are in-process and paired
per occurrence; this cvc5 number is aggregate external-protocol throughput and
must not be divided into those paired geomeans. Text parsing and model printing
are intentionally part of this integration boundary.

The result also does not close the warm representation mechanism selected by
ADR-0221: cvc5 is reset after each query and therefore retains no word-level
state. A neutral in-process or topology-equivalent warm API cell, broader
multi-driver replay, standing multi-oracle fuzzing, timeout-sensitive evidence,
and authoritative finding parity remain open.

The reproducible runner is
`crates/axeyum-bench/examples/cvc5_smt_stream_bench.rs`. The cvc5 binary came
from the official [cvc5 1.3.4 release](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.3.4).
