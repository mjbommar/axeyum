# Glaurung four-driver retained cvc5 SMT control

- Date: 2026-07-18
- Source: the first accepted ADR-0215/0217 trace for each driver
- Solver: cvc5 1.3.4 official Linux x86_64 libc++ static release, `f3b21c4`
- Solver binary SHA-256:
  `4a93548398445cf1a774655583f5465b156c26f63f2cdfb94f4728fdf7adde46`
- Official archive SHA-256:
  `6cbc48ad8812b72abed32418a9f8b928c56c776d67377e63bc6b8f6bb2e40ac5`
- Repetitions: one unreported warm-up plus five measured runs per driver,
  pinned to CPU 3
- Per-check timeout: 250 ms
- Process boundary: one external cvc5 process per repetition

The `retained-lcp` runner validates the clean trace, query index, exact query
bytes, four source-cell verdicts, source owner, persistent/temporary partition,
and synchronized warm metadata. It emits one independent cvc5 solver session
per contiguous source owner. Persistent assertions move by their exact
content-byte longest common prefix using `push`/`pop`; the temporary suffix is
passed through `check-sat-assuming`, matching the two native fair-shadow cells.
A full `(reset)` and declaration prelude separate source owners. An owner that
reappears after reset is rejected rather than silently losing state.

The process remains external and textual. This is topology-equivalent at the
solver-state and owner boundary, not an in-process API or FFI-cost match.

| Driver | Checks | SAT / UNSAT | Retained median | Sample CV | Cold-reset median | Descriptive cold/retained | Report SHA-256 |
|---|---:|---:|---:|---:|---:|---:|---|
| DptfDevGen | 561 | 317 / 244 | 0.158184 s | 1.6132% | 2.593056 s | 16.3927x | `440df5bafe5918c0d3f51d47779096ba91dab3e00a0d6a7098eca810688f31c9` |
| vwififlt | 4,742 | 2,932 / 1,810 | 1.133353 s | 0.2764% | 64.637115 s | 57.0317x | `afce844c19708ce39615e793da968fd76551a85ab97770852b504d31e1718ff7` |
| IntcSST | 1,672 | 1,270 / 402 | 0.295296 s | 0.3739% | 6.217003 s | 21.0535x | `e8b47737455efc28846dd84561a2def473a979c77014c192d2bae4b3613a9e0b` |
| SurfacePen | 2,551 | 2,282 / 269 | 0.283179 s | 0.4251% | 11.179779 s | 39.4795x | `a8e7aae3d27b97d6074bc40970c912d2b10a21f4156d2a0680429e62cae77527` |

Every measured repetition preserves all 9,526 expected decisions: 6,801 SAT,
2,725 UNSAT, and zero Unknown. All 6,162 requested SAT value responses and only
the 2,608 expected post-UNSAT diagnostics are present. Complete stdout is
byte-identical across all five runs within each driver.

| Driver | Owner sessions | Persistent pushes / pops | Retained prefix occurrences | Temporary assumptions | Exact persistent snapshots |
|---|---:|---:|---:|---:|---:|
| DptfDevGen | 7 | 304 / 198 | 15,138 | 188 | 136 |
| vwififlt | 14 | 3,019 / 2,685 | 242,890 | 1,477 | 978 |
| IntcSST | 24 | 1,354 / 1,100 | 30,179 | 266 | 291 |
| SurfacePen | 43 | 2,398 / 940 | 307,592 | 147 | 166 |

The reports also preserve the distinction between the explorer's requested
retain depth and the effective identity-derived prefix used by the native
engines. Depending on sibling rewind, the effective prefix can be slightly
above or below that request; no difference exceeds four assertions, and every
transition is derived from the exact persistent assertion bytes.

## Interpretation

This closes the requested neutral warm/topology control on the accepted
four-driver tier. Within the same external cvc5 protocol, binary, traces, model
work, timeout, and CPU, retaining source-owner word-level state reduces the
aggregate batch time by 16.4x--57.0x relative to the accepted full-reset
control. Those factors characterize the cost of reparsing/rebuilding versus
retaining cvc5 state; they are not Axeyum solver speedups and are not divided
into the in-process Z3/Axeyum paired geomeans.

The result strengthens the workload-dependent paper framing: warm word-level
state is a first-order mechanism for a neutral mature solver too, but it does
not establish a universal cross-solver order. Timeout-sensitive neutral and
authority tiers, independent fuzz seeds/another neutral implementation, and
real-query term-to-CNF faithfulness remain open.

The reproducible runner is
`crates/axeyum-bench/examples/cvc5_smt_stream_bench.rs`; `cold-reset` remains
the default so the ADR-0222/0223 command line and batch hashes are unchanged.
