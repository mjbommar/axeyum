# Gate (b) measured: BatSat/native vs. CaDiCaL/Kissat on Axeyum CNF, 2026-09-05

Companion to the [2026-09-05 SAT/SMT performance and architecture
review](2026-09-05-sat-smt-performance-and-architecture-review.md), closing
its §2.2 item 4 and Recommendation 2. Full artifact:
[`bench-results/sat-core-gate-b-20260905/`](../../../bench-results/sat-core-gate-b-20260905/README.md).

## The gate

The [benchmarking and performance
methodology](../08-planning/benchmarking-and-performance-methodology.md)'s
Decision Gates make the native CDCL core's *priority* (not its existence —
that is settled, ADR-0002) contingent on two conditions on the public/client
tiers: (a) SAT solve time dominates end-to-end time, and (b) the best Rust
adapter shows a consistent material gap to CaDiCaL/Kissat on Axeyum-generated
CNF specifically. Gate (a) was measured true in June/July 2026 on p4dfa (SAT
share 0.974) and Noetzli (~0.95). Gate (b) had never been measured — no
artifact under `bench-results/` contained a CaDiCaL or Kissat run before this
one.

## What was run

`crates/axeyum-bench/examples/dump_dimacs.rs` (pre-existing, unmodified)
bit-blasts a QF_BV `.smt2` file to DIMACS through the same word-level
preprocessing the fair corpus runs use. Two corpora: **p4dfa**, the family
gate (a) was measured on, dumped **exhaustively (113/113 files, 0
failures)**; and **Noetzli**, whose full family is 1575 tiny files — not
tractable at a 20 s × 4-engine budget inside one session, so a **seeded,
deterministic 100-file sample** (`random.Random(20260905)`, list recorded in
the artifact directory) was carried through the sweeps instead. Both corpora
were dumped in full; only Noetzli's engine sweep is a sample.

Four engines, on byte-identical DIMACS, 20 s per instance, `taskset -c 0-7`
(the host is a hybrid P/E-core part), one engine at a time: BatSat
(`solve_with_rustsat_batsat_timeout`), the native proof-producing core
(`solve_with_drat_proof_within`, `proof_sat.rs`), CaDiCaL 3.0.1, and Kissat
4.0.4. A new example, `gate_b_sweep.rs`, drives the two internal engines and
checks every `sat` model — internal or external — against the CNF with
`CnfFormula::evaluate`, so all four engines' SAT answers are checked by the
identical trusted code path. Because a full 20 s×2-engine sweep over 113
files runs close to an hour and no single foreground tool call can span
that, `gate_b_sweep sweep` appends one TSV row per file and skips files
already present, so the same command re-run in bounded batches (`max_files`)
turns one long sweep into a sequence of short, resumable, single-call
batches — the mechanism, not just the result, is worth noting for the next
lane that needs a >10-minute measurement.

## Results

| Family | Files | BatSat decided | native decided | CaDiCaL decided | Kissat decided |
|---|---:|---:|---:|---:|---:|
| p4dfa (exhaustive) | 113 | 4 | 6 | 10 | 11 |
| Noetzli (100-sample) | 100 | 86 | 86 | 88 | 89 |

| Family | BatSat PAR-2 (s) | native PAR-2 (s) | CaDiCaL PAR-2 (s) | Kissat PAR-2 (s) |
|---|---:|---:|---:|---:|
| p4dfa | 38.729 | 38.107 | 37.203 | 36.941 |
| Noetzli sample | 5.604 | 5.605 | 5.247 | 4.613 |

Zero cross-engine sat/unsat disagreements and zero invalid SAT models across
every (engine, file) pair in both families (452 pairs on p4dfa, 400 on the
Noetzli sample).

## Verdict on gate (b)

**Mixed — not a clean "consistent material gap."**

- On p4dfa, the family the gate was framed around, CaDiCaL and Kissat decide
  4–7 more files than the two Rust engines at 20 s (10–11 vs. 4–6, out of
  113). The direction is as expected, but the scale is small — six files is
  not a wholesale unlock, and PAR-2 for all four engines sits in a narrow
  36.9–38.7 s band because most of this family times out for everyone at 20
  s. This family is a place where the gap exists but is modest.
- On the Noetzli sample, the gap nearly disappears: 86–89/100 decide across
  all four engines, and Kissat's PAR-2 edge over BatSat/native (4.6 s vs. 5.6
  s) is real but the decide-rate difference is 2–3 files. This is the
  "easy" family (high SAT share came from a large decided population), and
  it does not show a material gap.
- **The native proof core is never worse than BatSat and sometimes
  meaningfully better** (6 vs. 4 decided on p4dfa; tied on the Noetzli
  sample; never slower PAR-2). Nothing measured here supports BatSat as the
  stronger in-tree engine — if either Rust engine should become the default,
  the data points at the native core, which also already carries the LRAT
  certification route (ADR-0613).
- Reading the two families together: the gap to CaDiCaL/Kissat is largest
  exactly where axeyum's own pipeline already times out most (p4dfa, per the
  July 2026 measurement of only 8/113 decided at 20 s in production), and
  smallest where axeyum already decides most of the corpus. That is more
  consistent with "the CDCL search itself is the bottleneck on the hardest
  instances, but is not the dominant cost on typical ones" than with a
  blanket claim that the Boolean engine is the thing to fix next everywhere.

**What this does not establish**, in full: see the artifact README's
"What this does not establish" section — in short, the Noetzli number is a
sample not a census; this measures pure-CNF CDCL strength only, saying
nothing about the `CdclT` engine every non-QF_BV division actually runs on
(D1 in the parent review); the host carried heavy, uncontrolled ambient load
throughout (`uptime` 12–33 typical, one spike to 111) despite core pinning,
so treat the engine *ordering* as more reliable than the absolute seconds;
and no profiling was done to explain *why* CaDiCaL/Kissat decide the extra
p4dfa files.

## Net

Recommendation 2 of the parent review ("measure gate (b)... decides whether
the native core becomes the default and whether D1's third engine should be
replaced rather than tuned") is now answered with data rather than left
open: the gap is real but modest and family-dependent, which weakens rather
than strengthens the case for jumping the native-core-as-default queue on
gate (b) alone. It does *not* weaken the case built independently in D1/D2
of the parent review — the `CdclT` engine's missing clause arena, blocking
literals, and thin theory interface are architectural facts about a
different code path than what this experiment measured, and remain the
larger, unmeasured-here opportunity.
