# The four datatype divisions — the first board rows, and what they found

**2026-09-12, lane `dt-divisions`.** `UFDT` (4,569), `UFDTLIRA` (7,749),
`AUFDTLIRA` (11,043), `UFDTNIRA` (4,424) — **27,785 files** — had never carried
a parity row. These are the first.

## Protocol

200 files per division from the stride-pinned lists in
`bench-results/parity-lists/`, committed **before** anything was run
(`UFDT` at `49a0e2698`, the other three at `62e55bdd1`). Per file: **24 s wall,
8 GiB address space**, three solvers **interleaved per file** (all three finish
file N before any starts N+1) on the same pinned core pair of the same idle
homogeneous box (`s5`/`s6`/`s7`, Ryzen 7 7840HS, load < 0.1 at launch), with the
solver that goes first rotating per file. Units differ and are set accordingly:
`z3 -T:24` (SECONDS), `cvc5 --tlimit=24000` (MILLISECONDS).

Each division's 200 files were split into three modulo-interleaved shards
(`NR%3`) so every shard spans the whole division; a shard is the unit that runs,
and the merged TSV is re-ordered back into the pinned list's order, so the
artifact does not encode the shard split.

**The wrapper timeout is `24 + 16 s`, not `24 + 8`.** A previous census used +8
under load, killed 17 processes, and produced rows that read as "no reason".
Every run records its own outcome in a per-solver `*_k` column: `ok`,
`wrapper-killed`, `rc134` (the 8 GiB address-space cap firing), `sigkill`.
**No row in these boards is `wrapper-killed`.**

Runner: `shard-run.sh` (this directory). Solvers: axeyum at `62e55bdd1`,
z3 4.13.3, cvc5 1.3.4.

## The rows (baseline, before ADR-1927)

| division | files | axeyum | z3 | cvc5 |
|---|---:|---:|---:|---:|
| UFDTLIRA | 200 | **66** | 181 | 158 |
| UFDT | 200 | **22** | 66 | 78 |
| UFDTNIRA | 200 | **5** | 173 | 183 |
| AUFDTLIRA | 200 | **0** | 176 | 176 |

**Soundness: 0 disagreements on all four divisions, three independent checks** —
the declared `:status`, z3, and cvc5. `AUFDTLIRA` decides nothing, so its zero
is vacuous and is not evidence; the other three are not.

## Reading them

- **The reference is not one solver, and it is not the same solver in every
  division.** On `UFDTLIRA`, z3 decides 23 files cvc5 does not and cvc5 decides
  **0** that z3 does not — the leader there is z3, not the datatype solver of
  record. On `UFDTNIRA` and `UFDT`, cvc5 leads. Name the reference when you
  quote a gap.
- **cvc5's `UFDT` row is a depressed floor: 100 of its 200 runs ended in
  `rc134`**, the 8 GiB address-space cap. That is the parity protocol's cap and
  those count as not solved, but the number is not "cvc5 decides 78 of 200 UFDT
  benchmarks". A bounded check: 5 of those 100 files re-run at a **24 GiB** cap,
  same 24 s — cvc5 returned `unknown` on all 5, so the cap was not hiding
  verdicts on that sample. 5 of 100 is a spot check, not a clearance.
  `AUFDTLIRA` has 2 such rows and `UFDTNIRA` 13.
- `UFDTLIRA` at 24 s decides 66/200 (33 %), while a 40-file 3 s census on
  2026-09-12 put it at 19/40 (47.5 %). Different samples, and 40 files carry a
  wide interval; the 200-file board is the number to quote.

## What the `AUFDTLIRA` zero turned out to be

A zero against two references that each decide 88 % of the same files, mostly in
under a tenth of a second, is not what a capability gap looks like. `--trace`
said `attempts=2` on a twenty-rung ladder, at 1 ms, quoting a `QF_UFBV`
Ackermann restriction for a quantified benchmark with no bit-vector in it.

Three quantified-ladder rungs were propagating a *speculative sub-solve's*
`SolverError::Unsupported` out of `solve`, so a backend refusing the fragment of
a query the solver had **built itself** became the file's answer and the
seventeen rungs below never ran.
[ADR-1927](../../docs/research/09-decisions/adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md)
is the fix;
[the measurement note](../../docs/research/03-measurements/the-dt-blocker-census-was-measuring-the-ladder-2026-09-12.md)
is the full write-up.

### The A/B (`ab/`)

Per-file, against the same binary without the guards, arms alternating per file,
back to back on the same pinned cores, 10 s / 8 GiB, 200-file stride samples.
Runner: `ab.sh`.

| division | base | guarded | newly decided | decided → undecided | flips |
|---|---:|---:|---:|---:|---:|
| AUFDTLIRA | 0 / 200 | **62 / 200** | 62 | 0 | 0 |
| UFDTLIRA | 70 / 200 | **75 / 200** | 5 | 0 | 0 |
| UFDT | 23 / 200 | **26 / 200** | 3 | 0 | 0 |
| UFDTNIRA | 10 / 200 | 10 / 200 | 0 | 0 | 0 |
| **UF (control)** | 83 / 189 | 83 / 189 | 0 | **0** | **0** |

`UF` is the control: an established quantified division, already on the parity
board, where the guards must cost nothing. They cost nothing.

### The verification (`verify/`)

All **70** newly decided files, cross-checked at 24 s on the same box. Every one
is `unsat`, and every one was *comparable* on all three checks — no check was
silently vacuous. Runner: `verify.sh`.

| check | comparable | disagreements |
|---|---:|---:|
| declared `:status` | 70 of 70 | **0** |
| z3 4.13.3 | 70 of 70 | **0** |
| cvc5 1.3.4 | 70 of 70 | **0** |

### The corrected blocker census

The census these divisions were previously mapped by
(`bench-results/dt-divisions-20260912/`) was measuring which rung refuses first.
`AUFDTLIRA`, undecided files, before and after:

| refusal | before | after |
|---|---:|---:|
| eager Ackermann, array-valued function results | **147** | **3** |
| `datatype_native`: array/UF-sorted datatype FIELDS (ADR-0022) | 0 | **70** |
| UF applied to a datatype argument (ADR-1920) | 7 | **32** |
| `is`/`select` over a non-variable datatype term | 0 | **13** |
| quantified / e-matching budget | 0 | **12** |
| parse: nested array element sort | 4 | **5** |

The `*_giveup` columns of the `ab/` TSVs carry both arms for every file, so the
table is re-derivable rather than quoted.

## Cost

A query the ladder refused in 1 ms now runs all twenty rungs and can spend its
whole budget. The A/B lost **0** verdicts to that at 10 s and the `UF` control
lost 0, but a sweep over these divisions is much slower in wall clock than it
was. The old speed was the speed of being wrong.
