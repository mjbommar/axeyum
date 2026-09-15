# QF_NIA — what the clause estimate counts, and what z3 builds instead

Lane `NIA-TRACE`, 2026-09-15, measured at `f0904bfe2`. Sidecar for
[ADR-2112](../../docs/research/09-decisions/adr-2112-qf-nia-what-the-clause-estimate-counts.md).

## Population

Derived from the pinned Tier 1 ledger
[`bench-results/ledger/t1-QF_NIA-db31113fa.tsv`](../ledger/t1-QF_NIA-db31113fa.tsv)
(200 rows, one per file, with the full route trail), not from a board TSV — a
board is a snapshot and its divisions move.

| file | rows | what it is |
|---|---:|---|
| `all-200.txt` | 200 | every pinned row |
| `undecided-116.txt` | 116 | `verdict = unknown` |
| `decided-84.txt` | 84 | 78 `sat` + 6 `unsat` |
| `estimate-wall-44.txt` | 44 | every admissible width's estimate exceeds the 64 M cap |
| `estimate-wall-smallest-10.txt` | 10 | the ten smallest of those, by source bytes |

All 200 paths resolve on disk; 0 missing.

## What bound the 116, read from the ledger rather than from one route

`decline_reasons` is keyed, `decline_details` is POSITIONAL, and the two are
aligned by index before anything is counted — 115 of 116 rows align, 1 does
not and is reported as unaligned rather than guessed at.

Terminal reason (`bound_by` and that route's own detail):

| rows | route | detail |
|---:|---|---|
| 59 | `int-blast-ladder` | wall-clock timeout reached |
| 24 | `nia-linearize` | pre-SAT skeleton exceeds the joint resource boundary |
| 22 | `nia-linearize` | exhausted the configured timeout after N rounds |
| 4 | `int-real-relax` | nonlinear abstraction (3 capacity, 1 clock) |
| 4 | `nia-linearize` | reconstruction / branch-and-bound |
| 3 | other | |

And `int-blast-ladder`'s OWN recorded detail, whatever bound the row:

| rows | detail |
|---:|---|
| 49 | `estimated N CNF clauses before lowering exceeds budget 64000000` |
| 59 | `integer bit-blast width ladder: wall-clock timeout reached` |
| 4 | bounded-width / combined-theory |
| 4 | absent or unaligned |

**0 of the 84 decided rows carry the clause-estimate sentence anywhere.**

## The census — `census-undecided-116.tsv`

`crates/axeyum-bench/examples/nia_estimate_census.rs`, eight widths per file
(4, 8, 12, 16, 20, 24, 28, 32), 922 rows, **0 files over the memory ceiling and
0 dropped**. One file (`array_3-1-O0.smt2`) takes the parser's word-only
fallback and has no flat view, so the shape columns cover 115.

| | min | median | max |
|---|---:|---:|---:|
| `constant_width` | 2 | **17** | 101 |
| `bound_width` | 2 | **2** | 33 |
| `bounded_symbols` | 0 | 16 | 264 |
| `unbounded_symbols` | 3 | 289 | 13,537 |

`constant_width` is the smallest width at which `blast_integers` admits the
query at all; `bound_width` the smallest width holding every variable's own
declared two-sided range. A symbol with no such range is counted unbounded and
contributes nothing, so `bound_width` is a LOWER bound on what a per-variable
policy would need — it cannot overstate the gap.

- **95 of 115** files have `bound_width < constant_width`.
- 108 of 115 need three bits or fewer for their variables.
- 110 of 115 have at least one two-sided bounded symbol.
- 29 files have exactly ONE admissible rung of the eight sampled; 2 have none.

Partition by whether the estimate is the binding constraint at all:

| rows | |
|---:|---|
| **44** | every admissible width's estimate exceeds the 64 M cap |
| **69** | at least one admissible width fits — a real solve ran and returned `Unknown` |
| 2 | no admissible width at all |

The ladder returns its LAST rung's `Unknown` (`auto.rs:11664`), so all three
groups report the same width-32 sentence.

## Estimate versus actual — `estimate-vs-actual-10.tsv`

The actual count is the shipped lowering's, with the pre-lowering gate lifted
(`cnf_clause_budget = u64::MAX`) and the search stopped the moment it starts
(`resource_limit = 0`), so the number measured is the encoding and nothing else.

| estimate | actual | ratio |
|---:|---:|---:|
| 74,481,639 | 7,923,115 | 9.40x |
| 75,355,131 | 7,916,829 | 9.52x |
| 81,656,940 | 7,858,039 | 10.39x |
| 82,137,495 | 7,911,622 | 10.38x |
| 82,762,788 | 7,986,732 | 10.36x |
| 94,622,511 | 6,065,434 | 15.60x |
| 94,374,759 | 8,300,893 | 11.37x |
| 99,823,977 | 8,359,515 | 11.94x |
| 105,875,904 | 6,195,202 | 17.09x |
| 111,943,962 | 6,317,982 | 17.72x |

Every one encodes to 6.1–8.4 M clauses, an order of magnitude under the 64 M
cap that refused it. The ratio is 9.40x–17.72x and rises with the estimate.

**This does not license lifting the cap.** That was measured and refuted:
[`nia-deficit-diagnosis-2026-08-21.md`](../../docs/research/05-algorithms/nia-deficit-diagnosis-2026-08-21.md)
§4.1 raised the ceiling to 600,000,000 — above every estimate above — over all
49 `EncodingBudget` files and decided **0**; 44 became full-budget timeouts, 0
aborted on memory, and all 38 baseline decisions held.

### A note on the two pipeline points

This census blasts the RAW parse; production reaches the ladder only after
`int-real-relax` / `nia-linearize` have already interned into the live arena.
The same file reads 74,481,639 here and 74,329,095 in the 2026-08-21 note
(0.2 %), and 130,689,153 here against the ledger's 130,191,180 (0.38 %). The
`clause_estimate_attribution` v2 result records the same boundary effect at
+24/+39 clauses. These are the same quantity at two points in the pipeline and
no claim here rests on them being byte-identical.

## The z3 reference trace — `z3-engine-trace.sh`, `z3-trace-116.tsv`

Three arms per file, back to back on the same pinned core (s6, cores 1 and 3),
each with its own 24 s budget, an 8 GiB address-space ceiling and a hard kill
at 30 s:

| arm | what it runs |
|---|---|
| `default` | z3's own strategy for the logic in the file |
| `qfnia` | `(check-sat-using qfnia)` |
| `nla2bv` | `(check-sat-using (then simplify nla2bv smt))` — the bit-blast route |

For the tactic arms the original `(check-sat)` / `(get-*)` / `(exit)` commands
are dropped and the tactic call appended, so the assertion set is the file's.

The `engine` column is read from `-st` COUNTERS being nonzero, not from a key
being present and not from the verdict. Every QF_NIA query runs the SAT core
and the linear arithmetic layer, so naming those says nothing; what separates
the routes is which nonlinear machinery produced conflicts.

`test-stat-extraction.sh` is the control suite for that extraction, sourced out
of the sweep script so it tests the shipped functions rather than a copy: nine
checks — five positive, two negative (an absent key must come back empty), one
prefix-collision (`conflicts` must not be read off `nlsat-conflicts`, which
appears FIRST in the block), and one engine attribution over a purely linear
stat block that must come back `none`. It exits nonzero when any fails.

It exists because the first version of this sweep wrote 79 rows with EVERY
statistic column empty: `stat_of`'s greedy `.*` consumed the value it was meant
to capture, and `engine_of` reported `nlsat+grobner+nla+sat` for every file
because it asked whether a substring appeared anywhere. Both are recorded here
rather than quietly fixed, because an extractor that returns empty is
indistinguishable from an engine that did not run.

RESULTS: see ADR-2112 Part C.
