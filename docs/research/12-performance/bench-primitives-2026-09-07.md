# bench-primitives — a running diary, 2026-09-07

Status: in progress
Lane: `bench-primitives` (`docs/plan/status/1740-bench-primitives.md`)

## What this is

A diary, not a report. It records what was measured, what was expected, what
was found, and — the part worth the file — **where the expectation was wrong**.
A diary of confirmations is worth much less than one that records a surprise,
so the surprises are given their own headings and are not smoothed away
afterwards.

Subject: the three shared primitives every division above them pays for.

| crate | what it owns | benches before this lane |
|---|---|---|
| `axeyum-ir` | term arena + interning, `Value`, ground evaluator, LSB-first bit conversion | 1 (`arena_intern`) |
| `axeyum-bv` | term-to-AIG bit lowering, `lower_terms` / `IncrementalLowering` | **0** |
| `axeyum-smtlib` | SMT-LIB parser, sharing-preserving writer | **0** |

This lane follows [`microbenchmarks-2026-09-05.md`](../08-planning/microbenchmarks-2026-09-05.md),
which added the first seven benches in the workspace. It does **not** repeat
them.

## The rule this lane is held to

From the brief, and it is the reason for every "proxy for" paragraph below:

> A microbenchmark that does not predict the real workload is worse than none.
> Measured on this repo 2026-09-06: `cdclt_solve_php_6_7`, a 42-variable
> pigeonhole, says engine A is 3.4% faster than engine B — while on a
> 330,000-variable real skeleton the same swap decides 4 MORE files at 12.9%
> better PAR-2. The benchmark and the corpus disagreed in **direction**.

So each bench added here states, in its own module doc, the real workload it
stands for. Where that could not be shown, the doc says so instead of implying
otherwise.

## Method

- Host: `s4` (the shared dev box, hybrid CPU, 16 logical CPUs). Sibling lanes
  hold `s5`–`s7`; `scripts/cargo-serialized.sh` takes a **host-wide** flock, so
  a build's own wall clock is not a measurement.
- Pinned to the performance cores with `taskset -c 0-7`, matching
  [`frontier-ratchet-reference-frame.md`](../08-planning/frontier-ratchet-reference-frame.md).
  Unpinned, this host is measured 1.84x slower on the E-cores, which has
  already produced one phantom REGRESSION.
- `/proc/loadavg` recorded **before and after** every timing run. A number
  taken next to an orphaned process is not comparable to one taken after it is
  reaped, and this box has produced three orphans in one evening.

---

## Entry 1 — the committed corpus is not the parse workload

**Expected:** pick a representative committed SMT-LIB file, bench the parser on
it, done.

**Found:** there is no such thing. Measured over `corpus/**/*.smt2`,
1,101 files:

| bytes | files |
|---|---|
| < 1 K | 965 |
| 1 K – 10 K | 107 |
| 10 K – 100 K | 18 |
| 100 K – 1 M | 8 |
| > 1 M | 3 |

**88% of the committed corpus is under one kilobyte.** The megabyte-scale
inputs that motivated the ingest deadline in the first place are not in the
tree at all — `SmtError::DeadlineExceeded`'s own doc cites a **58 MB**
benchmark taking ~54 s to read, and the largest file committed here is 10 MB.

This matters before a single number is taken, because it decides what a parse
bench can honestly claim. A bench over the median committed file measures
**fixed per-call overhead**, not parsing. So `smtlib_parse` benches three
sizes (~2.7 K, ~50 K, ~1.1 M) and its module doc states plainly that the tail
is unrepresented and must be run from the fetched corpus.

**Where I was wrong:** I assumed "use a real corpus file" was sufficient to
satisfy the brief's proxy rule. It is not. A real file drawn from a
distribution that does not match production is still a proxy, and an
unlabelled one is the more dangerous kind — it *looks* like ground truth.

## Entry 2 — splitting ingest into its two passes

`parse_script` is two passes, not one: `read_all` builds an `SExpr` tree
(lex, paren-match, one `String` per atom), then the typed parser walks that
tree doing sort checks and `TermArena` construction. Benching only the whole
gives a number nobody can act on.

Both are benched over the *same* three files, so the pair is a decomposition:
`read_all` is a lower bound on `parse_script`, and the gap is what semantic
analysis costs. Prediction on record before running, so it can be scored:
**I expect `read_all` to be the minority of `parse_script` — under 40% — on
the large file, because the typed pass does interning and sort checking while
the reader only allocates.**

(Result recorded below once measured.)
