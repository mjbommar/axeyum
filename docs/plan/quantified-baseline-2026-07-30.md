# First measured quantified baselines — UFLIA, and why UF is blocked

**Date:** 2026-07-30
**Lane:** A (quantifiers), task A1.
**Why:** UFLIA is the largest capability gap in the library — 10,128 benchmarks,
cvc5 wins SMT-COMP 2025 at **58.1 %** (1,656/2,849), and axeyum had **no honest
row at all**. The only quantified SCOREBOARD entries were `LIA` 0/12 and `UF`
0/5, both from the cvc5 regression suite rather than the library. You cannot
close a gap you have not measured, so this measures it.

## Method

The committed slices under `corpus/public-curated/` come from the **cvc5
regression suite**, which is why they are small enough to vendor. They are not
the SMT-LIB library, and for quantifiers that distinction is the whole point:
SMT-COMP measures UFLIA on families like `sledgehammer`, `tokeneer`, `simplify2`
and `boogie`, which exist only in the staged library.

So the slice is drawn from the staged library via
[`scripts/select-quantified-slice.py`](../../scripts/select-quantified-slice.py),
and it is **deterministic** rather than sampled — no clock, no RNG, no seed to
lose. Quotas are proportional to family size with every family guaranteed at
least one file; each family contributes an even **stride** through its sorted
list rather than a prefix, because generated families are ordered and a prefix is
systematically unrepresentative. Verified to reproduce byte-for-byte.

Run at the same config the committed baselines use: `--backend solver
--rewrite off --compare-z3 --timeout-ms 10000 --jobs 4`.

## UFLIA: 67 / 300 = 22.3 % decided, DISAGREE = 0

300 files stratified across 14 families out of a 10,128 population.

| Family | n | decided | % | breakdown |
|---|---:|---:|---:|---|
| sledgehammer | 102 | 9 | 8 % | 78 unsupported, 15 unknown |
| simplify2 | 68 | 11 | 16 % | 33 unknown, 24 unsupported |
| **tokeneer** | 54 | **46** | **85 %** | 7 unknown, 1 unsupported |
| boogie | 34 | 0 | 0 % | **33 unknown**, 1 unsupported |
| simplify | 24 | 0 | 0 % | **24 unsupported** |
| grasshopper | 10 | 0 | 0 % | 8 unsupported, 2 unknown |
| 8 small families | 8 | 1 | — | mostly unsupported |

Totals: **0 sat, 67 unsat, 92 unknown, 141 unsupported, 0 errors, DISAGREE = 0.**

Three things this says that estimates did not:

1. **Every single decision is `unsat`. Zero `sat`.** This is direct confirmation
   that the general **sat direction is the hole**, exactly as
   [`lane-a-quantifiers.md`](agent-program-2026-07-28/lane-a-quantifiers.md)
   argued from the 765-row gap selection — now corroborated on the real library.
2. **`unsupported` (141) outweighs `unknown` (92).** Nearly half the slice is a
   *feature or parse* gap, not a search gap. The cheap-encoding-first advice in
   [`decide-rate-frontier-2026-06-28.md`](decide-rate-frontier-2026-06-28.md) §2
   applies before any MBQI investment.
3. **The families split cleanly by failure mode, and the split is actionable.**
   `tokeneer` is already at 85 %. `boogie` is 0 % but **97 % `unknown`** —
   parsed, supported, undecided, so it is a *search* target. `simplify` is 0 %
   and **100 % `unsupported`** — a feature target. Those want different work, and
   without this table they would have been treated as one bucket.

For scale against the frontier: cvc5's 58.1 % is on the SMT-COMP selection, which
strips every benchmark all solvers solve in under a second, so it is a harder
population than this stratified sample. The gap is real and large; it is not
36 points on identical inputs.

## A conformance defect found on the way — fixed

One file reported `parse-error` and tripped the harness's integrity alarm, which
refuses to count an operational error as a result. The literal was `2^256 - 1`
(max `uint256`) from `20230314-Jaroslav-Bendik-Certora`, a family that verifies
Ethereum contracts.

SMT-LIB `Int` is unbounded, so that numeral is well-formed input; `Value::Int` is
an `i128`, so it is out of *representational* reach. Reporting `SmtError::Syntax`
claimed the benchmark was malformed, which is false, and converted a decline into
an error. It now returns `Unsupported`. Errors went 1 → 0 and the alarm cleared.

Whether `Int` should carry arbitrary precision end-to-end is a separate,
cross-crate question — the machinery exists in-tree as precedent (TL2.6 replaced
`Lit::Nat(u128)` with canonical `NatLit(BigUint)`; `axeyum-ir` has `WideUint`) —
but it needs its own ADR. It is parity-relevant: **we cannot decide what we
cannot parse**, so a bounded `Int` silently excludes the crypto and
smart-contract corner of the library from any measurement.

## UF is BLOCKED: the deadline does not bound one route

The UF baseline could not be produced. The 300-file run **aborted the entire
measurement** at a 32 GiB cap (`memory allocation of 24576 bytes failed`, exit
134, no artifact). Six files exceed a 4 GiB cap individually at only a **2 s**
solver timeout:

- `20170428-Barrett__cdt-cade2015__…_1210194.smt_in.smt2`
- `sledgehammer__FFT__uf.{556474,760434,885304}.smt2`
- `sledgehammer__TwoSquares__uf.{607512,730058}.smt2`

Two clusters plus one CADE datatypes file, so it is shape-specific rather than
size-driven — the FFT file is only 55 KB (466 asserts, 415 `forall`, 57
`declare-sort`, `:status unknown`).

### The measurement that makes it unambiguous

Same file, same `solve_smtlib` entry point, varying only the configured budget:

| `--timeout-ms` | wall | maxRSS |
|---:|---:|---:|
| 250 | 1.70 s | 305 MB |
| 1000 | 1.71 s | 305 MB |
| **2000** | **150 s (killed)** | **15.8 GB** |

A cliff, not a gradient. And varying only the *address-space* limit at a fixed
2000 ms budget:

| `ulimit -v` | wall | maxRSS | outcome |
|---|---:|---:|---|
| 6 GiB | 3.3 s | 305 MB | completes |
| 24 GiB | 150 s (killed) | 15.8 GB | still growing — **3/3 reproducible** |

**Consumption is governed by available address space, not by the configured
deadline.** A 2-second budget produced a 150-second, 15.8 GB run — 75× over
budget — and it only stops when an external `ulimit` refuses. That is the
standing rule violated outright: *"Graceful `unknown`, never OOM/crash. Every
solving path must degrade to `Unknown` under a **deterministic** resource bound
— no unbounded memory/time on adversarial input."*

It is also the same class as the ADR-0373 `let`-normalization blowup fixed
earlier the same day: work performed outside the deadline's reach. STATUS already
names the shape under P2.6d — *"finer cooperative polling inside individual
recursive encoders remains performance-hardening work"* — and this is a concrete
reproducer on real library input, which that note lacked.

### Localized to the SMT-LIB front door, not `check_auto`

At an identical 2000 ms budget and 6 GiB cap:

| entry point | wall | maxRSS |
|---|---:|---:|
| `solve_smtlib` (`smtcomp_cli`) | 3.3 s | 305 MB |
| `check_auto` (`explain_corpus`) | **0.10 s** | **11 MB** |

`check_auto_explained` declines in 0.1 s and names why:

```
probe: fragment {quant,uf}
euf-online:  declined (incomplete: boolean skeleton outside the online CDCL(T) encoder)
euf-offline: declined (incomplete: boolean skeleton undecided)
ufbv-declared-sort-lazy: declined (unsupported)
```

So the runaway is on a path `solve_smtlib` takes and `check_auto` does not. The
difference is the entry point: `solve_smtlib` calls **`solve`** (the
quantifier-aware entry — normalization, skolemization, the quantified portfolio),
while `explain_corpus` calls `check_auto` (the quantifier-free dispatcher). With
415 `forall` and 57 `declare-sort`, the runaway is inside the quantified
portfolio.

### One hypothesis tested and REFUTED — do not repeat it

The obvious suspect was finite-domain expansion. `expand_quantifiers`
(`crates/axeyum-rewrite/src/quantifiers.rs`) bounds itself with
`MAX_EXPAND_INSTANCES = 1 << 20`, and a million materialized instances plainly
cannot fit in 2 seconds or a few hundred megabytes — so the bound looked like a
*termination* bound rather than a *resource* bound, which would explain
everything.

It is not the cause. Lowering `MAX_EXPAND_INSTANCES` from `1 << 20` to `1 << 12`
— a 256× reduction — rebuilt and re-measured gave **150 s / 15.8 GB again, 2/2,
byte-for-byte the same behaviour**. The experiment was reverted.

That eliminates expansion and leaves the rest of the quantified portfolio:
instantiation/e-matching rounds, MBQI model construction, or the valid-universal
subchecks. Recording the refutation because the hypothesis is the one any reader
would form first, and it costs a build plus two runs to re-disprove.

Profiling was attempted and did not work in this environment: `perf record`
produced a zero-byte file (restricted `perf_event_paranoid`), and `gdb -p … -batch
-ex bt` returned no frames. The next attempt should either fix the profiling
permissions or instrument the portfolio's route boundaries directly with
timing/allocation prints, which is what actually localized the ADR-0373 blowup
after two failed rounds of reasoning.

## Next, in order

1. **Bound the runaway route** before any further UF work — it blocks the
   division's measurement entirely, not just six files. Localize which phase
   allocates by instrumenting per-phase growth on the FFT reproducer, exactly as
   the ADR-0373 diagnosis was done: measure, do not theorize. Two earlier
   attempts at that bound failed on reasoning alone.
2. **Then produce the UF baseline.** UF is the cheapest quantified entry point —
   cvc5 wins it with only **40.5 %**, the runner-up is 410 behind, and **59 % of
   the division is unsolved by anyone**.
3. **Then split UFLIA work by failure mode**, using the table above rather than
   one aggregate: `simplify`-style `unsupported` is a feature/parse target,
   `boogie`-style `unknown` is a search target, and they are not the same job.
