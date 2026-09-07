# QF_LRA theory side — the measurement log

Companion to [the diary](lra-theory-side-2026-09-07.md). This file holds the
numbers; the diary holds the reasoning and the hypotheses they falsified.

Protocol for every table below: idle **s7** (16 cores, 26 GiB), `taskset -c 0-7`,
24 s / 8 GiB per file, one file at a time, arms run in separate passes with the
binaries confirmed different by `sha256sum`, `/proc/loadavg` recorded before and
after each pass. Counters are preferred over wall time wherever they answer the
question, because they are clock-free: two runs minutes apart differ by up to
±20% on allocation-heavy work, and a counter does not.

Population: `bench-results/adr-1701-slice-1-20260905/qf_lra_population.tsv`,
33 files.

## 1. The baseline, before any change (`75286df9`)

The `; theory-layer` line from `smtcomp_cli --trace`, one row per file that ran a
CDCL(T) route to completion. `fchk` is `final_checks`, `fcconf` the ones that
answered `Conflict`, `core/c` the mean conflict-core width in literals, `rows/c`
the mean live-row count at a check, `piv/c` simplex pivots per check, `apc`
`assert_partial_conflicts`, `prop` `propagations_offered`.

| file | verdict | ms | fchk | fcconf | core/c | rows/c | piv/c | apc | prop | decisions |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `Heizmann/_standard_two_index_06…` | unknown | 24024 | 5737 | 5736 | 11.9 | 389.1 | 18.3 | 137 | 78251 | 815213 |
| `Heizmann/_count_by_k…` | unknown | 24020 | 2592 | 2591 | 13.7 | 340.8 | 38.1 | 15 | 43209 | 420789 |
| `2019-ezsmt/blending/1` | unsat | 6903 | 20732 | 20732 | 46.3 | 307.9 | 2.2 | 15 | 79 | 48532 |
| `2019-ezsmt/blending/5` | unsat | 6197 | 21138 | 21138 | 46.7 | 306.3 | 1.8 | 14 | 7793 | 57456 |
| `TM/p-driverlogNumeric_s7` | sat | 163 | 499 | 498 | 128.0 | 255.0 | 3.1 | 106 | 0 | 7827 |
| `TM/p5-driverlogNumeric_s9` | unsat | 289 | 0 | — | — | — | — | — | — | 4888 |
| `clock_synchro/…_2clocks` | unsat | 4988 | 30 | 29 | 9.0 | 176.8 | 2.2 | 7 | 59 | 2103 |
| `clock_synchro/…_4clocks` | unknown | 24266 | 58 | 57 | 8.5 | 364.1 | 2.0 | 11 | 197 | 8355 |
| `clock_synchro/…_6clocks` | unknown | 24825 | 84 | 83 | 8.5 | 592.0 | 2.1 | 15 | 389 | 19781 |
| `clock_synchro/…_8clocks` | unknown | 24729 | 110 | 109 | 8.5 | 859.5 | 2.2 | 19 | 645 | 36201 |
| `miplib/pp08a-1000` | unknown | 24033 | 30443 | 30443 | 138.2 | 527.0 | 0.5 | 339 | 0 | 1892449 |

The other 22 files printed **no** `; theory-layer` line at all — no CDCL(T)
route reached a verdict on them. That is the atom-cap class (section 4), not the
timeout class, and the census does not separate them.

**Decided at baseline: 7 of 33.**

### Where the time actually goes

| file | ms | `theory_final_check` | `theory_propagate` | `boolean_propagate` |
|---|---:|---:|---:|---:|
| `Heizmann/_standard_two_index_06…` | 24024 | 16984 (71%) | 6332 (26%) | 170 |
| `Heizmann/_count_by_k…` | 24020 | 16627 (69%) | 3157 (13%) | 71 |
| `blending/1` | 6903 | 6396 (93%) | 325 (5%) | 61 |
| `blending/5` | 6197 | 5576 (90%) | 439 (7%) | 59 |
| `miplib/pp08a-1000` | 24033 | 3288 (14%) | **18051 (75%)** | 1027 |
| `clock_synchro/…_4clocks` | 24266 | 3 | 46 | 1 |
| `clock_synchro/…_6clocks` | 24825 | 7 | 175 | 3 |
| `clock_synchro/…_8clocks` | 24729 | 13 | 461 | 6 |

## 2. The A/B, three arms

Arm **base** = `75286df9` (the counters, no behaviour change).
Arm **cand** = the scan filter + Stein's binary GCD + the integer fast paths.
Arm **c2** = the scan filter + **narrowed Euclid** + the integer fast paths.

All three arms produce **byte-identical counters** on `blending/1` — 20 732 final
checks, 46 618 pivots, 216 280 bound retractions, 20 791 learned clauses — so
every wall-time difference below is arithmetic and scan cost alone, with the
search trajectory held fixed. That is what makes the comparison a measurement of
the change rather than of the search.

| file | base ms | cand ms | c2 ms | c2/base |
|---|---:|---:|---:|---:|
| `blending/1` | 6903 | 11718 | 5942 | 0.86 |
| `blending/5` | 6197 | 10290 | 5265 | 0.85 |
| `TM/p-driverlogNumeric_s7` | 163 | 126 | 110 | 0.67 |
| `TM/p5-driverlogNumeric_s9` | 289 | 204 | 203 | 0.70 |
| `clock_synchro/…_2clocks` | 4988 | 5271 | 4245 | 0.85 |
| `spider_benchmarks/frame_prop` | 7857 | 6555 | — | — |
| `spider_benchmarks/fs_not_sc_seen` | 5368 | 4593 | — | — |
| `spider_benchmarks/no_op_accs` | unknown 24102 | **unsat 19229** | — | — |

**Decided: base 7/33, cand 8/33.**

## 3. The atom-cap census class, re-measured after ADR-1752

All 22 files of the 33-file population that printed **no** `; theory-layer` line
at baseline, re-run on the final binary at `--memory-limit-mb 8192 --trace`, with
peak RSS from `/usr/bin/time -f %M`. The `give-up` column is the
`UnknownReason` the binary used to discard.

| file | verdict | ms | peak RSS (MiB) | give-up kind |
|---|---|---:|---:|---|
| `sal/carpark/Carpark2-ausgabe-8` | unknown | 24234 | 915 | Timeout |
| `sal/gasburner/gasburner-prop3-12` | unknown | 24073 | 498 | Timeout |
| `sal/gasburner/gasburner-prop3-9` | unknown | 24233 | 398 | Timeout |
| `sal/pursuit/pursuit-safety-16` | unknown | 24473 | **3392** | Timeout |
| `sal/pursuit/pursuit-safety-5` | unknown | 24083 | 678 | Timeout |
| `sal/tgc/tgc_io-nosafe-4` | unknown | 24243 | 657 | Timeout |
| `sal/tgc/tgc_io-safe-20` | unknown | 24618 | **8699** | Timeout |
| `sc/sc-5.base.cvc` | unknown | 24067 | 291 | Timeout |
| `sc/sc-7.base.cvc` | unknown | 24100 | 378 | Timeout |
| `sc/sc-9.base.cvc` | unknown | 24099 | 547 | Timeout |
| `sc/sc-11.base.cvc` | unknown | 24259 | 747 | Timeout |
| `sc/sc-13.base.cvc` | unknown | 24270 | 977 | Timeout |
| `sc/sc-15.base.cvc` | unknown | 24408 | 1239 | Timeout |
| `sc/sc-17.base.cvc` | unknown | 24482 | 1529 | Timeout |
| `sc/sc-19.base.cvc` | unknown | 24560 | 1850 | Timeout |
| `sc/sc-21.base.cvc` | unknown | 24565 | 2202 | Timeout |
| `sc/sc-23.base.cvc` | unknown | 24345 | 2584 | Timeout |
| `sc/sc-25.base.cvc` | unknown | 24883 | **2996** | Timeout |
| `spider_benchmarks/frame_prop` | **unsat** | 6770 | 204 | — |
| `spider_benchmarks/fs_not_sc_seen` | **unsat** | 4737 | 201 | — |
| `spider_benchmarks/no_op_accs` | **unsat** | 19904 | 674 | — |
| `spider_benchmarks/reint_to_least` | unknown | 24238 | 771 | Timeout |

**Peak RSS: min 201 MiB, median 759 MiB, max 8 699 MiB across 22 files.**

Three readings, and the first is the one that matters for the census:

1. **Not one of these 22 files is refused by the memory budget.** Every give-up
   is `kind=Timeout`. The census class the plan calls "23 admission declines at
   the 1,024-atom cap" is, once the cap is a budget, **23 search timeouts**. The
   division's loss census is not a two-way split; it is one class with a
   misattributed subset.
2. **The memory these files use is not the LRA theory's.**
   `QF_LRA/sc/sc-11.base.cvc.smt2` reports `resident set 617 MiB … at backend
   entry` under a 400 MiB limit — before the LRA route runs at all. Whatever
   holds 617 MiB there is upstream of everything the atom cap was guarding.
3. **One file of 22 genuinely exceeds 8 GiB.** `sal/tgc/tgc_io-safe-20.smt2`
   peaks at 8 699 MiB, which is why it reads `crash-or-oom` at ~5.5 s under the
   population sweep's `ulimit -v 8 GiB` in **both** arms. That is a real memory
   defect, and it is *not* an LRA-construction one either.

### Why `BYTES_PER_LRA_COEFFICIENT` is not calibrated from these numbers

The obvious calibration — peak RSS divided by the coefficient count the builder
charged itself for — is unavailable, and reading (2) above is why: the peak is
dominated by allocations that are not coefficients, so the quotient would be a
confident number about the wrong thing. The constant is therefore a **structural
accounting** of the four places one semantic coefficient is stored (the
`BTreeMap` entry, the `assign_forms` key, that key again inside the form map, and
the sparse tableau row), summed at ~195 bytes and rounded up to 224. The rounding
direction is chosen deliberately: over-estimating refuses a query that would have
fitted (one lost decide), under-estimating admits one that will not (an abort).

### For a sibling division

The transferable form of this result, since `MAX_ONLINE_LRA_ATOMS` is also the
gate behind 62 QF_NRA losses:

- The shipping budget is **640 MiB** per online-LRA construction — 128 MiB of it
  the dense tableau's own ceiling, 512 MiB of coefficients, i.e. **2 396 745
  coefficients** at 224 bytes each. `SolverConfig::memory_limit_mb` overrides it,
  and `smtcomp_cli --memory-limit-mb N` exposes that.
- At the atom counts this class carries (>1 024, up to ~1 500), the budget
  refused **0 of 22** files. Admission is not what is losing them.
- The risk that remains is the **process** peak, not the construction: 201 MiB to
  8.7 GiB, median 759 MiB, one file over 8 GiB. A QF_NRA query reaching this
  route with 23 385 atoms should be expected to be admitted; what it should be
  watched for is process RSS, and the number to watch it against is the one above.


## 5. The shipped result

Arm **base** = `75286df9` (counters only, no behaviour change).
Arm **final** = `c7b1fa67` (the whole lane).
Binaries confirmed different by `sha256sum`; both arms 24 s / 8 GiB per file,
one file at a time, pinned to one core half of an otherwise idle s7.

| population | decided base | decided after | gains | losses | sat/unsat flips | wall on commonly-decided |
|---|---:|---:|---:|---:|---:|---:|
| committed 200-file parity list | 97 | **98** | 1 | **0** | **0** | 57 840 → 50 890 ms (**0.880x**) |
| 33-file scoring population | 7 | **8** | 1 | **0** | **0** | 31 765 → 28 363 ms (**0.893x**) |

The single gain is `spider_benchmarks/no_op_accs.base.smt2`, unknown → **unsat**.

### The six files that defined the cap work

Each of these decided the design of one guard, and three of them refuted one.
Measured on the shipped binary, 8 GiB `ulimit -v`, same host:

| file | base | shipped |
|---|---|---|
| `miplib/danoint-266` | unknown 0.04 s, 15 MB | unknown 0.04 s, 18 MB |
| `miplib/fixnet-5000` | unknown, small | unknown 0.04 s, 19 MB |
| `miplib/vpm2-5` | unknown, small | unknown 0.03 s, 16 MB |
| `TM/p5-driverlogNumeric_s9` | **unsat** 0.27 s, 40 MB | **unsat** 0.18 s, 42 MB |
| `Heizmann/_sanfoundry_10_ground…bpl_13` | unknown 0.82 s, 121 MB | unknown 0.61 s, 123 MB |
| `spider_benchmarks/no_op_accs` | unknown 24.1 s | **unsat** 19.2 s |

Between base and shipped, three intermediate builds each took one of the first
five files to a **7.8 GB abort** or to a lost `unsat`. None of those was visible
to review; each was found by the 200-file sweep. The three refuted cost models
are tabulated in
[the diary](lra-theory-side-2026-09-07.md#3-the-atom-cap-three-cost-models-three-refutations-adr-1752)
and in ADR-1752.

### A protocol note on the timing numbers

Two of the arms above were run on opposite core halves of the same host at the
same time, which is a deliberate departure from the one-arm-at-a-time protocol:
it halves the wall clock of a **verdict** comparison, which is what the
no-regression check is, and verdicts near the 24 s boundary were re-checked
individually. It is *not* how the ratios were taken — those come from arms run
alone, and the same file measured under contention read 0.99x where the idle run
read 0.86x. Quote the shape, not the third digit.
