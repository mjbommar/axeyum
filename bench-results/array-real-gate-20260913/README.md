# The `!features.has_real` array gate: sizing before building (2026-09-13)

Lane `ARRAY-REAL-GATE`. The question comes straight out of
[ADR-1955](../../docs/research/09-decisions/adr-1955-the-nested-array-sort-is-the-first-of-three-gates-and-the-only-one-the-ir-owns.md)'s
Decision section:

```
parse refusal            27,150 files    IR   — that ADR's design
  +  nested select base   7,530 files    solver — abv.rs:2735, incremental.rs:6014
  +  Real-element arrays 19,620 files    solver — auto.rs:6098
```

> and the third line is the one worth noticing: **it is the larger prize, it is
> not blocked by the IR at all, and a flat array demonstrates it in one query.**

This directory is the measurement taken **before** the guard was touched, and
it says the third line is not a prize at all. The decision is
[ADR-1960](../../docs/research/09-decisions/adr-1960-the-real-element-array-gate-was-three-gates-and-none-of-the-19620-were-behind-it.md).

## The bracket, published before the code

**Lower bound — files this change decides that we did not decide before: 0.**
**Upper bound — files it could ever decide once the IR change lands: 0 from
AUFLIRA/AUFNIRA, because those files' element sort is not the only thing in
their way.** The reachable population today is the probe set: four queries
move from `unknown` to a verdict, and z3 and cvc5 agree with every one of them.

The derivation is one census over whole divisions, `census.sh`, which classifies
every file by what the **dispatcher's own predicate** would do with it:

| division | files | parse_err | no_array | pass_today | blocked (other) | **real_gate_only** |
|---|---:|---:|---:|---:|---:|---:|
| AUFLIRA | 20,011 | 18,644 | 1,367 (q) | 0 | 0 | **0** |
| AUFNIRA | 1,480 | 976 | 504 (q) | 0 | 0 | **0** |
| AUFDTLIRA | 11,043 | 488 | 0 | 33 (q) | 10,522 uninterp | **0** |
| AUFDTNIRA | 1,567 | 83 | 0 | 0 | 1,484 uninterp | **0** |
| AUFFPDTNIRA | 166 | 16 | 0 | 0 | 150 uninterp | **0** |
| ABVFPLRA | 77 | 77 | 0 | 0 | 0 | **0** |
| QF_ABVFPLRA | 74 | 40 | 0 | 0 | 34 bv/float | **0** |
| ALIA (control) | 3,098 | 3,028 | 0 | 70 (q) | 0 | **0** |
| QF_ALIA (control) | 176 | 50 | 0 | 126 | 0 | **0** |

`real_gate_only` is the file's own definition of the prize: a **non-bit-vector
array** query that `scalar_alia_auflia_arrays_supported` refuses **on the
`has_real` clause and nothing else**. There are none, anywhere in the divisions
that can hold one.

Two things ADR-1955 did not separate produce that zero:

1. **AUFLIRA's and AUFNIRA's 19,620 are the SAME files as the 27,150.** They are
   behind the parse refusal *and* would be behind the Real gate. ADR-1945's own
   rule applies to its successor: a count attributed to a blocker is an upper
   bound, and **two sequential caps are not two caps**. Removing the second one
   while the first stands decides zero files, which is exactly what ADR-1955
   said about the IR change and did not say about this one.
2. **The files of those divisions that DO parse contain no array at all.** All
   1,367 AUFLIRA and 504 AUFNIRA parse-ok files are the `why`/`FFT`/`aviation`
   families, and `grep -c Array` over them is 0. There was never a control
   population for the Real array gate; there was no population.

The negative controls are in the table on purpose: ALIA and QF_ALIA are array
divisions with **no** Real, and their `real_gate_only` is 0 for a different
reason (`pass_today` instead). A classifier that returned 0 everywhere would
look identical, which is why `census.sh` is also run on the probe set, where it
must and does return a **nonzero** `real_gate_only` for `p5`/`r1` and
`pass_today` for their Int twins.

`census-all-array.sh` repeats the sweep over **every** array-carrying division
(28 of them), because "we looked where we expected a hit and found none" is not
a denominator.

## What the change is worth anyway

The gate was real, it was stale, and it was three gates rather than one — two
of which are lifted here and the third documented in place, see ADR-1960. The capability is demonstrated by the probe pairs below and by
`crates/axeyum-solver/tests/real_element_array_row.rs`; the corpus value today
is zero, and saying so is the point of measuring first.

## Files

| file | what it is |
|---|---|
| `crates/axeyum-smtlib/examples/array_real_gate_census.rs` | the census instrument. Mirrors `Features::scan_within`/`note_sort`, which are private to the solver crate, over the same public IR surface. A mirror can drift, so its output is a denominator confirmed by the A/B, never the finding. |
| `census.sh` | whole-division census over the Real-capable array divisions plus the two no-Real controls. |
| `census-all-array.sh` | the same over all 28 array-carrying divisions, behind a deliberately over-inclusive textual prefilter (`real`/decimal literal) — parsing every file was measured at ~20 hours for AUFBV alone. |
| `census/` | the committed per-division summaries. |
| `probes/` | this lane's gate-isolation probes, `r1`–`r7`. Each is a pair with an ADR-1955 probe or with its own Int twin, differing in one token. |
| `run-probes.sh` | every probe through ONE binary in one invocation — a pair read from two builds is not a pair. |
| `ref-probes.sh` | the same probes through z3 and cvc5. Prints the reference verdict verbatim: an `unknown` from a reference is an opportunity the check never had, not a pass. |
| `ab.sh` | the interleaved per-file A/B, one shard per division on its own core, both binaries back to back on one file. |
| `ab-summarize.py` | the A/B table **and** the wrong-verdict check. Exit 3 on a verdict contradicting a declared `:status`, 4 on the two arms deciding oppositely, 2 on an empty run. |
| `ab-summarize-controls.sh` | all five of those exit statuses, fired. |

## The probe table

Measured through `smtcomp_cli --timeout-ms 24000`, both arms in one
`run-probes.sh` invocation, at the SHAs recorded in this lane's status file.
References re-run at the same budget (`z3 -T:24`, `cvc5 --tlimit 24000` — the
units differ and mixing them corrupts a board).

| probe | shape | before | after | z3 | cvc5 |
|---|---|---|---|---|---|
| `p5-row-real` | `(Array Int Real)` ROW, distinct symbolic indices | `unknown` | **`unsat`** | `unsat` | `unsat` |
| `p6-row-int` | the same with `Int` (the pair) | `unsat` | `unsat` | `unsat` | `unsat` |
| `r1-row-real-uf` | `p5` plus one UF application, so `has_function` is set | `unknown` | **`unsat`** | `unsat` | `unsat` |
| `r2-fractional-read-real` | `0 < m[i] < 1` over `(Array Int Real)` | `unknown` | **`sat`** | `sat` | `sat` |
| `r3-fractional-read-int` | the same over `(Array Int Int)` (the pair) | `unsat` | `unsat` | `unsat` | `unsat` |
| `r4-unconstrained-index-pair` | store at `i`, read at `j`, nothing asserted about `i`,`j` | `unknown` | **`sat`** | `sat` | `sat` |
| `r5-rational-store-readback` | store-then-read at the same index, value `1/3` | `unsat` | `unsat` | `unsat` | `unsat` |
| `r6-ext-real-uf` | array extensionality, Real element, UF present | `unsat` | `unsat` | `unsat` | `unsat` |
| `r7-row-real-uf-distinct` | ROW with the UF applied to the array's index | `unknown` | **`unsat`** | `unsat` | `unsat` |

`r1`, `r6` and `r7` are also the three probes aimed at the gate that was
**identified and not changed** — `uf-arithmetic`'s `Unknown` early return for
`has_real`, gate 2 of ADR-1960's three. Another route decides all three before
that rung, and the corresponding mutation SURVIVED (nine tests, none depend on
it), so the gate is documented in place rather than relaxed on speculation.
Their value here is as negative evidence: they are what "we could not reach it"
means.

`r2`/`r3` is the pair that carries the soundness claim rather than the
capability claim: `0 < m[i] < 1` is satisfiable over `Real` and unsatisfiable
over `Int`, so an `unsat` on `r2` would mean the element sort had been
integralized somewhere on the newly reachable route. Every other probe in
`nested-array-ir-20260913/probes/` is byte-identical between the two arms.

## The A/B: 1,200 files, not one row moved

Interleaved per-file, both binaries back to back on one file on one pinned core,
24 s wall / 8 GiB, arms rotated per file (`ab.sh`). Arm A is `57bd22d37`
(baseline), arm B is this lane's `4ef107d35`. Rows in `ab/`, summary in
`ab/SUMMARY.txt`.

    division        n  A dec  B dec  delta  B-only  A-only
    AUFLIRA       200      9      9     +0       0       0
    AUFNIRA       200      3      3     +0       0       0
    ALIA          200      0      0     +0       0       0
    ABV           200      4      4     +0       0       0
    QF_ABV        200    187    187     +0       0       0
    QF_BV         200    186    186     +0       0       0
    rows: 1200

**Zero rows differ between the arms at all** — not merely equal decide counts:
a per-row comparison of the verdict strings finds 0 of 1,200 files where
`axeyum` and `axeyumb` disagree, so there is no single-pairing surprise to
re-run. No verdict in either arm contradicts a declared `:status`, and there is
no file where the two arms decide in opposite directions (`ab-summarize.py`
exit 0; its five failing exit statuses are demonstrated firing by
`ab-summarize-controls.sh`).

The last two rows are the live controls: QF_ABV at 187/200 (93.5%) and QF_BV at
186/200 (93.0%) are divisions we already decide well, so a regression would be
visible against a high floor rather than lost in noise. `rc134` (the protocol's
8 GiB address-space cap) appears on exactly one file, **in both arms**, and no
row on any solver was wrapper-killed.

The +0 is the predicted result, not a disappointment: the census said the
reachable population was zero before the code was written, and the A/B is what
turns that prediction into a measurement. What it additionally rules out is the
other half — that lifting two early returns would cost decisions elsewhere.

## Every array-carrying division

`census-all/all-array-divisions.txt` — all 28 divisions whose logic can hold an
array, `real_gate_only = 0` in every one. The `filtered out textually` column is
the two-stage prefilter and it is worth reading rather than skipping: the FIRST
version of that pattern matched 4,975 of ABV's 4,975 files (it accepted any
decimal literal, and every SMT-LIB file opens `(set-info :smt-lib-version 2.6)`),
which would have been reported as a sweep. A prefilter that matches everything is
not a prefilter, and the column is what made it visible.
