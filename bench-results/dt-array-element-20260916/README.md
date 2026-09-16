# DT-ARRAY-ELEMENT — sizing first: the `register_datatype` array refusal is
# real, is 100% `(Array Int <datatype>)`, and blocks 2 rows of 800

Lane `dt-array-element`, ADR-2135. This file is the **sizing**, produced
before any code, as exit criterion 1 requires. It answers one question with
denominators: *how many undecided competition rows would an "arrays of
datatypes as opaque elements" lever unblock?*

## Method

Three sources, none re-derived:

1. `bench-results/ledger/t1-AUFDTLIRA-db31113fa.tsv` and
   `t1-UFDTLIRA-db31113fa.tsv` — the shipped `--trace` ledgers, 200 rows
   each, `decline_details` carrying the per-attempt typed give-up sentence.
2. `bench-results/dt-field-expansion-20260916/census/reach-*.tsv` (ADR-2128) —
   per-file, per-datatype reach rows carrying `today_w1` (did
   `register_datatype` refuse this datatype today?) and `w1_sort` (**which
   sort it refused**).
3. `bench-results/dt-ground-probe-20260916/census/terminal-reasons.tsv` — the
   ground probe's 83-file population.

Buckets are matched on SUBSTRINGS of the raw give-up detail, using ADR-2128's
`blocker-buckets.py` SITES table verbatim so the two censuses are comparable;
an unmatched sentence is reported as `OTHER` with its text, never dropped.
`scripts/sizing.py`, `scripts/w1-files.py`. Terminal reason = the LAST
non-empty `decline_details` entry, i.e. the rung the ladder actually died on.

## 1. Which sort is refused — the split the brief asked for

`w1_sort` over every datatype the reach census marked `today_w1=1`:

| population | W1-refused datatypes | `(Array Int <datatype>)` | array w/ uninterpreted domain-or-range | anything else |
|---|---:|---:|---:|---:|
| ADR-2128 probe-stripped-83 | 142 | **142 (100%)** | 0 | 0 |
| AUFDTLIRA undecided (82 files) | 112 | **112 (100%)** | 0 | 0 |
| ADR-2114 cores-55 | 86 | **86 (100%)** | 0 | 0 |
| ADR-2114 originals-79 | 112 | **112 (100%)** | 0 | 0 |
| UFDTLIRA undecided (57 files) | **0** | 0 | 0 | 0 |
| QF_DT undecided (29 files) | **0** | 0 | 0 | 0 |
| UFDT undecided (150 files) | **0** | 0 | 0 | 0 |

Two distinct sorts account for all of it: `('Array', ('Int',), ('D',
'us_rep'))` and `('Array', ('Int',), ('D', 'us_rep1'))` — SPARK's array-of-record
representation. **The brief's premise is confirmed exactly**: the refused sort
is always an array whose ELEMENT is a datatype, never an array whose domain or
range is an uninterpreted sort. The uninterpreted-domain/range case is a
*different site* (`auto.rs`, the lazy Bool/Int array route's admission test)
and is counted separately in §3.

## 2. How many undecided rows this blocks — per division, with denominators

| division | rows | decided | undecided | undecided files declaring ≥1 W1-refused datatype | undecided rows whose **terminal** reason IS the W1 refusal |
|---|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 119 | 81 | **12 / 81** | **2 / 81** |
| UFDTLIRA | 200 | 144 | 56 | **0 / 56** | **0 / 56** |
| QF_DT | 200 | 171 | 29 | **0 / 29** | **0 / 29** |
| QF_ABV (control) | — | — | — | 0 by construction — `QF_ABV` is a datatype-free SMT-LIB logic, so `register_datatype` is never reached | 0 |

The two AUFDTLIRA rows are:

- `S702-024__record_attributes_in_allocators__test_constrained.adb_45_22_assert___00.smt2`
- `P518-021__loop_frame_condition__do_loops.adb_112_22_assert___00.smt2`

The other **10** of the 12 W1-carrying undecided AUFDTLIRA files die somewhere
else entirely — 6 at `quant:ematching`, 4 at the ADR-2103 quant-route ownership
decline. Lifting the array refusal changes their route but does not remove what
actually stops them, so they are an upper bound, not a forecast. A fourth
column that only counted "file declares a W1 datatype" would have reported
**12 / 81** and been six times too optimistic; that is why the terminal column
is the one that sizes the lever.

`W1 refusal appears ANYWHERE in the trail`: 6 / 81 (AUFDTLIRA), 0 / 56
(UFDTLIRA) — smaller than 12 because the datatype rung is not reached at all on
half the W1-carrying files.

## 3. The second bucket — arrays with an uninterpreted domain or range

This is `auto.rs`'s lazy-array admission test, not `register_datatype`:

| division | undecided rows terminating at `array:non-bv` |
|---|---:|
| AUFDTLIRA | **4 / 81** |
| UFDTLIRA | **0 / 56** |

The four files:
`QA23-042__ok_pointers__spark04.adb_22_10_null_pointer_dereference___00.smt2`,
`Q529-038__predicate__bounded_stacks.ads_18_20_integer_stacks.ads_4_1_postcondition___00.smt2`,
`R728-002__aggregates__pragmarc-b_strings.adb_79_22_range_check___00.smt2`,
`tagged_stacks__stacks.adb_17_19_index_check___00.smt2`.

## 4. The ground probe's 83 files, and why they are not a division

`bench-results/dt-ground-probe-20260916` reports the W1 refusal as its largest
bucket: **8 of 14** undecided files terminate at `datatype_native.rs:1511`
(recount from `census/terminal-reasons.tsv`, `arm=default`: 8 `datatype_native.rs:1511`,
5 `auto.rs:8527`, 1 `sat_bv_backend.rs:122`). That is the strongest signal for
this lever anywhere in the repository — but the probe's own README states the
population is quantifier-STRIPPED files whose reference verdict is `sat` on
**83 of 83**, deliberately constructed and not a competition division. A gain
there is `unknown → sat` on a synthetic file. It is corroboration that the site
is live; it is not sizing.

## 5. What this sizes the lever at

Across the four A/B divisions the brief names (800 rows):

- **2 rows** where the `register_datatype` array refusal is the last thing standing.
- **4 rows** in the separate `auto.rs` uninterpreted-component bucket.
- **0 rows** in UFDTLIRA, QF_DT and QF_ABV, at either site.

Ceiling **6 of 800 (0.75%)**, and that ceiling assumes every one of the six then
*decides* — which is not given, because all six still carry quantifiers after
the array is admitted. For comparison, ADR-2128's nested-field expansion —
built against a reach census showing `LEVER CONVERTS=410` datatypes on the same
AUFDTLIRA population — measured **+3 / −0** on AUFDTLIRA, **+1 / −0** on
UFDTLIRA, **0 / 0** on QF_DT, and shipped OFF. The reach-vs-terminal gap that
produced that outcome is the same gap this table shows as 12-vs-2.

---

## 6. The A/B — 800 rows, 0 gains, 0 stable losses, 0 flips

One binary (`smtcomp_cli-2135`, sha256 `66604134b6ec…`, built from `9fab977cc`,
licensed by a `find -newer` check over `crates/**/*.rs`), two env values, arms
back to back per file on one pinned s7 core, order alternated, 24 s / 8 GiB,
divisions SERIAL across cores 1/3/5/6 (one thread of each physical pair).

| division | base | arm | gains | losses | flips |
|---|---|---|---:|---:|---:|
| `AUFDTLIRA` | unsat 119, unk 81 | unsat 119, unk 81 | 0 | 0 | 0 |
| `UFDTLIRA` | unsat 138, sat 6, unk 56 | unsat 138, sat 6, unk 56 | 0 | 0 | 0 |
| `QF_DT` | unsat 107, sat 64, unk 29 | unsat 106, sat 64, unk 30 | 0 | 1 raw → **0 stable** | 0 |
| `QF_ABV` (control) | sat 132, unsat 55, unk 13 | sat 132, unsat 55, unk 13 | 0 | 0 | 0 |

`census/ab-divisions.txt`, `census/ab-*.shard*.tsv`.

**The all-agreeing rows are a genuine null, not an unarmed run**
(`scripts/arm-liveness.sh`, `census/arm-liveness.txt`): on both of the two rows
whose terminal reason is the refusal, the ON arm emits **0** of the W1 refusals
the OFF arm emits, changes the route, and still does not decide — at 117x and 5x
the solver's own `--trace` wall time and 14x the attempts.

**The one raw mover is not this lever** (`census/movers-recheck-QF_DT.tsv`,
`census/vlsat3-b84-shape.txt`): `vlsat3_b84.smt2` rechecks NEITHER-DECIDES 3 of
3 per arm, and contains **0 occurrences of `Array`** plus one field-free nullary
enum, so `field_is_opaque` is never reached and both arms run identical code.

**The held-out draw was NOT RUN.** No division moved, so there is nothing for it
to confirm, and it cannot turn 0 gains into a reason to ship.

## 7. A tool that lied: `date +%s%3N` on s7

The `base_ms`/`arm_ms` columns of these shard TSVs — and of
`bench-results/dt-field-expansion-20260916`'s, same script, same host — are
**nanoseconds under a millisecond header**. s7 runs uutils coreutils 0.8.0,
whose `date` ignores the width modifier in `%3N` and prints nine nanosecond
digits (30 of 30 samples 19 chars; GNU gives 13). Found because this lane's cost
pass reported a total of **−20,454,778,950,164,076,537 ms**
(`census/ab-cost.txt`, kept and labelled as refuted).

Fixed here: `scripts/ab-run.sh` times from the `EPOCHREALTIME` bash builtin and
**aborts before any solve** if a 200 ms sleep does not read as 150–400 ms;
`scripts/ab-cost.py` refuses a file whose elapsed values are outside
`[0, 10 × budget]` with exit 3 rather than reporting from it. Verified on s7
end to end: `v1l30030.cvc.smt2  unsat  114  unsat  113`. Verdict columns are
unaffected — `ab-summarize.py` reads only verdicts.
