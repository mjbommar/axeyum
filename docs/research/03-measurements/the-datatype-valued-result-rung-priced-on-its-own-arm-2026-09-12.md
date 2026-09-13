# The datatype-VALUED result rung, priced on the arm it will actually ship against — and the "57" it inherited is not that number

**Measured 2026-09-12, lane `dt-valued-result`, at `183758366`** (`main`'s tip,
which carries ADR-1942 as `295781893` and its pre-push gate as `183758366`).
The sizing pass for ADR-1946, done before a line of the implementation was
committed, on the same three pinned 200-file lists the boards, the census,
ADR-1935 and ADR-1942 all used.

**In one line: ADR-1942 handed this rung the figure "57 of the 173", and that
figure is right about its own arm and wrong about mine. It was the
EVERY-route-entry predicate taken over the 173 files whose first refusal was the
shape check *before ADR-1942 shipped*; on the arm that now exists that population
no longer has 173 members, and the predicate itself is the one ADR-1942's own §7
retracted as a bound. Re-measured on the ADR-1942 arm, the bracket is [0, 52]
newly-eligible undecided files with an ANY-entry point estimate in the low teens
— and the largest single population the change plausibly moves is one the
eligibility predicate does not see at all: the 48 files whose first refusal is
`is`/`select` over a NON-VARIABLE datatype term, because the witness this rung
introduces turns exactly that operand into a variable.**

## 1. Why the inherited number could not be reused

[ADR-1942's sizing note](the-constructor-arg-slice-is-10-of-173-files-2026-09-12.md)
§4 priced "slice B" — Ackermannising a datatype-VALUED result — at **57 of the
173**, with 52 of those also carrying a constructor argument. That is what made
the build order right, and it is not in dispute. But three things changed
between that measurement and this one, and each moves the number:

1. **The base arm is different.** ADR-1942 shipped. The 173-file population it
   measured over ("first refusal is the non-variable datatype argument") is now
   **72**, and 98 files that used to stop there now stop at the exactness arm
   instead. A figure quoted as a fraction of a population that no longer exists
   is not a sizing.
2. **The predicate was retracted as a bound.** ADR-1942's §7 correction: the
   datatype route is entered once per instantiation round, the file decides when
   ONE entry is handled, and so `all(entries eligible)` is neither an upper nor
   a lower bound on a quantified division. The 57 is an `all()` figure.
3. **This rung's change is wider than "admit a datatype-valued result".** To
   make that result usable it must also admit an `Op::Apply` term as a datatype
   ARGUMENT, and admitting it has a consequence downstream that the pre-pass
   predicate cannot express — §4 below.

So the rung was re-measured from scratch, on its own arm, with the bracket
printed rather than a single number.

## 2. Method

A RUNTIME census, not a static scan of the `.smt2` text — the same method as
ADR-1942's and for the same reason: `collect_ackermann_groups` returns at the
FIRST argument it cannot handle, so the refusal string a blocker census reads
cannot say how many files a fix would reach.

`census-instrumentation.py` (a measurement patch applied to
`crates/axeyum-solver/src/datatype_native.rs`, deliberately not committed to it)
recollects the applications under the **WIDENED** rule this lane proposes — an
application is a site when it has a datatype-sorted ARGUMENT *or* a
datatype-sorted RESULT — and then classifies, per entry into the datatype route:

* every datatype-sorted argument of every widened site: free **variable**,
  **constructor** application, another **`Op::Apply`**, or another shape by name,
  each split by whether its datatype's expansion is exact;
* every widened function's RESULT sort: a datatype whose expansion is exact, a
  datatype whose expansion is not, or a sort that merely MENTIONS one (an array
  over a datatype);
* the congruence pair count under BOTH the narrow and the widened site sets.

That last one is the term the ADR-1942 rows structurally could not supply: those
applications were never collected on the old rule, so their pairs were never
counted, and the widening's cost could not be read off them at all.

Every file of the three lists, 10 s wall / 8 GiB, a 16 s wrapper headroom,
twelve modulo-interleaved shards over `s5`/`s6`/`s7` (idle at launch), two pinned
cores each, each run recording its own outcome. Rows, scripts and the
instrumentation patch:
[`bench-results/dt-valued-result-20260912/`](../../../bench-results/dt-valued-result-20260912/README.md).
`analyze-census.py` reproduces every number below from the committed rows and
asserts it read 600 of them.

**The check that this census measures the same thing the A/B will.** Its base
verdicts are **71 / 88 / 29 = 188 decided**, which reproduces ADR-1942's A/B
new-arm rows exactly (71 / 88 / 29). A sizing whose base arm did not reproduce
the previous measurement's result arm would be measuring a different tree.

## 3. Where the 600 stand on the arm this lane starts from

| bucket (first refusal) | AUFDTLIRA | UFDTLIRA | UFDT | of 600 |
|---|---:|---:|---:|---:|
| **decided** | 71 | 88 | 29 | **188** |
| congruence over an argument whose expansion is not exact | 22 | 33 | 43 | **98** |
| UF applied to a datatype term that is neither variable nor constructor | 12 | 17 | 43 | **72** |
| a UF whose RESULT sort mentions a datatype | 21 | 3 | 27 | **51** |
| `is`/`select` over a non-variable datatype term | 25 | 16 | 7 | **48** |
| e-matching did not refute within the round budget | 4 | 7 | 29 | 40 |
| quantified solve budget exhausted after e-matching | 12 | 0 | 6 | 18 |
| e-matching instantiation budget exhausted | 8 | 1 | 7 | 16 |
| instantiation satisfiable; the universal may still hold | 0 | 15 | 0 | 15 |

**51** is this rung's blocker count — the files that stop on the result-sort
refusal FIRST. It is not a fix count, for the reason this project has now
measured three times.

## 4. The bracket

Over the **412 undecided** files, which is the only population a gain can come
from:

| | AUFDTLIRA | UFDTLIRA | UFDT | total |
|---|---:|---:|---:|---:|
| **ADR-1946 eligible, EVERY route entry** | 67 | 28 | 22 | **117** |
| **ADR-1946 eligible, ANY route entry** | 85 | 46 | 89 | **220** |
| the arm as it stands, EVERY route entry | 25 | 12 | 0 | 37 |
| the arm as it stands, ANY route entry | 57 | 30 | 81 | 168 |
| **newly eligible under the ANY predicate** | 28 | 16 | 8 | **52** |
| newly eligible under the EVERY predicate | 42 | 16 | 22 | 80 |

The two "newly" rows are different populations, not nested: a file can be
ANY-eligible on both arms — it clears the pre-pass on some round today and still
declines at a later rung — while only the new arm makes EVERY entry eligible.

Over all 600, for comparison with ADR-1942 §7's slice-B figures of 176 (EVERY)
and 285 (ANY), which were taken on the PREVIOUS arm: **169 (EVERY), 275 (ANY)**.
They are close, which is the second sign the two censuses are measuring the same
shapes; the difference is the 10 files ADR-1942 moved into `decided` plus the
pair-count term this census adds.

**The sizing this lane commits: a bracket of [0, 52] on the eligibility axis,
with a point estimate in the low teens, and one unquantified addition.**
The point estimate is calibrated on the only completed instance of this
measurement: ADR-1942 converted 10 of its 65 ANY-eligible files into gains, a
15 % yield, and 15 % of 52 is 8. It is stated as "low teens" rather than "8"
because of the mechanism in the next paragraph, which pushes the other way and
which the predicate cannot price.

**The unquantified addition, and it may be the larger half.** 26 of the 52
newly-eligible files — and 48 files in total — have `is`/`select` over a
NON-VARIABLE datatype term as their FIRST refusal. That refusal fires in
`scan_fragment`, downstream of the pre-pass, so no pre-pass eligibility predicate
can see it. But the operand it refuses is in many cases exactly a UF result:
`is_c(g(a))` with `g : Int -> D` is not collected under the narrow rule, so no
Ackermann refusal fires at all and the scan is the first thing to object. Under
the widened rule `g(a)` IS collected, is replaced by its witness VARIABLE before
the scan runs, and `is_c(w_g)` is a shape the scan already handles. How many of
the 48 are that shape rather than a `select` over a `select` is NOT measured
here — the census records argument and result shapes, not `is`/`select` operand
shapes — and it is recorded as an open term rather than folded into the estimate.

## 5. The cost, which is the term the previous rows could not carry

Widening the collection adds sites, and Ackermann is quadratic in the sites of
one function, so the risk is a file whose pair count crosses `MAX_ACK_PAIRS`
(20,000) and loses the WHOLE pre-pass — turning a decided file into a decline.
Measured:

| | count |
|---|---:|
| DECIDED files pushed over the pair bound by the widening | **0** |
| any file pushed over the pair bound by the widening | **0** |
| files whose wide pair count is over the bound at all | 5 |
| DECIDED files that collect a new site under the wide rule | 4 |
| … of those, not eligible at every entry (so the pass will refuse) | 1 |

The five files over the bound are over it on the NARROW rule too — the
Barrett/Reynolds `gram_lang` family, which applies one function to hundreds of
datatype arguments and already refuses at the bound. So on these 600 the
widening costs nothing at the bound. The one decided file that gains a site and
is not eligible at every entry is the concrete regression candidate, and the A/B
is what decides whether it is a loss; it is named in the rows.

## 6. What is still refused afterwards

Among the undecided files, counting each blocker wherever it appears rather than
only where it fires first:

| | AUFDTLIRA | UFDTLIRA | UFDT | total |
|---|---:|---:|---:|---:|
| a VARIABLE argument over an inexact datatype | 16 | 34 | 102 | 152 |
| an INEXACT datatype-valued RESULT | 18 | 26 | 103 | 147 |
| a CONSTRUCTOR argument over an inexact datatype | 21 | 36 | 66 | 123 |
| an `Op::Apply` argument over an INEXACT datatype | 12 | 12 | 47 | 71 |
| some other term shape | 6 | 15 | 13 | 34 |
| an ARRAY-over-datatype RESULT | 0 | 0 | 0 | **0** |

Every large row is the same thing: **a datatype with a datatype-typed field**.
That is ADR-1935's third capability — exact recursive equality, by bounded
unfolding with a depth certificate or a native datatype theory with congruence
and acyclicity — and it is not a slice of this one. It is where the DT
divisions' remaining mass is, and the next lane should size it rather than
inherit a number from here.

The zero row is worth its line: the array-over-datatype result sort, which this
lane refuses by name, does not occur at all in these 600. The guard is written
because the alternative to it is a fall-through, not because it is load-bearing
today, and the ADR says so rather than counting it as coverage.

## 7. Caveats

- Pass-level predicates, not verdicts. §4 says exactly what they are and are not
  bounds on. The A/B in `bench-results/dt-valued-result-20260912/ab/` is the
  number that counts.
- The 600 are three stride-pinned 200-file samples of 23,361 files — the same
  samples the boards, the census, ADR-1935 and ADR-1942 used. They are not a
  census of SMT-LIB, and nothing here is parity.
- `UFDTNIRA` is excluded, as in every previous note in this series: it is more
  than half clock-bound and this capability is not what it is waiting on.
- The instrumentation binary is the same source as the base arm plus the census
  block, and its base verdicts reproduce ADR-1942's result arm (§2), which is the
  check that it is.
- The `is`/`select` mechanism in §4 is an argument, not a measurement. It is
  written down BEFORE the A/B so that the A/B can refute it.
