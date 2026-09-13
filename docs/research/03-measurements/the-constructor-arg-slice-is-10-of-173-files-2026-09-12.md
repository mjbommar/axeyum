# The constructor-argument slice is 10 of 173 files; the datatype-VALUED result is the rung that is worth 57 — and it needs this one first

**Measured 2026-09-12, lane `dt-constructor-arg`, at `a25e98639`.** The sizing
pass for ADR-1942, done before a line of code, on the same three pinned 200-file
lists the boards, the census and ADR-1935 all used.

**In one line: ADR-1935's residual census put "UF applied to a datatype term
that is not a free variable" at 173 of 600 and named the constructor-term case
as the next slice; that slice reaches *10* of those 173, because in 87 of them
the offending argument is another function's RESULT, in 75 the constructor is
over a datatype whose expansion is not exact, and in 67 a plain variable
argument is inexact too. The rung that is worth 57 of the 173 is the one
ADR-1935 explicitly refused — Ackermannising a datatype-VALUED result — and 52
of those 57 also carry a constructor argument, so this slice is its
prerequisite, not its complement.**

That sentence is ADR-1935's own headline one rung out, and it is the second time
in one day the same arithmetic has caught a stated "BUILD NEXT". The general
rule is now measured twice and should be assumed rather than rediscovered: **a
blocker census names which refusal fires FIRST, and the population a fix reaches
is strictly smaller — usually by a lot — because the file must clear every OTHER
precondition of the same pass.**

## 1. The question

[ADR-1935](../09-decisions/adr-1935-the-congruence-precondition-is-exactness-not-scalarity.md)
closed with a residual census taken on its own new arm:

| refusal | files |
|---|---:|
| UF applied to a datatype term that is **not a free variable** | **173** |
| congruence over a datatype argument whose expansion is not exact | 50 |
| a UF whose RESULT sort mentions a datatype | 47 |
| e-matching instantiation did not refute within the round budget | 39 |
| `is`/`select` over a non-variable datatype term | 22 |

and said of the top row:

> it is a **constructor term as a UF argument** (`p(mk(a,b))`), whose argument
> equality is structurally exact and cheap. That is the next slice, and it is
> larger than either half of this one.

The equality claim is correct and this note does not dispute it — the
decomposition ADR-1942 ships is three lines of datatype axiom. The question is
the arithmetic one: **how many of the 173 does a fix to that refusal actually
reach?**

## 2. Method

A RUNTIME census, not a static scan of the `.smt2` text. The refusal fires
inside `collect_ackermann_groups`, which returns at the FIRST offending
argument; the instrumentation (`census-instrumentation.py`, a patch applied to
`crates/axeyum-solver/src/datatype_native.rs` for the measurement and not
committed to it) instead walks **every** datatype-sorted argument of **every**
collected application and classifies each one:

* a free **variable**, over a datatype whose expansion is exact or not;
* a **constructor** application, over a datatype whose expansion is exact or not;
* an **`Op::Apply`** — another uninterpreted function's result;
* anything else, recorded by its operator's name.

It also records, per function, whether the RESULT sort mentions a datatype, and
the congruence pair count against `MAX_ACK_PAIRS`.

From those it computes two per-file predicates, which are the pass-level
preconditions each candidate slice would have to satisfy for the Ackermann
pre-pass to stop refusing — all of them, because one refused application refuses
the file:

* **slice A** (ADR-1942, this lane) — every datatype argument is a variable or a
  constructor, every one over an exact datatype, no function has a
  datatype-mentioning result sort, the pair count is within bound, and at least
  one argument is a constructor.
* **slice B** (slice A, plus Ackermannising a datatype-VALUED result into a
  fresh datatype VARIABLE) — the same, with `Op::Apply` arguments and
  datatype-valued results admitted when their datatype's expansion is exact.

Every file of the three lists, 10 s wall / 8 GiB, twelve modulo-interleaved
shards over `s5`/`s6`/`s7`, two pinned cores each. Rows, scripts and the
instrumentation patch:
[`bench-results/dt-constructor-arg-20260912/`](../../../bench-results/dt-constructor-arg-20260912/README.md).
`analyze-census.py` reproduces every number below from the committed rows.

**What this over-counts, stated up front.** Both predicates are about the
Ackermann PRE-PASS only. A file that clears it still has to get through
`scan_fragment`, the tag/field expansion, the residual dispatch and — on `sat` —
the replay. So these are upper bounds on what the corresponding change can
decide, and the A/B is what turns an upper bound into a number. They are not
upper bounds in the other direction: a file is scored by the WORST argument it
has, which is the same file-level convention
[the ADR-1920 sizing note](the-adr-1920-slice-is-6-of-600-files-2026-09-12.md)
used.

> **The paragraph above is WRONG and §7 corrects it. Read §7 before quoting any
> number from §3 or §4 as a bound.** These predicates require EVERY entry into
> the datatype route to be eligible, and on a quantified division the route is
> entered once per instantiation round while the file needs only ONE of those
> entries to succeed — so the figure is neither an upper nor a lower bound. The
> A/B measured +10 against a strict prediction of 11 of which only 3 gained, and
> all ten gains lie inside the loose (`any`) predicate's 65. The relative finding
> the build order turned on — that slice A is slice B's prerequisite — holds
> under either predicate.

## 3. The result

The base arm reproduces ADR-1935's residual census exactly — 173 / 50 / 47 / 22,
and 69 / 82 / 27 decided — which is what says the two measurements are of the
same thing:

| | AUFDTLIRA | UFDTLIRA | UFDT | of 600 |
|---|---:|---:|---:|---:|
| decided | 69 | 82 | 27 | 178 |
| **non-variable datatype argument** | 44 | 54 | 75 | **173** |
| inexact expansion | 9 | 18 | 23 | 50 |
| datatype-valued UF result | 19 | 2 | 26 | 47 |
| `is`/`select` over a non-variable term | 15 | 2 | 5 | 22 |

Of those 173, classified by what else blocks them (the rows overlap — a file can
be blocked several ways, and most are):

| | AUFDTLIRA | UFDTLIRA | UFDT | of 173 |
|---|---:|---:|---:|---:|
| **slice A eligible** | **8** | **2** | **0** | **10** |
| blocked by an `Op::Apply` datatype argument | 16 | 22 | 49 | 87 |
| blocked by a constructor over an INEXACT datatype | 17 | 22 | 36 | 75 |
| blocked by a VARIABLE over an inexact datatype | 3 | 15 | 49 | 67 |
| blocked by some other shape (`DtSelect`, array `Select`) | 5 | 13 | 6 | 24 |

**Ten.** Nine of them are one SPARK/Ada family (`R509-011__higher_order_proof`,
five files, plus four others in `20200306-Kanig/spark2014bench`), and `UFDT`
contributes none — its Barrett/Reynolds codatatypes are the class where 49 of
75 have an inexact variable argument before a constructor is even reached.

## 4. The rung that is worth 57, and why this slice comes first

| | AUFDTLIRA | UFDTLIRA | UFDT | of 173 |
|---|---:|---:|---:|---:|
| **slice B eligible** | 21 | 22 | 14 | **57** |
| … and ALSO carries a constructor argument | 19 | 22 | 11 | **52** |
| … and carries none (slice B on its own) | 2 | 0 | 3 | **5** |

Across all 600 files rather than only the 173, slice B's pass-level population
is **176** against slice A's **11**.

So the shape of ADR-1935's finding repeats exactly: **the two are not
complements. 52 of slice B's 57 files also apply a function to a constructor
term, so shipping B without A buys 5 files.** A file decides only if EVERY
application it makes is handled, and these SPARK verification conditions mix
`p(mk(…))` and `p(g(…))` in the same query as a matter of course.

The reverse is also true and is the honest way to quote this slice: A without B
buys 10. The pair is worth 57 of the 173 and neither half is worth much alone.

## 5. What neither reaches

The `Op::Apply` row (87 of 173) is *not* the same population as slice B's
eligibility, because an `Op::Apply` argument only helps if the function's result
datatype is itself exact. Where it is not — the Barrett/Reynolds
codatatypes, and the SPARK records with datatype-typed fields — the argument
needs **exact recursive equality**, which is ADR-1935's third capability
(bounded unfolding with a depth certificate, or a native datatype theory with
congruence and acyclicity). 75 of the 173 have a constructor over such a
datatype and 67 have a variable over one. That is where the DT divisions'
remaining mass is, and it is not a slice of either of these.

## 6. Caveats

- Pass-level predicates, not verdicts. §2 says what they over-count; the A/B in
  `bench-results/dt-constructor-arg-20260912/` is the number that counts.
- The 600 are three stride-pinned 200-file samples of 23,361 files, the same
  samples the boards, the census and ADR-1935 used. They are not a census of
  SMT-LIB.
- `UFDTNIRA` is excluded, as in the census and the ADR-1920 note: it is more
  than half clock-bound and this capability is not what it is waiting on.
- The instrumentation binary is the same source as the base arm plus the census
  block, so the bucket column is directly comparable to ADR-1935's residual
  table — and it reproduces it (§3), which is the check that it is.

## 7. AMENDED after the A/B: the per-file predicate is not an upper bound, and §2 said it was

**Added 2026-09-12 after the ADR-1942 A/B, which measured +10 against this note's
predicted 10 — the same number, on a DIFFERENT set of files.** The headline
arithmetic (§3, §4) stands unchanged and is what redirected the work. One
methodological claim in §2 does not, and it is corrected here rather than
quietly edited, because the corrected version changes how the next lane should
read a table like this one.

§2 said the predicates "are upper bounds on what the corresponding change can
decide". **That is false for a quantified division.** The datatype route is
entered MANY times per file — MBQI and e-matching hand it a fresh residual after
each round of instantiation — and a file decides when ONE of those entries is
handled. This note's predicate requires EVERY entry to be eligible, which is
neither an upper nor a lower bound on the file.

Measured against the A/B's ten gains:

| | AUFDTLIRA | UFDTLIRA | UFDT | total |
|---|---:|---:|---:|---:|
| **slice A, EVERY route entry eligible** (this note's §3) | 9 | 2 | 0 | **11** |
| **slice A, ANY route entry eligible** | 20 | 21 | 24 | **65** |
| actual gains | 2 | 6 | 2 | **10** |
| … inside the EVERY predicate | | | | **3** |
| … inside the ANY predicate | | | | **10** |

So the honest bracket was **[3, 65]** and the answer was **10**. Seven of the
eleven predicted files did not gain (they clear the pre-pass and stop at a later
rung, which §2 did allow for), and seven of the ten that gained were outside the
strict predicate entirely — including both `UFDT` files, a division this note
predicted would gain **none**.

The same correction applies to §4's slice-B numbers, which should be read as the
same kind of bracket:

| | AUFDTLIRA | UFDTLIRA | UFDT | total |
|---|---:|---:|---:|---:|
| slice B, EVERY route entry eligible | 101 | 44 | 31 | **176** |
| slice B, ANY route entry eligible | 118 | 64 | 103 | **285** |

and the 57 / 52 of §4 — both computed with the EVERY predicate over the 173 — are
the conservative end of that bracket. The *relative* finding they were used for
is unaffected and is what the build order turned on: slice A is a prerequisite of
slice B under either predicate, because "also carries a constructor argument" is
a property of the file, not of the predicate.

`analyze-census.py` prints the EVERY figures; the ANY figures come from the same
rows with `all(...)` replaced by `any(...)`.

**The rule to carry forward.** A pass-level sizing over a QUANTIFIED division has
to be quoted as a bracket, because the pass runs once per instantiation round and
the file needs only one of those runs to succeed. Quoting the `all()` figure
alone is the same class of error as quoting a blocker census as a fix count — it
is a real number about the wrong population.
