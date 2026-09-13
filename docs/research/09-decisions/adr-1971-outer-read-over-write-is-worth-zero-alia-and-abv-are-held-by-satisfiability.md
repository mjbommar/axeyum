# ADR-1971: outer read-over-write is worth zero — ALIA and ABV are held by satisfiability, not by the array theory

Status: accepted
Index-summary: [ADR-1965](adr-1965-the-nested-array-prize-was-never-the-array-theory-it-was-congruence.md) named **outer read-over-write on a nested array** as the gate holding ALIA's 511 files and ABV's 423, and said re-sizing it needed a different instrument. That instrument is built (`bench-results/nested-array-outer-row-20260913/`, committed at `675282be2` before any solver change) and it is the **mirror** of ADR-1965's: it CURRIES the outer level and performs outer read-over-write syntactically, keeping the inner array theory and the quantified inner-array variables the SV-COMP memory model actually uses. **The gate is worth 0.** Two independent reasons, the first of which settles it before reach is measured: **39 of the 53 winnable ALIA+ABV files are SATISFIABLE**, and outer read-over-write is a refutation mechanism — so the gate's ceiling is 220 files, not 934. And of the refutable remainder it reaches none: handed outer read-over-write for free, axeyum answers `unknown` on **18 of 18** accepted ALIA files and **8 of 9** accepted ABV files; the one ABV refutation is the same file ADR-1965's surrogate already reached and contains **zero outer stores**, so the gate's marginal contribution is **0 on every division**. Sharpest form: **5 ALIA files are refutable AND inside the fragment AND had outer read-over-write performed for them — axeyum decided 0 of 5.** Re-run at a **300 s** budget those five still decline, and they decline in **0.11–0.13 seconds** — it is not a clock but a route: read-over-write is a rule you add to a route, and no route runs. Soundness control z3-original vs z3-surrogate agrees 14/14, **no opinion 13**, CONTRADICTS 0; non-vacuity is carried by two REACH fixtures because AUFLIRA and AUFNIRA refuse 187/187 and 139/139 under this surrogate. **Decision: do not build it.** The refusals name what does hold these divisions, and it is different per family.
Index-status: accepted
Date: 2026-09-13

## Context

[ADR-1965](adr-1965-the-nested-array-prize-was-never-the-array-theory-it-was-congruence.md)
built the interned nested array sort, moved AUFLIRA 10 → 164 and AUFNIRA 3 →
122 (+273 verdicts, all `unsat`), and closed with a named next gate:

> **Next gate: outer read-over-write on a nested array.** ALIA (511 files) and
> ABV (423) sit behind it. It needs a *different* instrument — ADR-1965's
> surrogate refuses exactly those files by construction.

It also recorded why: 33 of 36 ALIA and 12 of 17 ABV winnable files **write the
outer array**, and ADR-1965's surrogate turns the outer array into an
uninterpreted sort, which deletes outer read-over-write. Its 86.5% reach figure
is trustworthy precisely because it refused to speak about those files.

So the question was open, and the instrument to answer it had to keep outer
read-over-write rather than delete it.

## 1. The instrument

`scripts/nested_array_outer_row_surrogate.py`,
committed at `675282be2` **before any change under `crates/`**, so this ADR's
number can be checked against it rather than fitted to it.

It is the mirror of ADR-1965's surrogate. For each arity-0 declaration
`M : (Array I (Array J E))`:

* `M` becomes an uninterpreted **function** `M_row : I -> (Array J E)`;
* `(select M j)` becomes `(M_row j)`;
* an outer `store` is eliminated **where it is read**, by the read-over-write
  axiom applied syntactically:
  `(select (store A i r) j)` → `(ite (= i j) r (select A j))`.

The inner level is untouched. That is not an incidental choice: these files are
Ultimate Automizer's SV-COMP memory model, `(Array Int (Array Int Int))` with
the outer index a base pointer and the inner an offset, and they quantify over
**inner** arrays (`v_ArrVal_*`) on almost every line. An instrument that
abstracted the inner level would have measured a different population.

An outer-array-valued `let` binding is **inlined** rather than refused — it is
the generator's `.cseN` sharing idiom, and `let` is substitution, so inlining is
exact. Refusing it would have put 9 of ALIA's 36 winnable files outside the
instrument for a reason about the script rather than about the solver. The
duplication it can cause is capped, and `controls/c6` is what makes the inlining
observable rather than trusted.

### Soundness

On the accepted fragment the rewrite is model-preserving in **both** directions:
`M_row(i) := M[i]` one way, `M[i] := M_row(i)` the other, both well-defined
because the fragment forbids every context in which an outer array is anything
but the base of a `select` or of a `store` that is itself read; and the `store`
expansion is the read-over-write axiom itself, an equivalence.

**The number does not rest on that stronger claim.** The reach counts only
`unsat`, the direction that survives even if the equisatisfiability argument has
a hole:

> surrogate `unsat` ⟹ original `unsat`.

A surrogate `sat` is reported in its own column and counted nowhere — 0
everywhere, as it happens. Outer **extensionality** is the one axiom currying
does not have, and it is unreachable on the accepted fragment for the same
reason the fragment is accepted: an extensionality instance needs an equality
between two outer array terms, and every such context is refused.

### Non-vacuity, which this instrument needed more than ADR-1965's did

ADR-1965's surrogate could be read against a population where it demonstrably
reached something. **This one cannot: AUFLIRA and AUFNIRA refuse 187/187 and
139/139 under it**, because their files pass outer arrays to functions — exactly
what ADR-1955 said made currying the wrong recommendation for them. So a reach
of 0 on ALIA would have been indistinguishable from an instrument that cannot
reach anything, which is the vacuous zero
[ADR-1957](adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md)
warns about.

Six fixtures in `controls/` supply the missing opportunity, and each carries a
verdict confirmed on the ORIGINAL by z3 **and** cvc5 so a fixture cannot be
wrong about its own subject:

```
fixture                                kind    ax_surr  z3_surr  z3_orig  cvc5_orig  result
c1-outer-row-refutation                REACH   unsat    unsat    unsat    unsat      PASS
c2-outer-row-disjoint-index            GAP     unknown  unsat    unsat    unsat      PASS
c3-distinct-rows-are-satisfiable       SAT     unknown  sat      sat      sat        PASS
c4-quantified-inner-row-is-satisfiable SAT     unknown  sat      sat      unknown    PASS
c5-outer-equality-is-refused           REFUSE  -        -        unsat    unsat      PASS
c6-shared-outer-store-under-let        REACH   unsat    unsat    unsat    unsat      PASS
```

`c1` and `c6` are the proof the instrument reaches: an outer read-over-write
refutation it returns `unsat` on. `c3` and `c4` are adversarial over
**satisfiable** queries — a rewrite that relaxed the `ite` guard of the
expansion, or that captured a quantified inner row while inlining a `let`, would
flip one of them to `unsat` and the reach would be counting refutations of true
statements. `c5` is the fragment boundary.

## 2. The first reason the gate is worth nothing, and it settles it

Outer read-over-write is a **refutation** mechanism. It cannot produce a `sat`.
So before reach is measured at all, the refutable fraction of the population is
the ceiling — and it is the number nobody had looked at:

| division | winnable | reference `unsat` | reference `sat` | gate ceiling |
|---|---:|---:|---:|---:|
| AUFLIRA | 187 | 186 | 1 | 18,411 |
| AUFNIRA | 139 | 139 | 0 | 955 |
| **ALIA** | 36 | **12** | **24** | **170** |
| **ABV** | 17 | **2** | **15** | **50** |

Read from the board's own pinned TSVs (z3, then cvc5), not re-measured.

**This is the structural finding, and it explains every nested-array result so
far.** AUFLIRA and AUFNIRA are 99%+ refutable, which is why a refutation-only
capability — congruence through the nested read — took 273 of them, 273 of 273
`unsat`. **ALIA is 67% satisfiable and ABV 88%.** A gate that can only produce
`unsat` is aimed at the smaller third of one list and the smaller eighth of the
other. The honest ceiling on the named gate is **220 files, not 934**, and that
is if every refutable file fell to it.

## 3. The second reason: of the refutable remainder it reaches none

| division | winnable | rewritten | refused | ax `unsat` | ax `sat` | reach | ceiling | projected |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFLIRA | 187 | 0 | 187 | 0 | 0 | 0.0% | 18,510 | 0 |
| AUFNIRA | 139 | 0 | 139 | 0 | 0 | 0.0% | 955 | 0 |
| **ALIA** | 36 | 18 | 18 | **0** | 0 | **0.0%** | 511 | **0** |
| **ABV** | 17 | 9 | 8 | **1**† | 0 | 5.9% | 423 | 25† |

† **The 25 is not attributable to this gate.** The single ABV file is
`ABV/20190429-UltimateAutomizerSvcomp2019/dancing_true-unreach-call_false-valid-memtrack.i_0.smt2`,
which **ADR-1965's surrogate already reached**
(`bench-results/nested-array-build-20260913/sweep/ABV.tsv`), and which contains
**zero outer stores** — read-over-write has no instance in it.
**The marginal contribution of outer read-over-write is 0 on every division.**

**What the one ABV file actually represents.** It is reachable by an
outer-level ABSTRACTION — ADR-1965's uninterpreted-sort surrogate and this
lane's currying surrogate both refute it — and the shipped nested-array build
does **not** decide it: ADR-1965's own post-merge A/B records both arms
`unknown` at 0.11 s on it, an immediate decline rather than a timeout. So it is
an unrealized **+1 for the congruence route**, not evidence about
read-over-write, whose axiom it contains no instance of. Counting it toward
this gate would be the error this footnote exists to prevent.


Crossing the reference verdict against acceptance and reach gives the sharpest
form:

| division | reference | surrogate | axeyum | n |
|---|---|---|---|---:|
| ALIA | `sat` | REFUSED | — | 11 |
| ALIA | `sat` | ok | `unknown` | 13 |
| ALIA | `unsat` | REFUSED | — | 7 |
| **ALIA** | **`unsat`** | **ok** | **`unknown`** | **5** |
| ABV | `sat` | REFUSED | — | 7 |
| ABV | `sat` | ok | `unknown` | 8 |
| ABV | `unsat` | REFUSED | — | 1 |
| ABV | `unsat` | ok | `unsat` | 1† |

**Five ALIA files are refutable AND inside the fragment AND had outer
read-over-write performed for them. axeyum decided 0 of 5.** That is the whole
of the gate's opportunity on ALIA.

### The five, re-run at a 300 s budget — it is a ROUTE, not a clock

The five refutable-and-accepted ALIA files were re-run at **300 s**, 12.5x the
board's budget (`sweep-300s/ALIA5.tsv`, file list in
`sweep-300s/refutable-accepted-ALIA.txt`):

| file | axeyum | seconds |
|---|---|---:|
| `dll-token-1.i_25` | `unknown` | 0.13 |
| `dll2c_update_all_reverse.i_120` | `unknown` | 0.12 |
| `dll2c_update_all_reverse.i_4` | `unknown` | 0.11 |
| `sll-token-2.i_0` | `unknown` | 0.11 |
| `sll_to_dll_rev-2.i_102` | `unknown` | 0.11 |

**Every one declines in about a tenth of a second.** The solver is not
searching these and running out of time; it has no route that will take them,
and gives up before the budget is relevant. That is the sharpest reason the
gate is worth zero: **read-over-write is a rule you add to a route, and no
route runs.** z3 refutes two of the five surrogates within the same 300 s and
all five originals except one.

### The soundness control, with its denominator

z3 on the ORIGINAL against z3 on the SURROGATE, per accepted file — an
opportunity on **every** accepted file, not only the refutable ones:

```
z3 agrees 14 / 14, no opinion 13, CONTRADICTS 0
```

The **no opinion 13** is published beside the zero because ADR-1957 requires it,
and here it is load-bearing rather than ceremonial: 13 of the 27 accepted files
are ones z3 does not decide within 24 s on one side or the other, so the control
fired on 14 of 27. That is a small denominator, it is stated rather than hidden,
and the six fixtures are what make up for it.

## 4. What the refusals name, and it differs by family

The refusal reason is the gate *behind* this one, per file:

| refusal | ALIA | ABV | AUFLIRA | AUFNIRA |
|---|---:|---:|---:|---:|
| outer array **equality** (extensionality) | 15 | 8 | 0 | 0 |
| outer array passed to a **function** | 0 | 0 | 185 | 129 |
| no nested array at all | 3 | 0 | 2 | 10 |

ALIA and ABV are held by outer array **equality**; AUFLIRA and AUFNIRA pass
outer arrays to functions. The two families are behind different gates, and a
lane pointed at "the nested array frontier" as one thing will keep finding that
its instrument fits one half and refuses the other.

## 5. One real gap found on the way, and sized at zero

`controls/c2` is the disjoint-index half of read-over-write. Its surrogate is

```smt2
(assert (not (= i j)))
(assert (not (= (select (ite (= i j) r (|M..row| j)) o) (select (|M..row| j) o))))
```

and axeyum answers `unknown`. Writing the same query with `select` pushed
through the array-sorted `ite` by hand gives `unsat`. So the gap is **one
rewrite** — select-over-`ite` on an array-sorted `ite` whose branch is a
UF-returned row — and not the array theory.
`crates/axeyum-rewrite/src/arrays.rs` already has that rewrite; it is
`eliminate_arrays`' own, and these queries do not reach it.

It was sized rather than assumed. The sweep's `--distribute` arm pushes the
`select` through for every file:

| division | plain | `--distribute` | delta |
|---|---|---|---:|
| ALIA | 0 / 18 | 0 / 18 | **+0** |
| ABV | 1 / 9 | 1 / 9 | **+0** |

Worth a control fixture and **zero benchmark files**. It is recorded as
`EXPECT: GAP` in the control script — a fixture that fails loudly in **both**
directions, `sat` as a soundness defect and `unsat` as "the gap closed, this
ADR's number is stale".

## 6. The instrument's guards are mutation-verified

A measurement that concludes **zero** is the one nobody re-checks, so the
surrogate's guards are deleted one at a time and each deletion is required to
kill a test. `scripts/tests/test_outer_row_surrogate.py` (15 tests) is the
subject; `scripts/tests/mutation_controls.py outer-row-surrogate` is the
harness. The instrument lives at `scripts/nested_array_outer_row_surrogate.py`
rather than beside its data because the mutation harness excludes
`bench-results/` from its scratch copy (206 MB), so a guard kept there could not
be mutation-tested at all.

All ten mutations are `killed N`, exit 0:

| guard deleted | killed |
|---|---|
| the read-over-write expansion keeps its index guard | **6** |
| the expansion's else branch reads the curried row | 1 |
| an outer array in a non-read position is refused | 3 |
| an outer array as a function argument is refused | 1 |
| a quantifier binding an outer array is refused | 1 |
| nesting deeper than one level is refused | 1 |
| a file with no outer array is refused | 1 |
| a quantifier binder shadows an inlined `let` alias | 1 |
| the `let`-inlining growth cap fires | 1 |
| `--distribute` is not applied by default | 1 |

The informative row is the first, and it is informative for the same reason
ADR-1965's was: **the index guard is what separates a measurement from a
fabrication.** Replacing `(ite (= i j) r …)` with an unconditional `r` makes
every outer write visible at every outer index, which turns satisfiable files
into surrogate `unsat` — the reach would then be counting refutations of true
statements. Six tests die, including the two that check `--distribute` is a
separate arm, because without the `ite` there is nothing for it to distribute
through and the sweep's two arms would silently become the same measurement.

Eight of the ten kill **exactly one** test, which is what says the guards are
independently observable rather than all rejecting through one shared check.

## Decision

1. **Do not build outer read-over-write on a nested array.** Measured reach 0 on
   ALIA, marginal contribution 0 on ABV, ceiling 220 rather than 934, and the
   ceiling itself is unreachable for 39 of 53 winnable files that are
   satisfiable.
2. **ADR-1965's "ALIA and ABV are the next lane, and the gate is named" is
   superseded.** The gate was named correctly as the thing ADR-1965's instrument
   could not see; it is not the thing holding the population.
3. **The two gate-map tests stay `..._is_undecided` and gain this ADR's number.**
   `outer_read_over_write_on_a_nested_array_is_undecided` and
   `inner_read_over_write_under_an_outer_select_is_undecided` did not fire,
   because nothing was built. Their panic messages now say what re-measuring is
   worth, so the next lane to move them does not re-derive 934.
4. **Do not close the select-over-`ite` gap for the benchmark reason.** It is
   worth +0. If it is closed for another reason, `controls/c2` will say so.

## Consequences

* **The nested-array frontier splits in two, and only one half is an array
  problem.** AUFLIRA + AUFNIRA (19,465 of the 20,399-file ceiling) are refutable
  and were taken by congruence. ALIA + ABV (934) are majority-satisfiable, and
  no array capability produces a `sat`.
* **Where the ALIA and ABV files actually are: quantified model construction.**
  24 ALIA and 15 ABV winnable files are reference-`sat` — the majority of both
  lists. They are `forall`-quantified SV-COMP verification conditions whose
  answer is `sat`, and producing that needs a model finder over quantifiers.
  That is a different kind of work from every nested-array lane so far: ADR-1965
  moved 273 verdicts and all 273 were `unsat`.
* **A refutation-only capability must be sized against the refutable
  denominator, not the winnable list.** This is the generalizable rule. ADR-1957
  established that a zero-disagreement claim must publish its comparable
  denominator; the same applies to a reach claim. Four lanes have now sized a
  nested-array gate against "winnable", and for AUFLIRA/AUFNIRA that was
  harmless because winnable and refutable coincide at 99%. For ALIA and ABV they
  differ by a factor of three and eight, and the whole estimate turns on it.
* **An instrument that refuses a division 187/187 needs its own REACH fixture
  before its zero means anything.** ADR-1965's instrument had a population to be
  non-vacuous against; this one did not, and two fixtures are what make its
  zeroes readable. A surrogate's refusal rate is part of its result, not a
  footnote to it.
