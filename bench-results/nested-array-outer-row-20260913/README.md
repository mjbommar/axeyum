# Sizing ADR-1965's named next gate: outer read-over-write on a nested array

**The measurement, committed before any solver code, so the build's number can
be checked against it rather than fitted to it.**

[ADR-1965](../../docs/research/09-decisions/adr-1965-the-nested-array-prize-was-never-the-array-theory-it-was-congruence.md)
took AUFLIRA from 10 to 164 and AUFNIRA from 3 to 122, and named what did not
move and why:

> **Next gate: outer read-over-write on a nested array.** ALIA (511 files) and
> ABV (423) sit behind it. It needs a *different* instrument — ADR-1965's
> surrogate refuses exactly those files by construction.

This directory is that instrument and its result.

## The headline

**Outer read-over-write, handed to the solver for free by a sound rewrite, is
worth 0 files on ALIA and 0 marginal files on ABV.** The named gate is not the
one holding ALIA's 511 and ABV's 423.

Three independent reasons, and the first settles it before reach is even
measured:

1. **39 of the 53 winnable ALIA + ABV files are satisfiable.** Outer
   read-over-write is a refutation mechanism; it cannot produce a `sat`. The
   ceiling on the whole gate is therefore 170 + 50 = **220 files**, not 934 —
   and that is the ceiling *if every refutable file fell to it*.
2. **Of the refutable remainder, it reaches none.** The surrogate below removes
   the nested sort entirely and performs outer read-over-write by hand. axeyum
   answers `unknown` on 18 of 18 accepted ALIA files and 8 of 9 accepted ABV
   files. The one ABV file it does refute is **the same file ADR-1965's
   surrogate already reached**, and that file contains **zero outer stores** —
   so outer read-over-write contributed nothing to it.
3. **And the solver never searches them.** The five refutable-and-accepted ALIA
   files, re-run at a **300 s** budget — 12.5x the board's — are still
   `unknown`, and every one of them declines in **0.11–0.13 seconds**. It is not
   a clock, it is a route: read-over-write is a rule you add to a route, and no
   route runs.

## The instrument

`scripts/nested_array_outer_row_surrogate.py`. ADR-1965's surrogate turned the
outer array into an uninterpreted sort, which *deletes* outer read-over-write
and is why it refused
33 of 36 ALIA and 12 of 17 ABV winnable files. This one does the opposite: it
**curries** the outer level and keeps read-over-write.

For each arity-0 declaration `M : (Array I (Array J E))`:

* `M` becomes an uninterpreted function `M_row : I -> (Array J E)`;
* `(select M j)` becomes `(M_row j)`;
* an outer `store` is eliminated where it is read, by the read-over-write axiom
  applied syntactically: `(select (store A i r) j)` → `(ite (= i j) r (select A j))`.

The inner level is untouched — `(Array J E)` stays a real array, and a
quantifier binding an inner array variable stays one. That matters: the SV-COMP
memory model these files come from quantifies over inner arrays (`v_ArrVal_*`)
on almost every line.

### Soundness

On the accepted fragment the rewrite is model-preserving in both directions
(`M_row(i) := M[i]` one way, `M[i] := M_row(i)` the other; the `store`
expansion is the axiom itself, an equivalence). **The reach number does not rest
on that stronger claim.** It counts only `unsat`, the direction that survives
even if the equisatisfiability argument has a hole:

> surrogate `unsat` ⟹ original `unsat`.

A surrogate `sat` is printed in its own column and counted nowhere, exactly as
ADR-1965 did.

Outer **extensionality** is the one axiom currying does not have, and it is
unreachable on the accepted fragment for the same reason the fragment is
accepted: an extensionality instance needs an equality between two outer array
terms, and every such context is refused.

### The refusals, and what they name

| refusal | ALIA | ABV | AUFLIRA | AUFNIRA |
|---|---:|---:|---:|---:|
| outer array **equality** (extensionality) | 15 | 8 | 0 | 0 |
| outer array passed to a **function** | 0 | 0 | 185 | 129 |
| no nested array at all | 3 | 0 | 2 | 10 |

The refusal reason is the gate *behind* this one, per file, and it is different
for the two families: ALIA and ABV are held by outer **extensionality**;
AUFLIRA and AUFNIRA pass outer arrays to functions, which is why this instrument
has nothing to say about them and ADR-1955 recommended against currying for
them.

## The numbers

Pinned full-span winnable lists from
`bench-results/tier1-divisions-headtohead-20260913/winnable/`, 24 s budget,
`taskset`-pinned P-cores. Raw per-file data in `sweep/`.

### 1. Reach

| division | winnable | rewritten | refused | ax `unsat` | ax `sat`* | reach | ADR-1957 ceiling | projected |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFLIRA | 187 | 0 | 187 | 0 | 0 | 0.0% | 18,510 | 0 |
| AUFNIRA | 139 | 0 | 139 | 0 | 0 | 0.0% | 955 | 0 |
| **ALIA** | 36 | 18 | 18 | **0** | 0 | **0.0%** | 511 | **0** |
| **ABV** | 17 | 9 | 8 | **1**† | 0 | 5.9% | 423 | 25† |
| **total** | 379 | 27 | 352 | **1** | 0 | | 20,399 | **25**† |

\* a surrogate `sat` transfers nothing and is counted nowhere.

† **the 25 is not attributable to this gate.** The single ABV file is
`ABV/20190429-UltimateAutomizerSvcomp2019/dancing_true-unreach-call_false-valid-memtrack.i_0.smt2`,
which ADR-1965's surrogate already reached (`bench-results/nested-array-build-20260913/sweep/ABV.tsv`),
and which has **0 outer stores** — read-over-write has no instance in it.
**The marginal contribution of outer read-over-write is 0 on every division.**

**What the one ABV file actually represents.** It is reachable by an
outer-level ABSTRACTION — ADR-1965's uninterpreted-sort surrogate and this
lane's currying surrogate both refute it — and the shipped nested-array build
does **not** decide it: ADR-1965's own post-merge A/B records both arms
`unknown` at 0.11 s on it, an immediate decline rather than a timeout. So it is
an unrealized **+1 for the congruence route**, not evidence about
read-over-write, whose axiom it contains no instance of. Counting it toward
this gate would be the error this footnote exists to prevent.


### 2. Soundness control

z3 on the ORIGINAL against z3 on the SURROGATE, per accepted file. Every
accepted file is an opportunity, not only the refutable ones:

```
z3 agrees 14 / 14, no opinion 13, CONTRADICTS 0
```

The **no-opinion 13** is published beside the zero, as
[ADR-1957](../../docs/research/09-decisions/adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md)
requires. 13 of the 27 accepted files are ones z3 does not decide within 24 s on
one side or the other, so the control fired on 14. That is a small denominator
and it is stated rather than hidden; the six fixtures in `controls/` are what
make up for it, because each carries a verdict both references confirm.

### 3. The refutable denominator — the reason the ceiling is 220, not 934

| division | winnable | reference `unsat` | reference `sat` | gate ceiling |
|---|---:|---:|---:|---:|
| AUFLIRA | 187 | 186 | 1 | 18,411 |
| AUFNIRA | 139 | 139 | 0 | 955 |
| **ALIA** | 36 | **12** | **24** | **170** |
| **ABV** | 17 | **2** | **15** | **50** |

Read from the board's own pinned TSVs (z3, then cvc5), not re-measured.

Crossing that split against acceptance and reach gives the sharpest form of the
finding — the cell that matters is the bottom-right of each block:

| division | reference | surrogate | axeyum | n |
|---|---|---|---|---:|
| ALIA | `sat` | REFUSED | — | 11 |
| ALIA | `sat` | ok | `unknown` | 13 |
| ALIA | `unsat` | REFUSED | — | 7 |
| **ALIA** | **`unsat`** | **ok** | **`unknown`** | **5** |
| ABV | `sat` | REFUSED | — | 7 |
| ABV | `sat` | ok | `unknown` | 8 |
| ABV | `unsat` | REFUSED | — | 1 |
| **ABV** | **`unsat`** | **ok** | **`unsat`** | **1**† |

**Five ALIA files are refutable AND inside the fragment AND got outer
read-over-write performed for them. axeyum decided none of the five.** That is
the whole of the gate's opportunity on ALIA, and it is 0 for 5.

**This is the structural finding.** AUFLIRA and AUFNIRA are 99%+ refutable,
which is why a refutation-only capability — congruence through the nested read —
took 273 of them. ALIA is 67% satisfiable and ABV 88%. A gate that can only
produce `unsat` is aimed at the smaller third of one list and the smaller eighth
of the other.

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

### 4. The `--distribute` arm

The currying leaves an array-sorted `ite` behind (the read-over-write expansion
*is* one), and `controls/c2` shows axeyum answers `unknown` with that shape and
`unsat` without it. So the sweep was run again with `select` pushed through
every array-sorted `ite`:

| division | plain | `--distribute` | delta |
|---|---|---|---:|
| ALIA | 0 / 18 | 0 / 18 | **+0** |
| ABV | 1 / 9 | 1 / 9 | **+0** |

`crates/axeyum-rewrite/src/arrays.rs` already has that rewrite — it is
`eliminate_arrays`' own — and these queries do not reach it. Closing that is
worth a control fixture and **zero benchmark files**.

## The instrument's own controls

`controls/run-controls.sh`. This matters more than usual here, because
**AUFLIRA and AUFNIRA refuse 187/187 and 139/139 under this surrogate**, so
unlike ADR-1965's instrument this one has no natural population where it is
known to reach something. Without the fixtures below, a reach of 0 on ALIA
would be indistinguishable from an instrument that cannot reach anything — the
vacuous zero ADR-1957 warns about.

```
fixture                                kind    ax_surr  z3_surr  z3_orig  cvc5_orig  result
c1-outer-row-refutation                REACH   unsat    unsat    unsat    unsat      PASS
c2-outer-row-disjoint-index            GAP     unknown  unsat    unsat    unsat      PASS
c3-distinct-rows-are-satisfiable       SAT     unknown  sat      sat      sat        PASS
c4-quantified-inner-row-is-satisfiable SAT     unknown  sat      sat      unknown    PASS
c5-outer-equality-is-refused           REFUSE  -        -        unsat    unsat      PASS
c6-shared-outer-store-under-let        REACH   unsat    unsat    unsat    unsat      PASS
```

* **`c1` and `c6` are the non-vacuity proof**: the instrument does produce a
  reach, on a query whose refutation needs outer read-over-write and nothing
  else. So the zeroes above are about the population, not the instrument.
* **`c3` and `c4` are adversarial over satisfiable queries**: a rewrite that
  relaxed the `ite` guard of the expansion, or that captured a quantified inner
  row while inlining a `let`, would flip one of them to `unsat` and the reach
  number would be counting refutations of things that are true.
* **`c5`** is the fragment boundary: an unsat query whose refutation needs outer
  extensionality must be REFUSED, not rewritten.
* Every fixture's own claimed verdict is checked against z3 **and** cvc5 on the
  ORIGINAL, so a fixture cannot be wrong about its own subject.

`python3 scripts/nested_array_outer_row_surrogate.py --self-test` carries 16 further checks on the rewrite
itself, including the shape of the expansion and the four refusal classes.

## Reproducing

```sh
python3 ../../scripts/nested_array_outer_row_surrogate.py --self-test
./controls/run-controls.sh 24
./sweep.sh ALIA ../tier1-divisions-headtohead-20260913/winnable/ALIA.txt  <outdir> 24
./sweep.sh ABV  ../tier1-divisions-headtohead-20260913/winnable/ABV.txt   <outdir> 24
./sweep.sh ALIA ../tier1-divisions-headtohead-20260913/winnable/ALIA.txt  <outdir2> 24 --distribute
python3 summarize.py <outdir> --dist <outdir2>
```

## What this says the next lane should look at

Not outer read-over-write. The two candidates the measurement actually names:

1. **Outer array equality / extensionality** — the refusal reason for 15 of 36
   ALIA and 8 of 17 ABV winnable files. But 18 of those 23 are reference-`sat`,
   so the refutable part of it is 5 files, and the same ceiling argument applies.
2. **Quantified model construction (`sat` on AUFLIA/ABV memory-model queries)** —
   24 ALIA and 15 ABV winnable files, the majority of both lists, and something
   no array capability reaches. These are `forall`-quantified SV-COMP
   verification conditions whose answer is `sat`; producing that needs a model
   finder over quantifiers, not an array theory.

The second is where the files are. It is also a different kind of work from
every nested-array lane so far, all of which delivered `unsat` only: ADR-1965's
273 moved verdicts were 273 of 273 `unsat`.
