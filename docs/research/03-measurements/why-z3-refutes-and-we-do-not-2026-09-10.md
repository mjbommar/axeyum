# What z3 does on the 18 UF files it refutes and we do not

Measured 2026-09-10 on `s4` at `474423c8d`, load 1.9–4.0, `taskset -c 0-7`.

Item 3.5's measurement (`docs/research/03-measurements/instantiation-strategy-gap-2026-09-10.md`, a
sibling lane's note that was not yet on `main` when this was written — cited by path
rather than by link for that reason) established
that **z3 refutes 18 of the 32 UF parity-loss files at a 24 s budget with
E-matching + MBQI — the same strategy family we have — and we refute 0**, and
concluded correctly that this is not evidence for cvc5's six strategies. It did
not answer the follow-up. This note does.

**The answer, in one line: z3's refutations need 2–10 quantifier instantiations
each and land in at most 0.21 s; on 13 of the 17 files whose proof we could
extract, at least one of those instantiations substitutes a *Skolem function*
term — a term that only exists after an enclosing universal has already been
instantiated. We build those Skolem functions. We do not find the instance.**

**Recommendation: BUILD, but only two bounded items** (§Recommendation), and
**DO NOT BUILD** more clock or a higher ground ceiling — both are measured at
zero here, on top of item 3.5's 8x-ceiling arm.


> **Correction, 2026-09-10 (lane Q5).** The `+ MBQI` in that sentence is
> now bounded: `z3 smt.mbqi=false` decides the **identical 19 of 32**, file
> for file, and exactly ONE file in the whole slice is decided by z3's MBQI
> and by neither other arm (reproduced 3x). So MBQI is not how the reference
> solver beats us here — the gap is instance selection in E-matching, and
> nothing else. See
> `does-mbqi-reach-the-candidateless-universals-2026-09-10.md`.
>
> Also: this note's "2-10 instantiations" and z3's `:quant-instantiations`
> (4 to 12,055 here) are **different counters**; do not quote them
> interchangeably.

## The question, as a number

For each of the 18 files z3 refutes and we do not: what ground instance does the
refutation require, and which stage of our own pipeline fails to produce it?

Population: the 32 files in `bench-results/parity-losses-20260908/UF.txt`, all
from `/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/UF/`
(the NAS mount was live; nothing here is reproducible without it). File ids
`f01`–`f32` below are that file's line order.

**Replication of the 18.** `z3 -T:24 -st` on all 32 reproduces item 3.5's split
exactly: 18 `unsat`, 14 `timeout`, same files.

## Instrument 1 — z3's proof names the instances

z3's proof format is coarse for theory lemmas, but `(_ quant-inst t₁ … tₙ)` is
**not** coarse: it carries the substitution term-by-term. That is the ground
truth for "what instance is required", and it is the instrument used here — not
`-st`, and not inference from our own stopping point.

```sh
# `(set-option :produce-proofs true)` prepended, `(get-proof)` after (check-sat)
z3 -T:120 <file-with-proofs.smt2>
```

Proofs came back for 17 of the 18. `uf.1065126.smt2` (`f23`) solves in 0.01 s
without proofs and **times out at 120 s with them**, so it has no instance
attribution here and is excluded from every proof-derived count below.

**Coverage / positive control.** Every one of the 17 proofs contains at least
one `quant-inst` step, and the step count matches the file's difficulty ordering
from `-st`. On the smallest file the extracted instance was checked by hand
against the source and reconstructs the refutation (see `f27` below).

### How small these refutations are

`z3 -T:24 -st`, the 18 it refutes:

| | value |
|---|---|
| wall clock, worst of the 18 | **0.21 s** |
| `:quant-instantiations`, min / median / max | **4** / 194 / 12 055 |
| `:max-generation`, range | 1 – 10 |
| `:conflicts`, median | 1 |

Thirteen of the 18 finish in ≤ 0.04 s. `smtlib.1116374.smt2` and
`smtlib.1098821.smt2` each need **four** instantiations. This is not a class of
problem that wants a new strategy family; it is a class where a handful of
instances decide the file and we are not among the solvers that find them.

### What the instances look like

Rendering each `quant-inst` step's substitution (`arity` = the instantiated
universal's binder count):

```
--- f27  smtlib.1116374.smt2   2 quant-inst steps
    [5 vars]               (f17 (f18 f19) (f20 (f21 f11) f22)) , f6 , (f7 f8 (f9 f24)) ,
                           (f10 ?x66) , (f10 (f12 f13 f24))
    [3 vars] SKOLEM-FN     f24 , (?v5!1 ?x68 ?x82) , (?v6!0 ?x68 ?x82)

--- f01  x2015_09_10_16_53_56_537_1094926   2 quant-inst steps
    [6 vars]               t$ , l$a , l$ , r$a , r$ , p$
    [1 vars] SKOLEM-FN     (?v6!1 r$ r$a l$ l$a t$)

--- f22  uf.863296.smt2   2 quant-inst steps
    [1 vars]               f20
    [3 vars]               f20 , f16 , f25
```

`?v5!1`, `?v6!0`, `?v6!1` are z3's Skolem symbols, and they are **applied to
arguments**. A Skolem constant comes from the negated conclusion and is ground
from the start; a Skolem *function* can only arise from a quantifier nested
inside an enclosing universal, so `?v6!1(r$, r$a, l$, l$a, t$)` does not exist as
a ground term until the 6-variable universal above it has been instantiated at
those five constants. Every such instance is at generation ≥ 2 by construction.

Classifying all 17:

| what the required substitution contains | files |
|---|---|
| a **Skolem function** application | **13** |
| ground/compound terms only, no Skolem symbol | 4 (`f14`, `f15`, `f22`, `f26`) |

That 13 is the shape of the gap.

## Instrument 2 — where our pipeline stops

`smtcomp_cli --trace` with `AXEYUM_QPROBE=1`, plus a throwaway probe binary that
calls the pieces directly (reproduction in §Reproducing). All three of item
3.5's known recording defects were worked around, not trusted: per-rung wall
clock comes from the trail's `elapsed_ns`, `q:egraph`'s `NotApplicable` is
ignored in favour of the `AXEYUM_QPROBE` fixpoint message, and `q:mbqi`'s clock
is not quoted at all.

### Finding 1 — we DO build the Skolem functions

`quant_skolemize` with the shipped `Nested` layout, counting distinct `!qskf`
function symbols in the Skolemized assertion set:

| file class | distinct Skolem functions produced |
|---|---|
| the 13 files whose proof needs one | **2 – 341** (median 118) |
| `f14`, `f15` (ground-only instances) | 0 |

So the failing stage is **not** "the term is never formed". On every one of the
13, the pass that manufactures exactly the kind of term z3 instantiates with
fires, and produces hundreds of them.

### Finding 2 — the e-matching loop CAN close two of them, and the ladder never gets there

A probe ran `prove_quantified_unsat_via_egraph` on (a) the parsed assertions and
(b) the **Skolemized** assertions, each with the whole 24 s budget:

| arm | of the 18 z3 refutes | of the 14 z3 also times out on |
|---|---|---|
| loop on the original assertions, 24 s | **0** | 0 |
| loop on the **Skolemized** assertions, 24 s | **2** (`f27`, `f31`) | **0** |

`f27` refutes in **87 ms**, `f31` in **2.4 s**. The 0-of-14 column is the
negative control: the arm does not simply say `unsat` more often.

**`f27` is a routing defect, and it is exact.** `prove_unsat_by_ematching`
(`auto.rs:8822`) hands the e-graph loop the Skolemized set only under
`if retried.residual_quantifier`, i.e. only when a one-shot cartesian
instantiation happens to leave a quantifier behind. On `f27` it does not —
`AXEYUM_QPROBE` prints `ematch retried residual=false instantiated=true` on both
MBQI rungs — so **the loop is never handed the Skolemized assertions at all**,
at any budget. It is handed the original ones by `q:egraph`, where the nested
universal is still present and its registration admits zero instances
(`QPROBE universal[5] vars=4 patterns=2 joined=543 starved_joins=0 admitted=0`).

Confirmed independently by rewriting the file rather than the solver: replacing
`f27`'s negative-position nested `(forall ?v5 ?v6 …)` with its body at two
explicitly declared Skolem functions — an equisatisfiable edit, and the only
edit — flips our verdict.

```
arm A  f27 as shipped                        unknown
arm B  nested forall hand-Skolemized         unsat   (decided_by=q:egraph)
arm C  arm B + z3's two instances asserted   unsat
```

Control that arm B is not vacuously unsat: with the negated goal deleted it is
`sat` under z3, and all three arms are `unsat` under z3.

**`f31` is a second, unidentified routing difference.** The loop refutes it from
the parsed assertions in 2.4 s at a 3 s budget. Inside the ladder at a 120 s
budget the same rung receives **27.8 s**, runs 6.6 s, reaches
`ground=3284 foralls=3`, and reports a fixpoint with no refutation. Ruled out by
direct arms, each of which still refutes: the clock (3 s suffices), the one-shot
cartesian pre-pass (`instantiate_with_triggers` on the same arena first), and
each of the ladder's three pre-rewrites applied cumulatively
(`normalize_top_level_quantified_counterexamples`,
`skolemize_top_existentials`, `eliminate_valid_universals`). **Not identified:
what else differs between the parsed assertion set and the one the ladder holds
by that rung.** The `q:egraph` rung's own fixpoint census differs between the two
by one ground term (424 vs 423) on this file, so the sets are not identical.

### Finding 3 — it is not the clock, and the ladder does not even spend it

The shipped ladder at **5x** the budget the loss list was produced at:

```sh
./target/release/examples/smtcomp_cli <file> --timeout-ms 120000 --trace
```

| | files decided of 32 |
|---|---|
| 24 s (item 3.5's arm) | 0 |
| **120 s** | **0** |

And 24 of the 32 return `unknown` **before** the 120 s budget is spent —
7.9 s, 8.9 s, 10.9 s, … 90.6 s. Combined with item 3.5's 8x ground-ceiling arm
(also 0), the two obvious levers are now both measured at zero from two
directions.

### Finding 4 — what the remaining 13–15 look like

The ground set the loop accumulates in the shipped 24 s run, against the 2–10
instantiations z3 needs:

| | files of the 18 |
|---|---|
| reached the 8192 ground ceiling | **13** |
| stopped below it | 4 (`f17` 24, `f29` 273, `f31` 424, `f27` 656; `f22` 2017) |

And the scale the loop is working at. On the twelve largest of the 18, the
Skolemized set carries **311–499 assertions** with **735–1890 surviving
universal binders**. z3 closes the same files with a median
of 194 instantiations and one conflict. We are not short of instances; we are
generating the wrong ones, in a space three orders of magnitude wider than the
refutation needs.

`uf.966336.smt2` (`f29`) remains the sharpest reproducer, and this note
sharpens it further: 27 Skolemized assertions, 49 binders, **5 Skolem functions
built**, saturation at 273 ground terms — and z3 refutes it in 0.02 s with
**18** instantiations, two of which use a Skolem term.

## The per-file classification

| id | file | z3 | z3 wall | z3 qinst | instance needs | our blocker |
|---|---|---|---|---|---|---|
| f27 | Hoare/smtlib.1116374 | unsat | 0.02 s | 2 | Skolem fn | **R** routing — loop never handed the Skolemized set |
| f31 | TypeSafe/smtlib.1098821 | unsat | 0.02 s | 4 | Skolem fn | **R** routing — loop refutes it standalone, not in the ladder |
| f01 | bindag/…1094926 | unsat | 0.03 s | 2 | Skolem fn | **S** selection, flooded to 8192 |
| f05 | coinductive_list/…2416479 | unsat | 0.04 s | 3 | Skolem fn | **S** |
| f06 | coinductive_list/…2500061 | unsat | 0.06 s | 10 | Skolem fn | **S** |
| f07 | coinductive_list/…2906170 | unsat | 0.04 s | 4 | Skolem fn | **S** |
| f10 | gram_lang/…1432776 | unsat | 0.02 s | 2 | Skolem fn | **S** |
| f12 | rbt_impl/…992499 | unsat | 0.03 s | 5 | Skolem fn | **S** |
| f18 | Arrow_Order/uf.704291 | unsat | 0.04 s | 6 | Skolem fn | **S** |
| f19 | Arrow_Order/uf.813308 | unsat | 0.04 s | 4 | Skolem fn | **S** |
| f28 | Hoare/uf.834137 | unsat | 0.05 s | 9 | Skolem fn | **S** |
| f29 | Hoare/uf.966336 | unsat | 0.02 s | 6 | Skolem fn | **S′** selection, saturated at 273 |
| f17 | Arrow_Order/smtlib.663965 | unsat | 0.05 s | 9 | Skolem fn | **C** clock — watchdog kills `q:egraph` (120.7 s open) |
| f14 | instantiated/dl_remove_postcondition_50_4 | unsat | 0.21 s | 93 | ground only | **G** selection, flooded to 8192 |
| f15 | uninstantiated/dl_copy_invariant_19_2 | unsat | 0.01 s | 15 | ground only | **G** |
| f22 | FFT/uf.863296 | unsat | 0.02 s | 2 | ground only | **G**, stops at 2017 |
| f26 | Fundamental_Theorem_Algebra/uf.974621 | unsat | 0.20 s | 4 | ground only | **G** flooded to 8192 |
| f23 | Fundamental_Theorem_Algebra/uf.1065126 | unsat | 0.01 s | — | **unknown** (proof timed out) | unattributed |

**Counts: R 2, S 9, S′ 1, C 1, G 4, unattributed 1.**

So it is **not** 18 different reasons, and it is **not** one. It is two
mechanisms plus a tail:

- **2 files are a routing defect** — the machinery already refutes them; the
  dispatch ladder does not let it.
- **14 files are instance selection** (S + S′ + G) — the required instance is
  reachable in principle, the loop generates thousands of others first, and 13
  of them fill the 8192 ground cap. On 10 of those 14 the required instance is at
  generation ≥ 2 behind a Skolem-function term, which is why the trigger that
  would produce it cannot fire in round 1.
- **1 file is the clock** and **1 is unattributed.**

## Recommendation

**BUILD**, two items, both small and both grounded in a flipped verdict:

1. **Hand the e-matching loop the Skolemized assertion set unconditionally.**
   `prove_unsat_by_ematching`'s `if retried.residual_quantifier` gate is a proxy
   for "the cheap route failed", and on `f27` it is the wrong proxy: the cheap
   route *succeeded* at instantiating and still did not decide, so the loop —
   which refutes the file in 87 ms — is skipped. Worth ≥ 1 of 18 measured, plus
   whatever it is worth on population B, which was not swept here.
2. **Find why `f31` refutes standalone and not in the ladder.** 2.4 s vs 27.8 s
   on the same rung, with clock, pre-instantiation and all three pre-rewrites
   already ruled out. This is the highest-information single bug in the set,
   because it says the ladder loses refutations the loop finds for a reason
   nobody has named. Worth ≥ 1 of 18, and it may be the same defect that costs
   the S class rounds it never gets.

**DO NOT BUILD:**

- More budget. 120 s decides 0 of 32, and 24 of 32 exit early.
- A higher ground ceiling. Item 3.5 measured 8x at 0; this note adds that the
  four files stopping *below* the ceiling include the two we can already close.
- Any of cvc5's six strategies. Nothing changed item 3.5's conclusion; the
  refutations z3 finds are E-matching refutations at generation ≤ 10.

**The 14 remaining are one problem, not fourteen: instance selection at a scale
of 250–500 assertions and ~1000 binders, where z3 needs a median of 194
instantiations.** That is a relevance/priority problem (z3's `qi_queue` cost
model, relevancy propagation, its generation-ordered queue), and it is the
follow-up item this measurement supports — but it is a bigger piece of work than
either item above and should be scoped after they land.

## What I did not measure

- **cvc5.** Still not installed on `s4`. Unchanged from item 3.5.
- **Whether our loop would find the specific instance if handed the Skolem term
  directly.** Arm C did this for `f27` only (and it was already `unsat` at arm
  B, so arm C is not load-bearing). Mapping z3's Skolem symbols onto ours is
  per-file manual work and was not done for the other 12.
- **Whether the required term ever enters our e-graph.** I measured that the
  Skolem *symbols* are built (Finding 1) and that the *instance* is not found.
  The three sub-cases the brief asked to separate — trigger not selected,
  pattern not matched, term not in the e-graph — are **not** separated for the
  S class. Doing so needs a dump of the loop's ground set and a structural match
  against the proof's instance terms, which is the natural next probe.
- **`f23`.** z3 refutes it in 0.01 s and cannot produce a proof for it in 120 s,
  so nothing here says what it needs.
- **Population B** (the random NAS `UF`/`UFLIA`/`UFNIA` draw) and
  `corpus/regression`. Everything here is population A only. The routing fix in
  item 1 should be re-measured against B before its value is quoted.
- **`AXEYUM_NESTED_QUANT=0`.** Every arm ran with the shipped `Nested` layout.
- **Contention.** Sweeps ran 4-wide at load 1.9–4.0 pinned to the P-cores.
  Verdict counts are robust to this; the wall-clock numbers are ratios, not
  absolutes. The `f31` 2.4 s / 27.8 s contrast is a verdict difference, not a
  timing one, so contention does not explain it.

## Reproducing

Populations and z3 arms need only the NAS mount:

```sh
cp bench-results/parity-losses-20260908/UF.txt /tmp/pop-A.txt
z3 -T:24 -st <file>                       # the 18/14 split
# proofs: prepend (set-option :produce-proofs true), append (get-proof)
z3 -T:120 <file-with-proofs.smt2>         # then grep '(_ quant-inst'
```

The shipped-ladder arms need only the committed binary:

```sh
scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli
AXEYUM_QTRACE=1 AXEYUM_QPROBE=1 ./target/release/examples/smtcomp_cli \
  <file> --timeout-ms 120000 --trace
```

Findings 1 and 2 used a throwaway probe, removed per the Phase 3 brief. It was
~60 lines: an example in `crates/axeyum-bench` modelled on
`examples/uf_unknown_probe.rs` that parses with `axeyum_smtlib::parse_script` and
calls three `#[doc(hidden)] pub` shims added to `axeyum-solver` for the run —
one wrapping `quant_skolemize::skolemize_assertions_with_layout` +
`prove_quantified_unsat_via_egraph`, one adding the ladder's three pre-rewrites
in stages, and one counting `!qskf` symbols and surviving binders in the
Skolemized set. It is worth re-creating rather than keeping: the shims are
`pub(crate)`-piercing and should not be public API, and `examples/route_solo.rs`
already has the right shape and only lacks the two quantified routes in its
table. The per-file dumps live in this session's scratchpad and are not
committed.

`f27`'s hand-Skolemized arms are a three-line edit to
`UF/sledgehammer/Hoare/smtlib.1116374.smt2`: declare `sk5`/`sk6` over the two
enclosing `S5` variables, and replace `(forall ((?v5 S10) (?v6 S10)) B)` with
`B[?v5 := (sk5 ?v3 ?v4), ?v6 := (sk6 ?v3 ?v4)]`.
