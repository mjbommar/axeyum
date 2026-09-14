# ADR-2005: the instances a refutation needs are e-matchable, we already build them, and the witness we substitute is the wrong member of the class

Status: accepted
Index-summary: [ADR-1995] closed the budget question at **0 of 87** and handed over *"the vein is instance selection, not clock"*. This lane tested the named suspicion behind it — that a refutation may need terms **pure e-matching structurally cannot generate**, so the missing capability is enumerative or model-based instantiation — and it **does not survive**. A **reference ablation** answers the capability question without our own instrumentation: of the **115** winnable `UFNIA`/`UFLIA` files cvc5 decides, `--no-enum-inst --no-cegqi` decides **111 the same way — 97 %, Wilson 95 % `[91 %, 99 %]`** (`UFLIA` 66/66, `UFNIA` 45/49), and **0 of 115 need the COMBINATION** — the four exceptions all refute under `--no-e-matching`. Both flags are shown live by MECHANISM (`default` emits 4 instantiation tuples and refutes where `--no-enum-inst` emits **zero**), because "5 of 129 verdicts moved" is equally what a silently ignored flag looks like. The brief's own exemplar refutes its hypothesis: `f2_rw160`'s refutation runs entirely through the **two `pow2` lemmas carrying NO `:pattern`** while the `:pattern ((instantiate_me a))` fence contributes nothing — and `pow2_base_cases` writes `(pow2 0)`, `(pow2 1)`, `(pow2 2)`, `(pow2 3)` into the file **as applications**, so "enumeration over small numerals" is a two-variable multi-pattern over a five-element match set. Reduced to a minimal file, **we refute it** (negative control refuted by neither us nor cvc5). Our own ground dump holds every application needed — `(pow2 0)` 1,256 rows, `(pow2 3)` 1,254 — so this is **[Q2]'s case (ii), "we build it and rank it 1000th", the OPPOSITE of Q2's `UF` finding**, and the two families need different fixes. The defect is located: `InstBridge::repr_term` is `entry(root).or_insert(term)` — **first-inserted, not smallest** — and is keyed on the root **as it was at insertion time**, never repaired when a later `merge` re-roots the class, so `(= (pow2 0) 1)` makes us substitute the application and build `(pow2 (pow2 0))`: **1,128 nested rows against 4 instances at bare numerals**, a ~280:1 dilution. `AXEYUM_QINST_SMALLEST_WITNESS` (**ships OFF**) fixes exactly that — nested rows **1,128 → 500**, useful instances **20 → 36** — and **decides nothing**: `UFNIA` +0, `UFLIA` +1, `UF` control +0 with the route binding **40 + 13** of its 110 undecided rows; three `UFLIA` passes give **+1 / −2 / +0**, base band **3 files**, and **all 3 moved rows are UNSTABLE — zero STABLE-GAIN, zero STABLE-LOSS**, 0 disagreements and 0 sat↔unsat flips in 1,200 solves. **Measured +0, Wilson `[0.0 %, 0.9 %]`**, and the arm costs **+5.0 %** wall on `UF`. So the vein is selection rather than clock, but **not because we cannot reach the instances** — we reach, build and admit them; **do not size a lane against enumerative instantiation on this population**, it would be aimed at 4 files of 115. Bucket N is published BOTH ways because it is contaminated: cvc5 prints `(+ -1 (typeof S))` where the source writes `(- (typeof S) 1)`, and **727 of 2,544 N terms (28.6 %) have an arithmetic head**; on `2019-Preiner` the split is **Q=32, G=0, N=0, S=9**. Numerals are only **12.7 %** of distinct instantiating terms, and the explicit-`:pattern` shape is a **per-family** property (`vcc-havoc` 279/375, `spec_sharp` 199/224 against **0 of 1,446** for `sledgehammer`/`simplify`/`grasshopper`), not a division one.
Index-status: accepted
Date: 2026-09-13

## Context

[ADR-1995] closed the budget question on `UFLIA`/`UFNIA` — the target family is
**0 of 87** under a genuine one-way clock ceiling — and handed over one sentence:
*"the vein is instance selection, not clock."* This lane was briefed to test
whether that is true, and specifically to test a named hypothesis:

> the winning instantiations use small integer numerals and Skolem constants, and
> if a refutation needs `pow2 2` where the numeral `2` occurs nowhere in the
> query, then pure e-matching — which only instantiates with terms already in the
> e-graph — **structurally cannot generate it, at any budget**. That would mean
> the missing capability has a name (enumerative / model-based instantiation over
> small domains) rather than being "more search".

The brief was explicit that this was a hypothesis to test and not to build
toward. It does not survive, and the direction it fails in is the useful part.

Sizing and method were [pre-registered](../../../bench-results/inst-select-20260913/PREREGISTRATION.md)
in their own commit (`e9b2b75bd`) before the population was touched, including
the prediction that the hypothesis would fail — recorded so it could be wrong.

## The measurement that settles it: a reference ablation

The capability question can be answered without our own instrumentation at all.
cvc5 lets its instantiation strategies be switched off independently, so the
population can be run in four arms and the arms compared against cvc5's own
default verdict. All 129 winnable `UFNIA`/`UFLIA` rows, 24 s / 8 GiB / one pinned
physical core.

| division | rows | `default` | `ematch`<br>(`--no-enum-inst --no-cegqi`) | `noematch`<br>(`--no-e-matching`) | `neither` |
|---|---:|---:|---:|---:|---:|
| `UFNIA` | 61 | 49 unsat | 45 | 29 | 25 |
| `UFLIA` | 68 | 66 unsat | 66 | 18 | 18 |

**Of the 115 files cvc5 decides, e-matching alone decides 111 the same way — 97 %,
Wilson 95 % `[91 %, 99 %]`** (`UFLIA` 66 of 66; `UFNIA` 45 of 49).

And the complement: **0 of 115 need the combination.** Every file cvc5 decides is
decided either with e-matching alone or with e-matching switched off entirely.
The four `UFNIA` exceptions are all `2019-Zohar-ic` and all refute under
`--no-e-matching`, so even they are not evidence of an e-matching-shaped wall.

**The arms are not a partition and are not reported as one.** A file may refute
in several. Only a *success* under `ematch` is load-bearing; a failure there says
nothing about e-matching in general, because cvc5's e-matching is one
implementation with its own trigger inference.

**Both levers are shown live by MECHANISM, not by verdict counts** — "5 of 129
verdicts moved" is equally consistent with a live lever and with a silently
ignored flag plus ambient noise. On
`UFNIA/2019-Zohar-ic/qf/int_check_bvsge_bvneg_ltr_no_inv.smt2`, `default` emits
**4 instantiation tuples and refutes**; `--no-enum-inst` emits **zero** and
returns `unknown`. `--no-e-matching` moves 73 of 129 rows.

`NONE` — a run producing no verdict-shaped line — is kept distinct from
`unknown` throughout. All 7 were re-run individually: every one is cvc5's own
`--tlimit` firing (`cvc5 interrupted by timeout`), not a crash or an OOM, so they
sit outside the denominator of 115 rather than inflating it.

## The brief's exemplar, read to the bottom

`UFNIA/2019-Preiner/combined/f2_rw160.smt2` is the file the brief names. It has
**two** top-level assertions, `(assert pow2_ax)` and `(assert (not (forall …)))`,
and `pow2_ax` expands to a block of `pow2` lemmas of which exactly **two carry no
`:pattern`** — `pow2_weak_monotinicity` and `pow2_strong_monotinicity`. Every
other lemma in the file is fenced behind `:pattern ((instantiate_me a))`.

Those two triggerless lemmas are **precisely the two quantifiers cvc5's dump
shows it instantiating**. The `instantiate_me` fence contributes nothing.

The hypothesis fails on its own exemplar, and not narrowly:

    (define-fun pow2_base_cases () Bool
      (and (= (pow2 0) 1) (= (pow2 1) 2) (= (pow2 2) 4) (= (pow2 3) 8)))

`(pow2 0)`, `(pow2 1)`, `(pow2 2)` and `(pow2 3)` are **written in the file, as
applications**. A trigger inferred from the lemma body is the multi-pattern
`{(pow2 i), (pow2 j)}`, and matching it against those four ground applications
plus the Skolem for `k` yields exactly the cross-product cvc5 printed. What looked
like enumeration over a small domain is a two-variable multi-pattern over a
five-element match set. "`pow2 2` where the numeral `2` occurs nowhere" is the
one thing this file is not.

**Reduced to a minimal file** carrying just that lemma and those applications,
**we refute it** — `unsat`, `triggerless=0`, the multi-pattern inferred. Its
negative control (the consistent inequality, same shape) is refuted by neither us
nor cvc5, so the pair is non-vacuous in both directions. The machinery is
present; the failure is one of scale and context, not of reach.

## Where our loop actually goes wrong

Our own ground set for that file, dumped at give-up via `AXEYUM_QGROUNDDUMP`,
contains every application the winning instantiation needs — thousands of times:

    (pow2 !sk_2) 1481    (pow2 0) 1256    (pow2 3) 1254
    (pow2 2)     1174    (pow2 1) 1174

So this is **[Q2]'s case (ii)** — *"we build it and rank it 1000th"* — and the
exact opposite of Q2's `UF` finding, where the required term was never built at
all. **The two families need different fixes, and the `UF` one does not transfer
here.**

The instances themselves are there too, and so is the problem. In the same dump:

    GROUND 14 gen=1 (=> (and (>= (pow2 0) 0) (>= (pow2 1) 0))
                        (=> (<= (pow2 0) (pow2 1))
                            (<= (pow2 (pow2 0)) (pow2 (pow2 1)))))

We instantiated the monotonicity lemma with `i := (pow2 0)` where `i := 1` would
do. The base equation `(= (pow2 0) 1)` merges the application with the numeral,
and the substituted witness is the *application*, so the instance carries
`(pow2 (pow2 0))` and the term grows.

    1,128 rows carrying a nested (pow2 (pow2 …))
        4 instances of the lemma at bare numerals

**The useful instances are built and then diluted about 280 : 1** by term growth
the representative choice introduced.

### The defect, located

`InstBridge::repr_term` is filled with `entry(root).or_insert(term)` and read at
both witness sites as the substitution term for a matched class. Two consequences,
neither intended:

- it is **first-inserted, not smallest**; and
- it is keyed on the class root **as it was at insertion time**, and is never
  repaired when a later `merge` re-roots the class — so after a union one of the
  two classes' terms becomes unreachable as a witness, whichever it happened to be.

## Decision

**Record the finding; ship the fix OFF.**

`AXEYUM_QINST_SMALLEST_WITNESS` (`off`/`0`/`false`/empty/unparseable/absent all
resolve to the shipped behaviour) substitutes the **smallest** ground member of a
matched class, recomputed against the class as it stands rather than as it was at
insertion.

**Soundness is structural, not empirical.** Every admitted instance is
`body[x := t]`, and `∀x. B ⊨ B[x := t]` holds for *every* ground `t` — it does not
depend on where `t` came from. A class member is ground and equal to every other
member, so choosing a different one changes *which* entailed instance is admitted,
never *whether* it is entailed. This is the separation the trigger machinery
already documents: a trigger proposes, it never justifies.

### The arm does what it was built to do, and it decides nothing

Same file, same core, both arms:

| arm | verdict | ground rows | nested `(pow2 (pow2 …))` | lemma at bare numerals |
|---|---|---:|---:|---:|
| base | `unknown` | 1,654 | **1,128** | 20 |
| smallest-witness | `unknown` | 1,877 | **500** | **36** |

**The dilution more than halves and the useful instances nearly double, and the
verdict does not move.** That is the finding, and it is why the lever ships off
rather than being tuned: the representative choice is a real defect, it is worth
having named and fixed behind a flag, and it is **not what stands between us and
these refutations**.

### The A/B, and why its one gain is not one

Interleaved per-file, **one binary and two env values**, both arms back to back
on the same file on the same pinned physical core with the order alternating,
24 s wall / 8 GiB `ulimit -v`, 6 shards on s5 and s6. Branch `1a9054710`;
`git merge-base main HEAD` is `2611e14b0`, which **is** `main`'s HEAD, so the
base arm is the shipped tree.

| division | n | base | arm | net | gain | loss | sat↔unsat flips |
|---|---:|---:|---:|---:|---:|---:|---:|
| `UFNIA` | 200 | 53 | 53 | **+0** | 0 | 0 | 0 |
| `UFLIA` | 200 | 72 | 73 | **+1** | 1 | 0 | 0 |
| `UF` *(control)* | 200 | 89 | 89 | **+0** | 0 | 0 | 0 |

`UFNIA`'s base of 53 reproduces the pinned board and [ADR-1995]'s figure exactly.

**Soundness, with the comparable denominator on the same line ([ADR-1957]):**

    UFNIA  vs :status 14/14 base, 14/14 arm
    UFLIA  vs :status 72/72 base, 73/73 arm
    UF     vs :status 87/87 base, 87/87 arm
    DISAGREEMENTS: 0.  sat<->unsat flips: 0 in 1,200 solves.

**The control is not vacuous, and the number saying so is published rather than
asserted.** Of `UF`'s 110 undecided rows, `q:mbqi` — the rung this loop runs
under — binds **40**, and `q:egraph` another **13**; 16 of the 200 rows run the
instantiation loop far enough to dump a ground set. The route runs on the
control, and the control is flat.

**Then the `UFLIA` division was run three independent times, and the +1
evaporated.**

| pass | base | arm | net |
|---|---:|---:|---:|
| 1 | 72 | 73 | +1 |
| 2 | 75 | 73 | **−2** |
| 3 | 74 | 74 | +0 |

    base-arm totals 72 / 75 / 74   BAND 3 files
    arm totals      73 / 73 / 74   BAND 1 file
    files that disagree with THEMSELVES across passes: base 3, arm 2

Three rows move in at least one pass. **All three are UNSTABLE; there is not one
STABLE-GAIN and not one STABLE-LOSS**, and no row is ever decided differently by
the two arms:

| row | base ×3 | arm ×3 | verdict |
|---|---|---|---|
| `sledgehammer/…/smtlib.1057395` | unknown ×3 | unsat, unknown, unsat | **UNSTABLE** — this is pass 1's "+1" |
| `simplify/javafe.parser.TokenQueue.576` | unknown, unsat, unsat | unknown ×3 | **UNSTABLE** — one of pass 2's "losses" |
| `sledgehammer/FFT/smtlib.1015458` | unknown, unsat, unknown | unknown ×3 | **UNSTABLE** — the other |

A single pass would have reported `+1` on pass 1 and `−2` on pass 2 from the same
code. **The measured result is +0**, against a base band of 3 files that a
one-pass A/B cannot see.

**The cost is real and is reported whether or not it is convenient.** The arm
scans the witness pool per bound variable per joined substitution:

| division | median base ms | median arm ms | total base s | total arm s |
|---|---:|---:|---:|---:|
| `UFNIA` | 22,928 | 22,831 | 3,205.6 | 3,182.2 |
| `UFLIA` | 20,127 | 21,329 | 2,858.4 | 2,932.0 |
| `UF` | 12,719 | 13,925 | 2,605.3 | 2,735.8 |

On `UF` the arm is **+5.0 %** of total wall. That is the mechanism behind the
instability rather than an aside: `smtlib.1015458` decides in 2,112 ms under the
base arm in one pass and spends 21,926 ms under the arm, so a scan cost of this
shape converts near-boundary decisions into timeouts — which is exactly what a
row that churns looks like.

**Target-division gain rate 0/400 after re-checking, Wilson 95 % `[0.0 %, 0.9 %]`.**

## Consequences

- **[ADR-1995]'s closing sentence is half right.** The vein is instance selection
  rather than clock — but *not* because we cannot reach the instances. We reach
  them, build them, and admit them. What is missing is downstream of
  construction, and it is not the witness choice either, since fixing that
  halves the dilution and moves no verdict.
- **The named capability the brief proposed is not the gap.** Enumerative or
  model-based instantiation over small domains would buy at most the 4 of 115
  files cvc5's own e-matching arm loses, and those four are decided by its
  `--no-e-matching` arm anyway. **Do not size a lane against it on this
  population.**
- **`2019-Preiner`'s explicit-trigger shape does not generalise, and the
  direction matters.** Across the 115 dumps, the quantifiers cvc5 actually
  instantiates carry a `:pattern` in some families and never in others:
  `vcc-havoc` 279 of 375, `spec_sharp` 199 of 224, `simplify2` 183 of 481,
  `boogie` 139 of 260 — against **0 of 1,446** for `sledgehammer`, `simplify`,
  `grasshopper`, and 0 of 38 for `2019-Preiner` and `2019-Zohar-ic`. It is a
  per-family property, not a division-level one, so a trigger-inference change
  must be evaluated per family.
- **The small-numeral hypothesis is quantified and refused**: numerals are
  **12.7 %** of distinct instantiating terms across the population; other ground
  terms are 69.2 %.
- **A future lane should look at what happens AFTER admission**, not at reach.
  On the exemplar the loop reports `ematch retried residual=true
  instantiated=false` and prints no fixpoint line at all — it is killed at a
  round head — while the final ground check is handed a set whose own code
  records the hazard (*"the full-set final check over a near-cap conjunction is
  itself a wall"*). That is the next honest target, and this ADR does not claim
  to have sized it.

## What this ADR does not establish

- `--dump-instantiations` prints what cvc5 **produced** on the run that ended
  `unsat`, not a minimised set it **needs**, so the bucket census measures a
  **superset**. A small bucket-N is therefore strong evidence and a large one is
  weak — the asymmetry is carried into every number below rather than assumed
  away.
- The three-way bucket split is reported over the 95 files (of 115) where our own
  run also produced a ground set; the other 20 get a two-way `Q` / not-`Q`
  reading, never an invented three-way one.
- **Bucket N is contaminated and the contamination is measured, not asserted.**
  cvc5 prints arithmetic as a sum of monomials — `(+ -1 (typeof S))`, `(* -1 x)` —
  where the source writes `(- (typeof S) 1)`; the same term compares unequal as
  strings. 727 of 2,544 N terms (**28.6 %**) have an arithmetic head. The bucket
  is published both ways and the classifier records the count as a field rather
  than moving terms out of N on its own judgement.
- Where the census is cleanest it is unambiguous: over the whole
  `UFNIA/2019-Preiner` family (16 files) the distinct instantiating terms are
  **Q = 32, G = 0, N = 0, S = 9**. Bucket N is *empty* on the family the
  hypothesis was drawn from.
- The cvc5 ablation is a statement about **cvc5's** e-matching, and bounds the
  question from one side only.

## Alternatives considered

- **Take [ADR-1995]'s handoff at face value and build enumerative
  instantiation.** This is what the brief's hypothesis pointed at and what a lane
  that skipped the census would have built. The reference ablation cost well
  under an hour and shows it would have been aimed at 4 files of 115, none of
  which needs it.
- **Report bucket N at face value (34.9 %) as "terms we never build".** Rejected:
  its examples are overwhelmingly arithmetic normal forms, and a number that
  large would have redirected several lanes on a printer disagreement.
- **Ship the smallest-witness lever ON because the mechanism demonstrably
  improves.** Rejected. Halving a dilution is not a verdict, the arm carries a
  linear scan of the witness pool per bound variable per joined substitution, and
  [ADR-1995] set the precedent for shipping a working mechanism OFF at zero
  yield.
- **Repair `repr_term` unconditionally rather than behind a lever.** Tempting,
  since first-inserted-and-never-repaired is hard to defend on its own terms. But
  it changes which instances every quantified query admits, and at a measured
  +0 there is no evidence to pay that risk with.

[ADR-1995]: adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md
[ADR-1957]: adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[Q2]: ../03-measurements/does-the-required-instance-enter-our-egraph-2026-09-10.md
