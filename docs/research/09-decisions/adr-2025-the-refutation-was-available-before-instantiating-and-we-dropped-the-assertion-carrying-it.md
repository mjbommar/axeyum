# ADR-2025: the refutation was available before instantiating, and we dropped the assertion carrying it

Status: accepted
Index-summary: [ADR-2020] measured that cvc5 refutes nine of our skeleton-refusal files with **zero instantiation tuples** and left the follow-up open. It is answered here, and the answer inverts the obvious hypothesis: the GROUND assertions alone are **`sat`** on 8 of the 9 (cvc5 and z3 agreeing), so "the quantifier-free part is already contradictory" is FALSE. On 9 of 9, exactly **one** assertion — always the LAST, the negated verification condition, 1 of 589 — is unsat **on its own**; cvc5 still refutes it with every quantifier module disabled AND with `--simplification=none`. Measured on the BENCHMARK rather than on cvc5: replacing every maximal quantified subformula by one opaque atom leaves a **quantifier-free skeleton that is already unsat** on 8 of 9, confirmed by two independent solvers. We *do* have this check — twice (`ground_subset_refutes_quantified_query`, and a round-0 check inside the loop) — and neither can fire, because both **DROP whole conjuncts that contain a quantifier** while the refutation lives *inside* one. Widened to the 129-row winnable population the skeleton is unsat on **15**, 11.6 % `[7.2 %, 18.3 %]` — **not** the 8/9 of the seed, which was a population selected by its outcome (R3). A new `q:bool-skeleton` rung that ABSTRACTS instead of dropping moves **+9 of 129, 0 losses, 0 flips**, every gain carrying `decided` in its route trail, **all 9 STABLE-GAIN** over three passes per arm, **0 disagreements** against `:status`/z3/cvc5 at a **full 9/9 comparable denominator** on each, against a same-arm noise floor of **0 of 129** and at **0.93x** the wall clock. **Ships ON**, so the env var inverts to a kill switch — and the shipped default is *verified* (9/9 decided with no environment variable, 9/9 reverted under the kill switch), not predicted. Of the 15, the 6 that did not convert split **4 RUNG-NEVER-REACHED / 2 CAPABILITY-LIMIT / 0 BUDGET-LIMIT**; the zero says the probe's one-tenth share is not what binds. Three instrument defects were found and fixed in flight, each of which would have published a wrong number: 499 of 589 singleton probes counted as **errors** were `sat` verdicts (cvc5 turns a correct `sat` on a subset into `(error …)` because of the benchmark's own `:status`); both mechanism columns of the first strategy isolation read `NONE` because cvc5 **refuses** `--opt=false` and wants `--no-opt`; and a 107 ms timing column was `date`/`taskset`/`grep` fork overhead against an 11 ms solve.
Index-status: accepted
Date: 2026-09-14

## Context

[ADR-2020] closed the sixth explanation for the `UFLIA`/`UFNIA` gap — the
ground checker's bounds, a lever worth 0 of 129 — and ended on a measurement
nobody had followed up. On the 22 files where our ground checker refuses:

> cvc5 refuted **21**, median **70 ms**, **nine with ZERO instantiation
> tuples — and eight of those nine are files where we flooded to the 8,192
> ground cap.**

If a refutation needs no instantiations, the work happened somewhere else.
This lane asked where, and then asked whether we ever look there.

Branch base: `git merge-base main HEAD` is
`37ff18b568f414dc21e151c3a53292c40fb7fa71`, which **is** local `main`'s HEAD.
Rules were [pre-registered](../../../bench-results/zero-inst-20260914/PREREGISTRATION.md)
in their own commit (`4e110d024`) before any lever existed.

**Not re-tested here**, and none of them is this: budget policy ([ADR-1995],
0 of 87), round ceiling ([ADR-1956], 0 of 177), instance reach ([ADR-2005],
e-matching alone gets 97 %), front-door refusal ([ADR-2000]), the round head
([ADR-2015], 1 of 209 exits), and the ground checker's bounds ([ADR-2020],
0 of 129).

## 1. What refutes those nine files

Four measurements, in the order the answers forced them. The population is
[ADR-2020]'s committed `ref/cvc5-on-our-skeleton-refusals.tsv`, so it inherits
that lane's flag-liveness argument rather than re-deriving it.

**The obvious hypothesis is false.** Splitting each file into its ground and
its quantified assertions:

| | 8 of 9 (`UFLIA/simplify2`) | the 9th (`UFNIA/vcc-havoc`) |
|---|---|---|
| ground assertions alone | **`sat`** (cvc5 and z3) | no ground assertions at all |
| quantified assertions alone | `unsat` | `unsat` |
| assertion counts | ~500 ground / exactly 90 quantified | 0 / 3 |

So the refutation does **not** live in the quantifier-free part. That single
row is also what makes every later "the ground part is sat" statement a
measurement rather than an assumption.

**One assertion of 589 carries it.** Scanning every assertion of the original
benchmarks, one at a time: on **9 of 9** exactly **one** is unsat on its own,
and it is always the **last** — the negated verification condition.

| file | assertions | singletons unsat | which |
|---|---:|---:|---:|
| `javafe.ast.AmbiguousVariableAccess.004` | 589 | 1 | 588 (last) |
| `javafe.ast.CompilationUnit.001` | 599 | 1 | 598 (last) |
| `javafe.ast.ConstructorDecl.007` | 601 | 1 | 600 (last) |
| `javafe.ast.DefaultVisitor.028` | 393 | 1 | 392 (last) |
| `javafe.ast.ForStmt.009` | 593 | 1 | 592 (last) |
| `javafe.ast.SuperObjectDesignator.008` | 589 | 1 | 588 (last) |
| `javafe.ast.ThrowStmt.004` | 589 | 1 | 588 (last) |
| `javafe.parser.test.TestLex.030` | 588 | 1 | 587 (last) |
| `havoc-bench_dlist_insert_head.12.ua_wcscpy` | 3 | 1 | 2 (last) |

**No quantifier module is responsible, and neither is the rewriter.** On that
single assertion, cvc5 still returns `unsat` under
`--no-e-matching`, `--no-finite-model-find`, `--no-cegqi`,
`--no-conjecture-gen`, `--no-full-saturate-quant`, `--no-miniscope-quant`, and
independently under `--simplification=none` and `--no-static-learning`. Each
flag was **validated individually** and shown to still produce a verdict.

**The mechanism, measured on the benchmark rather than on cvc5.** Replace
every *maximal* quantified subformula by one opaque Boolean atom — the standard
CDCL(T) abstraction. It only weakens, so `skeleton unsat ⟹ original unsat`, and
that is the only direction claimed.

| | result |
|---|---|
| skeleton `unsat` (cvc5 **and** z3) | **8 of 9** |
| skeleton `sat` | 1 of 9 — the `UFNIA/vcc-havoc` file |
| atoms abstracted per file | 105–167 |

The one `sat` is what makes the probe non-vacuous: it can return the other
answer. That file refutes by some other route and is **not** explained here.

This measures the benchmark, not a solver, so it does not depend on cvc5's
internals and is checkable by any two independent implementations.

## 2. We have this check. Twice. Neither can fire.

Searched for, then read:

- **`ground_subset_refutes_quantified_query`** (`auto.rs:162`, called at
  `auto.rs:767`) — a dedicated top-of-ladder rung, gated at ≥ 32 quantified
  conjuncts, a non-empty ground list and one tenth of the budget.
- **A round-0 check inside the loop** (`qinst_egraph.rs:2386`,
  `quantifier_qf_refutation_check`) — runs before `admit_next_source_batch`.

Both **drop** every top-level conjunct that *contains* a quantifier. Neither
**abstracts** a quantified *subformula*. On this population the refutation lives
inside one assertion, and that assertion contains quantifiers — so dropping it
throws the refutation away.

**This was measured before the code was read.** §1's first row — the ground
assertions alone are `sat` — is exactly the verdict that makes the existing
rung correctly decline. The gates are not misconfigured and the bound is not
wrong; the *granularity* is.

**`exceeds_pre_sat_skeleton_boundary` is not this**, despite the name. It is a
size admission bound inside the lazy-LIA ground solver, downstream of
instantiation, and it never returns `unsat`. It is [ADR-2020]'s largest binding
cause (22 of 78) and a different object entirely.

## 3. The transferable number is 11.6 %, not 89 %

R3 was pre-registered for this: the 8-of-9 is a rate on a population **selected
by its outcome** (cvc5 refuted it without instantiating). Widened to the whole
129-row winnable population:

| | n of 129 | `[Wilson 95 %]` |
|---|---:|---|
| **skeleton `unsat`** (cvc5 **and** z3) | **15** | 11.6 % `[7.2 %, 18.3 %]` |
| skeleton `sat` | 84 | |
| skeleton `unknown`, or one solver silent | 18 | |
| **NOT MEASURED** (`ABSTRACT-FAIL`) | **12** | 9.3 % `[5.4 %, 15.6 %]` |

Of the 117 actually measured, 15 is 12.8 % `[7.9 %, 20.1 %]`.

**The 12 are reported as NOT MEASURED, never as negatives.** Their quantifiers
live inside `define-fun` **bodies**, which the diagnostic refuses to abstract
because a fresh constant cannot track a function **parameter** — the same
unsoundness one level down. R15's liveness rule caught them: the abstractor
exits nonzero rather than handing back the original file and calling its
verdict a skeleton. The limit is the **diagnostic's**, not the solver's — inside
axeyum the parser has already expanded such definitions.

**Every one of the 15 is checked five ways, and all five agree on all 15:**

| column | result |
|---|---|
| declared `:status` | `unsat` 15/15 |
| z3 on the original | `unsat` 15/15 |
| cvc5 on the original | `unsat` 15/15 |
| shared-atom skeleton | `unsat` 15/15 |
| **fresh-per-occurrence skeleton** | `unsat` 15/15 |

The last column is a **soundness control added because the default atom map was
not unconditionally sound**: it shares one atom between occurrences with
identical *text*, and `let` can bind one name to two values in two scopes, which
would *strengthen* the skeleton and could manufacture a false `unsat`. One atom
per occurrence is unconditionally a weakening. Running it on only the 15 is
complete rather than a shortcut — the fresh map is strictly weaker, so no row
that was `sat` or `unknown` under the shared map could become `unsat` under it.

**The shipped rung does not inherit that hazard.** It abstracts over the
hash-consed arena, where one `TermId` is one formula and a *maximal* quantified
subterm has no bound variable to vary with, so sharing by identity is sound
there. The text-level control exists because the *diagnostic* works on bytes.

## 4. The lever

`q:bool-skeleton`, immediately below `q:ground-subset` in the quantified ladder:
build the query's Boolean skeleton and refute it, before any instantiation.
Only `Unsat` is propagated; every other outcome leaves the ladder in charge, and
the probe takes one tenth of the budget so it cannot starve the routes it
precedes. Atoms are minted through `declare_internal`, whose namespace is
disjoint from user symbols, so a benchmark declaring `qskel!7` cannot alias one.

Registered with `mutation_controls.py` as `solver-bool-skeleton-rung`. **Its
first run is why two things look the way they do:**

| guard | first run | after |
|---|---|---|
| the lever's polarity | killed 1 | killed 1 |
| the abstraction-liveness floor | **SURVIVED** — 6 tests, none depended on it | killed 1 |
| the maximality rule | **AMBIGUOUS ANCHOR** — matched 3 places | killed 1 |

The liveness floor survived because the whole function early-returns on the OFF
lever and a test cannot set process environment, so **no test could reach the
guard at all**. Splitting the armed body out made it reachable. The maximality
anchor was ambiguous because `if matches!(op, Op::Forall(_) | Op::Exists(_)) {`
occurs three times in `auto.rs`; the rule is now named in a binding, so there is
one place to read it and one to break it. All three now kill **exactly one**
test each.

The distinguishing fixture is a query whose top-level conjuncts are `(=> Q R)`,
`Q` and `(not R)` with `Q` quantified: the sibling drops two of three and is
left with the satisfiable `(not R)`; the skeleton keeps the structure and
refutes. **The test asserts both halves**, so if the two rungs ever stop being
distinguishable it fails rather than passing vacuously.

## 5. The A/B

Interleaved per file, **one binary, two env values**, both arms back to back on
the same pinned core with the order rotating per file. **Shard configuration
held fixed across every phase**: s5 cores `{1,3,5}` and s6 cores `{1,3,5}` —
six pinned pairs and never more, with both arms *inside* each shard so a shard
cannot move one arm relative to the other. Files go to shards **round-robin**,
not in contiguous blocks: the lists are path-sorted and a contiguous split would
confound shard with division. 24 s budget, 8 GiB `ulimit -v`.

Polarity at measurement time: **OFF was the shipped arm** (variable removed with
`env -u`, because the harness environment is inherited).

The arm is visible **by mechanism**: under `AXEYUM_TRACE=1` the route trail
names `q:bool-skeleton` with its outcome, so each row records a rung column per
arm and a silently ignored variable would read `declined` in **both**.
`ab-preflight.sh` asserts that before any measuring and fails if the rung is
absent, if both arms agree, or if the polarity is inverted:

    arm off   rung=declined  verdict=unknown   (18.7 s, bound_by=q:mbqi-quick)
    arm on    rung=decided   verdict=unsat     (266 ms)

| run | rows | OFF decided | ON decided | GAIN | LOSS | FLIP | wall |
|---|---:|---:|---:|---:|---:|---:|---|
| **main** `UFLIA`+`UFNIA` | 129 | 0 | **9** | **+9** | **0** | **0** | **0.93x** |
| **noise floor** (both arms shipped) | 129 | 0 | 0 | **0** | 0 | 0 | 1.00x |
| control `QF_BV` | 6 | 0 | 0 | 0 | 0 | 0 | 1.00x |
| control `AUFLIA` | 30 | 15 | 15 | 0 | 0 | 0 | 1.01x |

Gain 9 of 129, Wilson 95 % `[3.7 %, 12.7 %]`. **All nine carry `rung=decided`
in the on arm**, so each is attributable to this rung rather than to timing; the
summarizer labels a gain whose rung did not fire `UNEXPLAINED` and names it,
and there are none.

**R5 — three passes per arm on every moved row: 9 of 9 STABLE-GAIN**, the same
verdict in all three passes, zero UNSTABLE and zero FLIP. [ADR-2005] got
+1 / −2 / +0 from three passes of identical code, so one pass would not have
been evidence.

**R9 — the nine new verdicts against three independent authorities:
0 disagreements, at a comparable denominator of 9/9 on each** of `:status`, z3
and cvc5. Printed beside the zero per [ADR-1957] — no authority abstained, so
the zero is nine agreements rather than nine no-opinions.

**The noise floor settles the frame**: at byte-identical configuration the same
division moves **0 of 129**, `[0.0 %, 2.9 %]`. [ADR-2020] measured 1 of 129 on
this division, so this is if anything the tighter frame. The effect is 9; the
band built to detect it is 0.

**The noise-floor runner is written out in full rather than derived by
substitution**, because the first attempt to derive it by `sed` silently failed
to substitute one of the two branches — which would have produced a second copy
of the real A/B still labelled a noise floor. `ab-verify-noise.sh` guards
against that and is **mutation-verified**: arming one branch makes it exit 1,
and the restore is confirmed byte-identical with `diff` before the checker is
trusted again.

**The controls, and which of them carries weight.** `QF_BV` moves 0 but the rung
is **ABSENT** on all 6 — quantifier-free queries never enter the quantified
ladder, so "it did not move" is guaranteed rather than measured, and it is a
**weak** control. `AUFLIA` is the real one: the rung **ran** on all 30 and
**fired** on one — `smt1220699141798901390.smt2`, returning `unsat` at 107 ms
where the off arm returned `unsat` at 110 ms by a different route. In the
control division the rung is demonstrably live, demonstrably capable of
deciding, and changes nothing it should not.

**Measurement condition, stated because it is not ideal.** A concurrent lane
held s5 `{1,3}` and s6 `{1,3}` throughout — four of the six pairs. The
interleaved design is what protects the comparison: both arms of a file run back
to back on the *same* core, so contention hits them equally. The noise floor was
run on the identical shard configuration for exactly this reason, so it measures
the variance actually present rather than a cleaner one.

## 6. Decision

**Ship the rung ON.** R4's go/no-go was ≥ 6 rows net, all STABLE-GAIN; it is
**9**, all STABLE-GAIN, with zero losses, zero flips, zero authority
disagreement, and a wall clock of 0.93x.

**The polarity therefore INVERTS at this commit.** The rung was off unless
`AXEYUM_ZERO_INST_SKELETON=1`; it now runs unless
`AXEYUM_ZERO_INST_SKELETON=0`, and the variable is a **kill switch**. Anyone
reusing `ab-run.sh` on a later binary without noticing would measure the shipped
arm in both halves and report the zero as a null, so the inversion is stated in
the gate's doc comment, in the runner's header, and here. The polarity test is
inverted with it and renamed
(`the_bool_skeleton_lever_is_on_unless_killed_exactly`), so a change back to
opt-in cannot land silently — it would have to edit that test, in that
direction, on purpose.

**R12 — the shipped default is verified, not predicted.** The A/B's ON arm was
produced by an environment variable; the shipped build produces it by default,
and those are different things until somebody checks. A fresh release binary,
run with **no environment variable at all**:

- **9/9** decided `unsat`, each with `q:bool-skeleton` `decided` in its trail;
- **9/9** back to undecided under `AXEYUM_ZERO_INST_SKELETON=0`.

The second line is what makes the first a measurement: had the kill switch also
decided them, the default would prove nothing, and the checker fails such a row
as `VACUOUS`.

**Predicted post-merge value: the `UFLIA`/`UFNIA` division totals move by +9
relative to `main`, and no other division moves.** The reason is that the rung
returns `Ok(false)` for every query with no quantifier to abstract, and the
`AUFLIA` control shows it firing outside the target population without changing
a verdict.

## 7. Why only 9 of the 15, and where the next lane should look

| | n | what it means |
|---|---:|---|
| **CONVERTED** | **9** | |
| **RUNG-NEVER-REACHED** | **4** | the trail stops at `fd:parse`; the ladder never reaches this rung. All `UFNIA`. Not this rung's to fix. |
| **CAPABILITY-LIMIT** | **2** | the rung **runs** and declines at both the 24 s budget and 5x it — our ground checker cannot refute a skeleton that cvc5 *and* z3 both refute |
| **BUDGET-LIMIT** | **0** | |

**The zero is the useful negative**: the probe's one-tenth share is not what
binds, so raising it buys nothing — the same shape [ADR-2020] measured for the
pre-SAT envelope, and a lever the next lane need not build.

The two remaining axes, in the order this lane would take them:

1. **RUNG-NEVER-REACHED (4).** These never reach the quantified ladder at all.
   That is a dispatch question, not an instantiation one, and no ADR in the
   `UFLIA`/`UFNIA` series has looked at it.
2. **CAPABILITY-LIMIT (2).** A quantifier-free `UFLIA`/`UFNIA` query that two
   independent solvers refute and we cannot. This is the cleanest possible
   statement of the ground-checker gap — no quantifiers, no instantiation, no
   admission bound — and it is the same component [ADR-2020] left open.

## 8. Three instruments lied, and each would have published a wrong number

Recorded because the finding survived all three only by being re-measured.

- **499 of 589 singleton probes were counted as `errors`. They were `sat`
  verdicts.** These benchmarks carry `(set-info :status unsat)`, and cvc5 turns
  a correct `sat` on a *subset* into `(error "Expected result unsat but got
  sat")` with a nonzero exit. The benchmark's own metadata is about the whole
  file and is meaningless for a subset; `set-info` is now dropped, and the
  re-run is `errors=0` with the finding unchanged.
- **Both mechanism columns of the first strategy isolation read `NONE`.** cvc5
  **refuses** the `--opt=false` form (`can't understand option`) and wants
  `--no-opt`. Every flag is now validated individually. This one *refused*
  rather than being ignored, which is the better failure — an ignored flag
  prints the same verdict and is invisible.
- **A 107 ms timing column was fork overhead.** Identical on every row,
  including a 3-assertion file, because it measured `date`/`taskset`/`grep`
  around an **11 ms** solve.

## 9. The rules that were pre-registered, against what happened

| rule | pre-registered | outcome |
|---|---|---|
| R1 | split any string covering several sites before censusing | no give-up string was censused; the population came from [ADR-2020]'s committed TSV. **Not exercised** |
| R2 | publish every cause with its denominator, zeros included | §3 and §7, including the 12 NOT MEASURED and the 0 BUDGET-LIMIT |
| R3 | no conversion RATE pre-registered | the 8/9 is explicitly **not** transferred; the measured 15/129 is used instead |
| R4 | ship only if ≥ 6 rows move net, all STABLE-GAIN | **9**, all STABLE-GAIN → **ships ON** |
| R5 | 3x per arm on every moved row | 9 of 9 STABLE-GAIN, 0 UNSTABLE, 0 FLIP |
| R6 | noise floor, whole division, same arm | **0 of 129** at fixed code |
| R7 | interleaved, one binary, two env values, polarity stated | done; polarity in the runner header, and its post-ship inversion stated in §6 |
| R8 | control division that must not move, shown non-vacuous | two: `QF_BV` 0 (weak — rung absent, said so) and `AUFLIA` 0 with the rung **firing** on one row |
| R9 | new verdicts vs three authorities, denominators separate | 0 disagreements at 9/9 comparable on each |
| R10 | this lever can only add `unsat`, so control the **unsat** half; one disagreement is a P0 | 0 disagreements; the soundness-negative test refutes nothing on a satisfiable skeleton |
| R11 | Wilson for every small-n proportion | every ratio here |
| R12 | the A/B measures THIS BRANCH | it does, and the shipped default is separately **verified** rather than predicted |
| R13 | freshness licensed by `find -newer`, not exit status | both builds passed it; neither was stale |
| R14 | unfinished checks reported as "did not run" | §10 |
| R15 | the abstraction's own liveness is a measured column | it **fired**: 12 of 129 exited `ABSTRACT-FAIL` and are reported NOT MEASURED |

**The pre-registered prediction was 4 to 12 rows, deliberately straddling R4's
threshold of 6 so the rule would decide rather than the author. The measured
value is 9 — inside the range, above the threshold.** The secondary prediction,
that a skeleton refutation would cost tens of milliseconds and leave the arms'
wall clocks indistinguishable, was **wrong in a favourable direction**: the rung
fires in 0.7–2.1 s (not tens of ms) and the ON arm is **faster overall**
(0.93x), because deciding a file in 2 s replaces a 24 s timeout.

### Not measured here, and reported as "did not run"

- **R1 was not exercised.** No give-up string was censused by this lane.
- The **`UNSPLIT` bucket** [ADR-2020] left (`no model within the bounded integer
  width 32`, 5 of 78, two emit sites) is **still unsplit**; this lane did not
  touch it.
- **The 12 `ABSTRACT-FAIL` files were never measured for skeleton
  satisfiability.** They are excluded from the 15, not counted against it.
- The **one `UFNIA/vcc-havoc` file with a `sat` skeleton** that cvc5 still
  refutes with zero instantiations is **unexplained**. Some mechanism other than
  Boolean abstraction refutes it, and this lane did not find out which.
- **A per-round cap on the lazy function-consistency lemma batch**, which
  [ADR-2020] named as the lever it would pick up next, was **not built**.

[ADR-1956]: adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md
[ADR-1957]: adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-1976]: adr-1976-qf-nia-is-model-bound-adr-1937-took-the-sat-half-and-the-eager-split-is-worth-four.md
[ADR-1980]: adr-1980-the-cheap-check-was-the-whole-target-a-dispatch-decline-not-a-datatype-capability.md
[ADR-1995]: adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md
[ADR-2000]: adr-2000-the-front-door-refusal-was-not-the-binding-constraint.md
[ADR-2005]: adr-2005-the-instances-are-e-matchable-and-we-already-build-them.md
[ADR-2010]: adr-2010-the-sat-side-replay-cannot-see-the-parser.md
[ADR-2015]: adr-2015-the-round-head-is-a-symptom-the-ground-checker-is-the-wall.md
[ADR-2020]: adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
