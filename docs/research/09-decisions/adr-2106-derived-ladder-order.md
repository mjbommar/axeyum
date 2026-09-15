# ADR-2106: the ladder order is a table, the ledger's own order loses, and the plan's key does not say whose elapsed

Status: proposed
Index-summary: Phase 4 of the dispatch-and-instrumentation plan runs a feature class's ladder order off ADR-2102's ledger. **SIZING FIRST, and both nominated classes came back under five files.** `QF_NIA`/`Int`: 115 undecided of 199, raw ceiling 47, **REFINED 3** — 42 of the 47 declined with `estimated 130191180 CNF clauses before lowering exceeds budget 64000000`, a CNF-SIZE refusal that renders through the same `DeclineReason::Budget` word as a clock expiry (ADR-2060's defect in miniature, and only the DETAIL text separates them), and 2 more are a bounded-width refusal; more clock buys none of them. `UFNIA`/`Int`+`Function`: **0 of 6, and its 126,764 ms of "prefix cost" is not a prefix at all** — `q:skolem-qf` records a PROBE, hands off to `check_auto` (the whole quantifier-free ladder), and records its decision when that returns, so the hand-off lands between the two entries and gets counted as time above the decider; it appears TWICE on all 24 trails and the clock before its first entry is **0 ms on every one of them**, 89.8 % of the 126,764 ms being `uf-arith-online` inside the hand-off. That refutes the second of the two classes Phase 4 was conditioned on, and no `UFNIA` order ships. What shipped is the MECHANISM: `dispatch_nonlinear_int_tail`'s six rungs move behind `int_tail_order::IntTailRoute` so the order is data (`HAND`/`DERIVED`) and `AXEYUM_LADDER_ORDER` gives an interleaved A/B both arms out of ONE binary — strictly better evidence than two builds, which differ by a compiler invocation as well as by the change. Two things made `hand` a real control: `int-blast-ladder`'s `Unknown` is RETAINED as the fallback rather than promoted to a mid-ladder verdict or replaced by a manufactured one, and each deadline check is attached to the rung it FOLLOWED rather than to a position. **`SHIPPED` points at `HAND`, and the reason is measured three times over.** Phase 4's key is "(decision rate, then median elapsed)"; it does not say WHOSE elapsed, and `int-blast-ladder` wins in a **339 ms** median and LOSES in a **12,566 ms** median (p90 14,297, max 23,189 against a 24,000 ms budget) on 112 of its 177 attempts — at the HEAD that is paid out of every rung below it, on exactly the population that still needs one. Five committed `hypothesis_min::tests` capability fixtures go red under `derived` at their own 2 s budget and all ten pass under `hand`; a fixture is not weakened to let a lever ship. Interleaved one-binary A/B, 24 s / 8 GiB, 12 pinned core pairs across s5/s6/s7, divisions serial per shard: **pinned 400 rows, A 137 / B 129, net −8, 3 gains, 11 losses, 0 flips, 0 exit-status differences, 92 `:status` comparisons with 0 disagreements, 0 malformed**; all 14 movers re-run 3× per arm: **11 STABLE-LOSS, 1 STABLE-GAIN, 2 BOTH-DECIDE, 0 UNSTABLE** — every raw loss survived and two of the three raw gains were ambient. The HELD-OUT draw (200 fresh files per division, seeded, excluding every pinned path and every path any committed ledger row carries; pools of 25,243 and 13,264) agrees and is WORSE -- 400 rows, A 135 / B 124, net -11, 4 gains, 15 losses, 0 flips, 0 exit-status differences, 90 `:status` comparisons with 0 disagreements -- and its 19 movers re-checked 3x per arm give **14 STABLE-LOSS and ZERO STABLE-GAIN**, so the loss is not an artifact of measuring on the training set. And the trade is real in the other direction and is reported rather than buried: on the 75 `QF_NIA` rows BOTH arms decide the derived order costs **129.0 s against 767.9 s**, a 638.9 s saving with the median falling from 10,918 ms to 407 ms — **27× faster on what it decides, five net files worse at deciding**. Mutation: two mutations, each killing EXACTLY ONE named fixture from a 5-test baseline, and the fixture had to move out of `bench-results/` because `mutation_controls.py` excludes that directory from the tree it copies — an `include_str!` from there makes every mutation report `BASELINE DID NOT BUILD`, which is not a result.
Index-status: proposed
Date: 2026-09-15

## Context

[ADR-2102] built the outcome ledger. Lane LEDGER-STRUCTURE filled it over all
seven Tier 1 pinned 200-file lists and asked the one question
[Phase 4][plan] is conditioned on:

> Runs only if Phase 3's ledger shows structure. Specifically: if, for some
> feature class, one route decides a large majority of what gets decided and a
> different route is tried first, then ladder order for that class should come
> from the table.

It found STRUCTURE on 5 of 12 (division, feature class) groups and ranked two
of them far above the rest by `prefix_cost_ms`:

1. `QF_NIA` / `Int` — `int-blast-ladder` decides 65 of 84, **631,307 ms** over
   65 files;
2. `UFNIA` / `Int|Function` — `q:skolem-qf` decides 24 of 24, **126,764 ms**
   over 24 files.

This ADR is Phase 4 on those two.

## Part A — sizing first, and both classes are under five files

**The numbers up front, because the exit criterion asks for them there: 3 and
0, against denominators of 115 and 6.**

Both ledger figures are in TIME on files that **already decide**. Reordering
makes them decide sooner; it cannot make them decide. The gain, if there is
one, is on rows that do NOT decide today and would if the deciding route got
the clock the routes above it are spending. So the ceiling in FILES is, per
class, the undecided rows where the class's top decider was never reached or
got less than its median winning clock.

| class | undecided rows | raw ceiling | **refined** | reorderable prefix |
|---|---:|---:|---:|---:|
| `QF_NIA` / `Int` | 115 of 199 | 47 | **3** | 628,792 ms / 65 files |
| `UFNIA` / `Int\|Function` | 6 of 30 | 0 | **0** | **0 ms** |

Two corrections got there, and each moved a headline number.

### A1 — 42 of the 47 candidates are a SIZE ceiling wearing the word `budget`

The raw test is necessary and not sufficient. A route can fail for the clock —
and a reorder is exactly the fix — or for anything else, and a reorder fixes
nothing. Splitting the 47 by `int-blast-ladder`'s own recorded decline
(`decline_reasons` / `decline_details` / [ADR-2104]'s `decline_names`):

| bucket | rows | can a reorder help? |
|---|---:|---|
| CAPACITY — `estimated 130191180 CNF clauses before lowering exceeds budget 64000000` | 42 | no |
| FRAGMENT — `integer constant 4294967295 does not fit the bounded width 32` | 2 | no |
| no recorded decline at all, decider NEVER reached | 3 | **yes** |

This is [ADR-2060]'s defect in miniature: `DeclineReason` renders a CNF-size
refusal and a clock expiry with the same word. Only the detail text separates
them, which is why the checker matches on the detail and not on the reason.

### A2 — `UFNIA`'s 126,764 ms is not a prefix

`q:skolem-qf` records a **probe**, calls `check_auto` — the entire
quantifier-free ladder — and records its decision when that returns
(`auto.rs::solve_inner`). A `prefix_cost` defined as "everything before the
`decided` occurrence" therefore counts the whole hand-off as time spent
*above* the decider.

| | before its FIRST trail entry (reorderable) | between that entry and its decision (its OWN work) |
|---|---:|---:|
| `UFNIA` / `Int\|Function` | **0 ms**, all 24 files | 126,764 ms |
| `QF_NIA` / `Int` | 631,307 ms | 0 ms |

`q:skolem-qf` appears twice on all 24 trails; `int-blast-ladder` appears twice
on none of its 65. So `QF_NIA`'s figure survives unchanged and `UFNIA`'s goes
to zero. The 126,764 ms is real work and 89.8 % of it is `uf-arith-online`
(113,777 ms) — a **quantifier-free** route inside the hand-off, so it is a
finding about the QF ladder on `Int|Function` queries, not about the quantified
ladder's head, which is what a `UFNIA` reorder would move.

**`UFNIA` / `Int|Function` therefore ships nothing.** Its ceiling in files is
0 and its reorderable clock is 0 ms. Its derived order also is not a
permutation of independent rungs but a hoist of the skolemization step that
**mutates the assertion list** the rungs above read — a restructure of
`solve_inner`'s head, which [Phase 4][plan]'s own non-goals exclude ("not a
rewrite of `auto.rs`").

**So: both classes are a TIME SAVING, not a gain, and this ADR says so rather
than implying otherwise.** They are measured anyway, which is the rest of it.

## Part B — the mechanism: order as a table, both arms from one binary

`dispatch_nonlinear_int_tail`'s six rungs move behind
`int_tail_order::IntTailRoute`. The rung bodies are verbatim the inlined
originals; what changes is that the ORDER is data
(`int_tail_order::HAND`, `int_tail_order::DERIVED`) and `AXEYUM_LADDER_ORDER`
selects. Unset, and any value nobody recognises, is `int_tail_order::SHIPPED` —
a typo must never select an arm nobody chose.

One binary is **better** evidence than two builds, not a shortcut: with two
builds the arms differ by a compiler invocation as well as by the change, and
the runner can only hash-check that they differ at all. It also removes the
failure mode the two-build runners guard against (the same binary in both
arms) and replaces it with one that can actually happen here — the same env
value in both arms — which `ab-run-lever.sh` refuses.

Two things the reorder had to get right, or `hand` is not a control arm:

- **`int-blast-ladder` is the hand order's TAIL**, so its result is returned
  whatever it is and its `Unknown` is the tail's answer. Off the bottom that
  `Unknown` must not become a verdict from the middle of the ladder, and must
  not be dropped for a manufactured one that says strictly less ([ADR-2100]
  classified its own two tails on exactly this reasoning). It is RETAINED as
  the fallback and returned only when every rung has run.
- **Each deadline check is attached to the rung it FOLLOWED**, not to a
  position. Under `HAND` the three checks land where they landed carrying the
  strings they carried; under a reorder the message keeps naming the work that
  just happened, rather than becoming an [ADR-2060]-shaped lie.

One inherited oddity is recorded and left: the message after `cas-ideal-refuter`
names the *bounded integer blast*, the rung before it. Correcting the string
would move bytes in a control arm whose whole job is to be byte-identical.

## Part C — the derived order, and why it is not the shipped one

`derive.py` reads `outcome_ledger.load()` only, is deterministic (re-run, the
TSV is byte-identical; the key carries the route NAME as its final tiebreak, so
it is a total order), and prints the numbers beside every route.

| # | hand order | derived order | decides | rate | median WIN |
|---|---|---|---:|---:|---:|
| 0 | `nia-square` | **`int-blast-ladder`** | 65/177 | 0.367 | 339 ms |
| 1 | `int-real-relax` | **`nia-linearize`** | 19/198 | 0.096 | 788 ms |
| 2 | `nia-linearize` | **`cas-ideal-refuter`** | 0/115 | 0.000 | — |
| 3 | `nia-bounded-blast` | `nia-bounded-blast` | 0/179 | 0.000 | — |
| 4 | `cas-ideal-refuter` | **`nia-square`** | 0/199 | 0.000 | — |
| 5 | `int-blast-ladder` | **`int-real-relax`** | 0/198 | 0.000 | — |

**The key is under-specified.** "(decision rate, then median elapsed)" does not
say *whose* elapsed, and on this class the two readings are not close:

| rung | wins | losses | median WIN | median LOSS | p90 LOSS | max LOSS |
|---|---:|---:|---:|---:|---:|---:|
| `nia-square` | 0 | 199 | — | 0 ms | 0 ms | 0 ms |
| `int-real-relax` | 0 | 198 | — | 4,020 ms | 4,195 ms | 9,573 ms |
| `nia-linearize` | 19 | 179 | 788 ms | 6,680 ms | 6,959 ms | 8,004 ms |
| `nia-bounded-blast` | 0 | 179 | — | 0 ms | 8 ms | 984 ms |
| `cas-ideal-refuter` | 0 | 115 | — | 0 ms | 1 ms | 13 ms |
| `int-blast-ladder` | 65 | 112 | **339 ms** | **12,566 ms** | 14,297 ms | 23,189 ms |

The derived order promotes `int-blast-ladder` from the ladder's TAIL to its
HEAD on a 339 ms median WINNING clock. On the 112 attempts of 177 where it does
not decide it costs 12,566 ms median and 23,189 ms at worst against a 24,000 ms
budget — and at the head that is paid out of every rung below it, on exactly
the population that still needs one. **Its position at the tail is not an
oversight; it is what makes it the rung that soaks up the remainder.**

That is not a prediction. Five committed capability fixtures go red under
`AXEYUM_LADDER_ORDER=derived` at their own 2 s budget —
`closes_the_route_b_l3_lemma_from_the_full_hypothesis_set`,
`finds_the_minimal_sufficient_subset`, `minimisation_is_deterministic`,
`reported_indices_are_ascending_unique_and_in_range`,
`reported_subset_independently_refutes_the_goal` — because the minimiser's
small nonlinear-integer subsets stop being refuted once `nia-linearize` and
`int-real-relax` lose the clock. All ten `hypothesis_min` tests pass under
`hand`. **A fixture is not weakened to let a lever ship.**

`DERIVED` is retained exactly as derived, as the A/B's treatment arm and as the
record of what the key yields.

## Part D — the measurement

Interleaved one-binary A/B, both arms back to back on the same file on the same
pinned core with arm order alternating per file, 24 s wall / 8 GiB `ulimit -v`,
12 pinned PHYSICAL core pairs across s5/s6/s7, **divisions serial per shard**
([ADR-2103] measured 9× oversubscription collapsing both columns toward
`unknown`, and a wash of `unknown` reads exactly like no movement).

### Pinned draw — the files the order was derived from

| division | rows | A | B | net | gain | LOSS | FLIP | rc≠ | cmp | DIS |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| QF_NIA | 200 | 83 | 78 | −5 | 3 | 8 | 0 | 0 | 78 | 0 |
| UFNIA | 200 | 54 | 51 | −3 | 0 | 3 | 0 | 0 | 14 | 0 |
| **TOTAL** | **400** | **137** | **129** | **−8** | **3** | **11** | **0** | **0** | **92** | **0** |

0 malformed rows. All 14 movers re-run **3× per arm**:
**11 STABLE-LOSS, 1 STABLE-GAIN, 2 BOTH-DECIDE, 0 UNSTABLE.** Every raw loss
survived; two of the three raw gains were ambient, which is why the raw column
is not the finding.

`UFNIA` loses three despite its own class shipping nothing, and the mechanism
is A2's: a quantified `UFNIA` file reaches `dispatch_nonlinear_int_tail`
*inside* `q:skolem-qf`'s hand-off, so a lever on the quantifier-free integer
tail moves quantified divisions too. A lane reading only the class's own
division would have missed all three.

### Held-out draw — 200 fresh files per division

Drawn by `draw-heldout.py` with the seed as a source constant (not a
command-line default, so it cannot be re-rolled after a result), from
`/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/<DIV>/`,
excluding every path in the pinned list **and** every `corpus_path` any
committed row in `bench-results/ledger/` carries for that division. Pools of
25,243 (`QF_NIA`) and 13,264 (`UFNIA`); the exclusion is checked rather than
assumed and the script aborts if an excluded path leaks into the pool. The
drawn lists are committed.

| division | rows | A | B | net | gain | LOSS | FLIP | rc≠ | cmp | DIS |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| QF_NIA | 200 | 84 | 79 | −5 | 4 | 9 | 0 | 0 | 79 | 0 |
| UFNIA | 200 | 51 | 45 | −6 | 0 | 6 | 0 | 0 | 11 | 0 |
| **TOTAL** | **400** | **135** | **124** | **−11** | **4** | **15** | **0** | **0** | **90** | **0** |

0 malformed rows. All 19 movers re-run **3× per arm**:
**14 STABLE-LOSS, 0 STABLE-GAIN, 4 BOTH-DECIDE, 1 UNSTABLE.**

**The held-out draw agrees with the pinned one and is worse**, so the loss is
not an artifact of measuring on the training set — which is exactly what
[Phase 4][plan]'s §7 risk ("Phase 4 optimises the sample") asked this draw to
rule out. On the fresh files the derived order has fourteen stable losses and
**not one** stable gain.

### The trade, in the other direction

Reported separately, because a time saving does not license a loss and a
combined score would let one pay for the other. On the rows BOTH arms decide:

| division | both | A total | B total | saved | A median | B median | B faster | B slower |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| QF_NIA | 75 | 767.9 s | 129.0 s | **+638.9 s** | 10,918 ms | **407 ms** | 71 | 1 |
| UFNIA | 51 | 137.5 s | 162.6 s | −25.0 s | 208 ms | 209 ms | 6 | 12 |

**27× faster on `QF_NIA` files it decides, five net files worse at deciding.**
That is the honest shape of the result, and it is why the mechanism ships and
the order does not: the lever is now one env value away for anyone measuring a
budget where 12.5 s of losing clock at the head is affordable and 10.9 s of
median latency is not.

## Part E — the guards, and the trap the mutation control found

Five tests, and the guard population is deliberately not one shared check —
six of seven guards in one suite here were once removable because they all
rejected through one:

| test | what it pins | order-blind? |
|---|---|---|
| `derived_order_matches_the_committed_ledger_derivation` | `DERIVED` against the committed TSV, read with `include_str!` | no — the only one |
| `every_order_runs_every_rung_exactly_once` | both arrays are permutations (what makes the fallback branch unreachable) | yes, sorts |
| `ladder_order_lever_spelling` | the env policy, without touching process environment, with a positive control that the arms differ | yes |
| `hand_order_deadline_checks_are_where_they_were` | the control arm's three strings and their positions | n/a |
| `int_tail_labels_are_the_committed_trail_vocabulary` | the trail labels every committed ledger sweep reads, plus `from_wire`'s positive control | yes |

`scripts/tests/mutation_controls.py`'s `derived-ladder-order` suite, baseline 5
tests:

| mutation | outcome |
|---|---|
| swap the derived order's first two rungs | **killed 1**: `derived_order_matches_the_committed_ledger_derivation` |
| move a deadline string off the rung it followed | **killed 1**: `hand_order_deadline_checks_are_where_they_were` |

**The trap, worth more than the mutations.** The first run came back `BASELINE
DID NOT BUILD` — not a result, and precisely the outcome class that harness was
rewritten to stop counting as coverage. `mutation_controls.py` EXCLUDES
`bench-results` from the tree it copies (206 MB; the exclusion carries its own
comment, and the same trap already cost a whole suite once when `corpus` was
excluded), so a fixture `include_str!`ed from a lane's `bench-results/`
directory makes **every** mutation on that file unmeasurable. The derivation's
committed home is therefore
`docs/plan/fixtures/derived-ladder-order-20260915.tsv` — ONE file, not a copy,
because a second copy beside the evidence is a thing that drifts from the
derivation it claims to be. The reason is recorded at the `include_str!`, in
`derive.py`'s usage block and in the lane README.

## Decision

1. **Ship the mechanism.** `dispatch_nonlinear_int_tail`'s order is a table,
   `AXEYUM_LADDER_ORDER` selects, and `SHIPPED` is one named constant so the
   ship decision is one edit.
2. **Do not ship the derived order.** `SHIPPED` points at `HAND`. The ship
   criterion is 0 stable losses on BOTH draws; it is 11 against 1 stable gain
   on the pinned draw and **14 against 0** on the held-out one, plus five
   capability fixtures red at a 2 s budget. `DERIVED` stays, exactly as
   derived, as the treatment arm and the record of what the key yields.
3. **Ship nothing for `UFNIA` / `Int|Function`.** Ceiling 0 files, reorderable
   clock 0 ms, and the "reorder" is a restructure.
4. **Record that Phase 4's ordering key is under-specified.** "(decision rate,
   then median elapsed)" needs to say *whose* elapsed. At a ladder POSITION
   what you pay is the losing clock, and on this class the winning and losing
   medians differ by 37×. A later lane deriving an order from this ledger
   should read `cost-when-declining.py` before its key.

## What this ADR does not claim

- **Not that the ladder's hand order is optimal.** It says the ledger's order
  by this key is worse, on this corpus, at this budget. `int-real-relax`
  deciding 0 of 198 on `QF_NIA`/`Int` while costing 753,694 ms remains an
  open, separately measurable question — and moving it is a smaller change
  than moving the tail.
- **Not that the derived order is bad at every budget.** Its losses are
  budget-shaped: at 24 s it loses 11 and saves 638.9 s; at the capability
  suite's 2 s it loses five fixtures. A table that cannot express
  budget-dependence is the limitation, and this ADR does not pretend
  otherwise.
- **Not a portfolio widening.** The ledger's portfolio criterion found 2 pairs
  over 5 of 634 undecided rows. That is noise at this sample size and was left
  alone.

[plan]: ../../plan/dispatch-and-instrumentation-2026-09-15.md#5-phase-4--derived-ladder-policy-conditional
[ADR-2060]: adr-2060-the-give-up-variant-could-not-tell-six-gates-apart-and-nothing-asked-it-to.md
[ADR-2100]: adr-2100-typed-route-ownership.md
[ADR-2102]: adr-2102-the-outcome-ledger.md
[ADR-2103]: adr-2103-quantified-ladder-ownership-and-bounded-continuation.md
[ADR-2104]: adr-2104-typed-decline-detail.md
