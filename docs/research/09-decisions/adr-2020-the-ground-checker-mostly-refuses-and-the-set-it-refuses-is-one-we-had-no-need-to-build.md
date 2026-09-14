# ADR-2020: the ground checker mostly REFUSES, and the set it refuses is one we had no need to build

Status: accepted
Index-summary: [ADR-2015] left 78 held-set replays in which our own ground checker declines our own instantiated conjunction, and asked for them to be split before anyone sized the work. **Censusing them needed a string split first, and this lane walked into the trap before catching it**: the record separator in the committed census is `;QPROBE`, not a bare `;`, because the `why=` detail contains `;` -- and a `why=` may WRAP another reason or APPEND one after a stats parenthetical. The outer census has **5** buckets, the binding census **10**, **46 of the 78** had their cause behind a wrapper, the 25-row largest outer bucket is **four** causes, and the leader changes: it is the **lazy LIA pre-SAT skeleton boundary at 22 of 78** (28.2 %, Wilson `[19.4 %, 39.0 %]`), not the eager Ackermann bound (17) the prose led with. The 78/40 is a REPLAY split; at ROW level it is **58 unknown-only / 31 sat-only / 6 MIXED and genuinely not separable** of 127. Structurally, **55 of 78 = 70.5 % `[59.6 %, 79.5 %]` are CHEAP REFUSALS by an admission bound** (wall median 1,407 ms of a 10,000 ms budget), not exhausted clocks, and the two split by division (`UFLIA` refuses 40:5, `UFNIA` exhausts 18:15). The bounds, read rather than assumed: **`64` is not a unit error** but was never calibrated against the expansion -- it is a proxy for an unbounded downstream solve, fitted between 40 and 117 pairs in 2026-06 and unchanged since -- and **the same constant is a route selector at `auto.rs:4068` and a hard decline at `combined.rs:86`, with 17 of 17 of our replays at the hard-decline site that has no lazy fallback**. The skeleton envelope is a MEMORY bound whose own re-derivation measured peak RSS at **71 MiB, 1/115th of the ceiling it cites**, and wrote "above this, nobody has measured"; it refuses at 1.4x that point. Ten seconds on **11** ground terms is **20,626 LIA calls, 18,678 LP relaxations, 9,035 simplex solves and 11.4 M cloned arena nodes** (27 % CDCL, 22 % allocator, 16 % simplex/Gomory by `perf`), because the width ladder clones the WHOLE file's DAG per rung. An env-gated A/B raising the envelope 4x moves **0 of 129**, Wilson `[0.0 %, 2.9 %]`, at 1.00x wall -- with the null shown NON-VACUOUS (the OFF arm crosses both pre-SAT bounds on a measured file in the shipped path and the ON arm crosses neither) and the refusal measured converting into a TIMEOUT, exactly as pre-registered. The **same-arm noise floor moves 1 of 129**, so the lever's effect is smaller than the band built to detect it. **Ships OFF.** The redirect: the reference refutes 21 of those same 22 files at a median **70 ms**, **nine without instantiating a single quantifier**, and **eight of those nine are files where we flooded to the 8,192 admission cap** -- so the undecidable conjunction is an artifact of over-instantiation and the open axis is **selection**, which none of the five closed hypotheses covers.
Index-status: accepted
Date: 2026-09-14

## Context

[ADR-2015] closed the last loop-side hypothesis for the `UFLIA`/`UFNIA` gap and
handed over one measured observation: of the 122 held-set replays it ran,
**78 are our own ground checker declining our own instantiated conjunction**.
It listed some of the reasons and stated explicitly that whoever sized the work
must split the `sat` replays from the `unknown` ones first, *"which is the same
mistake this ADR's first section is about, one layer down."*

This lane sized it. Branch base: `git merge-base main HEAD` is
`4436e9cd5c912c590fa5a2dbfa4c73b8065b3623`, which **was** local `main`'s HEAD
when this lane branched.

Rules were [pre-registered](../../../bench-results/ground-decide-20260914/PREREGISTRATION.md)
in their own commit (`bdcffb3d0`) before any lever existed, including the
prediction that a bound-raising lever would ship OFF.

## 1. The split, at both levels — and they are different numbers

The 78/40 is a **replay-level** split. Rows are not replays: the probe fires at
every loop exit, so one file contributes several. Both levels are reported
because only one of them answers "how many FILES could a better ground checker
move", and it is not the one [ADR-2015] published.

Denominator: the **127 still-failing rows** ([ADR-2015]'s 129 winnable minus the
2 it drops as sometimes-decided). Method is re-analysis of the committed census
in `bench-results/round-head-20260914/census/`, so it is **observational, not an
experiment**, and reproduces [ADR-2015]'s counts exactly
(122 replays / 99 rows / 78-40-2-2) before departing from them.

| level | split |
|---|---|
| **replay** (122) | `unknown` 78, `sat` 40, `unsat` 2, `error` 2 |

| row-level class | rows | of 127 |
|---|---:|---|
| `unknown`-only — **our checker declined** | **58** | 45.7 % `[37.3 %, 54.3 %]` |
| `sat`-only — instantiation genuinely insufficient | 31 | 24.4 % `[17.8 %, 32.6 %]` |
| **MIXED `sat`+`unknown` — not separable** | **6** | 4.7 % `[2.2 %, 9.9 %]` |
| refutes on a fresh clock | 2 | 1.6 % `[0.4 %, 5.6 %]` |
| `error`-only | 2 | 1.6 % `[0.4 %, 5.6 %]` |
| never reached a replay | 28 | — |

**The 6 MIXED rows are reported as MIXED rather than assigned.** On those files
one exit's held set replays `sat` and another's replays `unknown`, and the brief
for this lane asked for the two-way number rather than an invented three-way
one. Notably the direction is **not** uniform: on only 2 of the 6 is every
`unknown` set larger than every `sat` set, so "we instantiated past the point of
decidability" is not the explanation for the other 4 — those are small `UFNIA`
sets (ground 5–19) that time out while a larger set on the same file is `sat`.

**So the addressable population is 58 rows clean, at most 64 with the MIXED
rows, of 127.**

## 2. The census needed splitting first — and this lane walked into the trap

[ADR-2015]'s own first section is about one give-up string covering several
exits. The instrument it left behind has the same defect one layer down, and
the first census this lane ran reproduced it.

**The record separator inside the committed census cells is `;QPROBE`, not a
bare `;`** — because the `why=` detail *contains* `;`. Splitting on `;`
truncates the largest bucket. A `why=` may additionally **wrap** another reason
(`the reduced solve's own reason was [Kind] …`) or **append** one after a stats
parenthetical (`…): <inner>`).

| | outer string | binding cause |
|---|---:|---:|
| distinct buckets | 5 | **10** |
| largest bucket | `Timeout｜preprocessed dispatch timeout after reduced solve` (25) | `lazy LIA pre-SAT skeleton exceeds the joint resource boundary` (22) |

**46 of the 78 had their binding cause behind at least one wrapper**, and the
25-row largest outer bucket is **four** distinct causes. The top bucket is not
the same bucket at the two levels, so a census keyed on the outer string ranks
the wrong remedy first.

**The binding-cause census, every bucket listed, denominator 78:**

| n | % `[Wilson 95 %]` | binding cause | kind |
|---:|---|---|---|
| **22** | 28.2 `[19.4, 39.0]` | lazy LIA pre-SAT skeleton exceeds the joint resource boundary | refusal |
| 17 | 21.8 `[14.1, 32.2]` | `combined theories:` eager Ackermann bound of 64 | refusal |
| 11 | 14.1 `[8.1, 23.5]` | integer bit-blast width ladder: wall-clock timeout | timeout |
| 10 | 12.8 `[7.1, 22.0]` | lazy Ackermann secondary bound of 2,000,000 | refusal |
| 7 | 9.0 `[4.4, 17.4]` | auto-dispatch timeout after NIA real relaxation | timeout |
| 5 | 6.4 `[2.8, 14.1]` | no model within the bounded integer width 32 | refusal |
| 3 | 3.8 `[1.3, 10.7]` | lazy LIA exhausted the configured timeout after N rounds | timeout |
| 1 | 1.3 `[0.2, 6.9]` | combined-theory timeout after scalar backend | timeout |
| 1 | 1.3 `[0.2, 6.9]` | LIA sat-model reconstruction declined in the integer theory | timeout |
| 1 | 1.3 `[0.2, 6.9]` | lazy LIA SAT skeleton declined after round N | refusal |

[ADR-2015]'s prose led with the eager Ackermann bound. It is second.

**One bucket remains `UNSPLIT` and is reported as such.** `no model within the
bounded integer width 32` (5) has **two** emit sites — `lia.rs:102` and
`combined.rs:156` — and nothing in the string distinguishes them. This lane did
not split it, because at 5 of 78 it cannot change the ranking; it is recorded so
the next lane does not treat it as one cause.

## 3. The structural result: 70 % are REFUSALS, not exhausted clocks

| | n of 78 | `[Wilson 95 %]` | ground median | wall median | divisions |
|---|---:|---|---:|---:|---|
| **REFUSED by a bound** | **55** | 70.5 % `[59.6 %, 79.5 %]` | 2,920 (21 at the 8,192 cap) | **1,407 ms** of 10,000 | UFLIA 40, UFNIA 15 |
| **EXHAUSTED the clock** | 23 | 29.5 % `[20.5 %, 40.4 %]` | 96 (0 at the cap) | 10,024 ms | UFNIA 18, UFLIA 5 |

Refusal and exhaustion have opposite remedies, and the two populations separate
cleanly **by division**: `UFLIA` refuses 40:5, `UFNIA` exhausts 18:15. Seventy
per cent of this wall is policy, declining in a seventh of the budget it was
given.

## 4. The absurd-looking numbers, read rather than assumed

**`64` is not a unit error.** `ackermann_congruence_pairs` sums `k(k−1)/2` over
functions and eager elimination emits exactly one congruence constraint per
pair, so 57,219 constraints against a bound of 64 compares like with like.

**But the bound was never calibrated against the cost of the expansion.** Its
own doc comment (`euf.rs:29-63`) says the bound must sit *"below the smallest
hanging instance, not merely below the construction blowup"*, because the
instances that hang do so *"in the downstream LIA/IDL solve (which does not
honor `config.timeout`) even when the O(k²) construction itself is cheap."* It
was placed between the largest decided in-tree instance (**40** pairs) and the
smallest observed hang (**117**). So `64` is a **proxy for an unbounded
downstream solve**, fitted to a handful of in-tree files in 2026-06, and the
900x gap to 57,219 measures the file's function-application count, not any
cliff. It has **never changed since `6233a7c98`, 2026-06-24.**

**And the same constant means two different things at its two call sites.**
At `auto.rs:4068` exceeding it is a **route selector**: the eager path is
skipped and the **lazy/CEGAR** route runs instead, under the real deadline. At
`combined.rs:86` exceeding it is a **hard decline** that returns `Unknown` with
no fallback at all. **All 17 of our censused replays carry the
`combined theories:` prefix — 17 of 17 at the hard-decline site, 0 at the
route-selector site.** The lazy fallback that already exists for the other
caller is simply not offered to them.

**The pre-SAT skeleton boundary is a MEMORY bound that measured its own
headroom at two orders of magnitude.** Its re-derivation (`832c2afd0`,
2026-09-08) measured peak RSS at **71 MiB** on its largest admitted point —
`1/115th` of the 8 GiB ceiling it cites — with peak RSS moving by at most
**0.5 %** whether the envelope was enforced or removed, and it recorded that
*"there is no measured memory risk anywhere in the region it was refusing."* It
then set the envelope to the largest point measured and said plainly: *"above
this, nobody has measured, and unmeasured is not the same as safe."* The
queries it declines here sit at `atoms ≈ 14.7 k` / `cnf_vars ≈ 24 k` — **1.4x**
that point. The region doing the refusing is exactly the unmeasured one.

Its predicate is
`(atoms > 1024 && cnf_vars > 4096) && (atoms > 10240 || cnf_vars > 16384)`; the
base trigger's own justification was **retired** in 2026-09-08 (it blamed
`BatSat`, which [ADR-1703] removed from this path) and the trigger now refuses
nothing on its own.

**A second missing wiring, found beside the first.** The
`oversized_admission_probe` rescue is wired only into `check_with_arith_dpll`
(`dpll_lia.rs:578`). The UF+arith route reaches the boundary through
`check_with_arith_dpll_reusing_lemmas` and `euf.rs:948`, neither of which passes
through it — so a `UFLIA`/`UFNIA` instantiated conjunction that crosses this
rectangle gets **no bounded online-CDCL(T) shot at all**.

**And the lemma batch that grows the skeleton is uncapped.** The lazy
function-consistency loop adds a congruence lemma for **every equal-argument
pair** once *any* pair is violated (`euf.rs:1112-1143`), so a round with
`violated_pairs=448` adds `lemmas_added=17,750`. Neither
`MAX_PRESEEDED_FUNCTION_CONSISTENCY_LEMMAS` (256) nor
`MAX_POST_CANDIDATE_SIBLING_LEMMAS` (1) bounds that path, and no per-round cap
exists. The batching is **deliberate and regression-tested** (`42fc03e6e`,
which measured the narrow "violated-only" policy and rejected it), but that
measurement was taken at **6 to 23** equal-arg pairs — three to four orders of
magnitude below what this population produces. `euf.rs:141-142` still justifies
the 2,000,000 lazy bound with *"the lazy loop never asserts all O(pairs)
constraints up front"*, which the code has not done since `b659d5744`.

## 5. Where 10 seconds goes on 11 ground terms

Not one hard solve. Measured on `UFNIA/2019-Preiner/combined/t3_rw899.smt2`
(11 ground terms, 10,007 ms, binding cause `integer bit-blast width ladder`),
release binary, pinned core, at a 10 s budget:

    20,626 offline LIA calls        18,678 LP relaxations
    20,546 Gomory cut calls          9,035 simplex solves
       801 arena clones          11,401,903 arena nodes cloned

`perf record` over the same run, self time:

| share | where |
|---:|---|
| 27.1 % | native CDCL search (`propagate` 20.7, `analyze` 4.9, heap 1.5) |
| ~22.5 % | allocator (`malloc`/`free`/`memmove`) |
| 15.8 % | simplex / Gomory rational arithmetic |
| 7.2 % | AIG + Tseitin encoding |

So the budget goes into **tens of thousands of small repeated arithmetic solves
and re-encodings**, about a fifth of it in the allocator. The width ladder
clones the arena per rung by design (`let mut scratch = arena.clone();`) and
**each clone copies the whole file's term DAG, not the held set** — 14,235 nodes
per clone for a set of 11 terms. This family is 11 of 78 and is **entirely
`UFNIA`** (11 of 11).

## 6. What the reference does instead

cvc5 1.3.4, its own instruments, on the **22 files whose binding decline is our
pre-SAT skeleton boundary** — the largest cause:

| | |
|---|---|
| refuted | **21 of 22** (1 `NONE`) |
| `global::totalTime` | median **70 ms**, min 25, max 3,019 |
| refuted with **zero** instantiation tuples | **9** |
| our held set at the **8,192** admission cap | **12 of 22** |
| **zero-instantiation refutations that are at our cap** | **8 of 9** |

`--dump-instantiations` is live **by mechanism**: it emits nonzero tuple counts
(up to 1,255) on 12 of the 21 refuted rows, so the nine zeros are a measurement
rather than a silently ignored flag.

**This is the finding that reframes the problem.** On the largest binding cause,
the reference refutes the file **without instantiating a single quantifier**,
while we have instantiated to the ceiling, built a ~15 k-atom / ~24 k-variable
arithmetic skeleton out of the result, and then refused that skeleton as
oversized. [ADR-2015] concluded the gap is *"downstream of the instantiation
loop entirely."* For 70 % of this population that is half right: the decline is
downstream, but **the set being declined is an artifact of over-instantiation**,
and the axis is *selection* — not budget ([ADR-1995]), ceiling ([ADR-1956]),
reach ([ADR-2005]), or head ([ADR-2015]), all of which are closed.

## 7. The A/B: raising the largest bound moves nothing

The lever is `AXEYUM_GROUND_DECIDE_PRESAT_ENVELOPE`, off by default, failing
**closed** (unset, empty, malformed, or a zero in either dimension all return
the shipped constants). It raises the moderate envelope from `10,240 / 16,384`
to `40,960 / 65,536` — past every observed decline in this population. The
give-up string prints the **effective** envelope, so the arm is visible **by
mechanism**; a silently ignored variable prints the shipped pair.
Mutation-verified: removing the zero-guard kills
`the_presat_envelope_lever_is_off_unless_spelled_exactly` and **exactly** that
test (43 passed, 1 failed).

**Interleaved per-file, one binary, two env values**, both arms back to back on
the same file on the same pinned core, order rotating per file. **Shard
configuration held fixed across arms**: s5 cores `{1,3,5,7}` and s6 cores
`{1,3,5,7}`, 8 shards, both arms *inside* each shard so a shard can never move
one arm relative to the other. s7 ran the controls. 24 s budget, 8 GiB
`ulimit -v`.

| run | rows | OFF decided | ON decided | GAIN | LOSS | FLIP |
|---|---:|---:|---:|---:|---:|---:|
| **main** `UFLIA`+`UFNIA` | 129 | **0** | **0** | **0** | 0 | 0 |
| **control** `QF_BV` (must not move) | 6 | 0 | 0 | 0 | 0 | 0 |
| secondary `QF_LIA` | 27 | 2 | 2 | 0 | 0 | 0 |
| **noise floor** (both arms shipped) | 129 | **1** | **0** | 0 | **1** | 0 |

Gain rate 0 of 129, **Wilson 95 % `[0.0 %, 2.9 %]`**. Wall clock 2,654 s vs
2,658 s — **1.00x**; the lever does not even cost time.

**The control is non-vacuous by ROUTE, not by assertion.** The committed census
records 5 of the 6 `QF_BV` rows as `search-timeout` on route `qf-bv`, which
spends the whole budget in bit-blast/SAT search and never reaches the
arithmetic pre-SAT skeleton this lever touches.

**And the NULL is non-vacuous, which is what makes it a measurement.** On
`javafe.ast.MethodDecl.005.smt2`, in the **shipped 24 s path** (not the replay
probe), the OFF arm records **both** pre-SAT bounds crossed —
`MAX_PRE_SAT_ARITH_ATOMS=15500/1024`, `MAX_PRE_SAT_CNF_VARS=23388/4096` — and
the ON arm records **neither**. The lever demonstrably changes which admission
bound fires, on a file in the measured population, and the verdict still does
not move.

**What the refusal converts into is also measured.** On
`AssignToRepField_AssignToRepField.N.smt2` the held-set replay's binding cause
moves from the skeleton-boundary **refusal** to a lazy-CEGAR **timeout** at
10,154 ms. The refusal becomes an exhausted clock, not a verdict.

**The noise floor settles it.** At **byte-identical** configuration the same
division moves **1 row** (`javafe.ast.SuperObjectDesignator.008.smt2`, `unsat`
at 22,731 ms in one pass and `unknown` at 25,027 ms in the other — a row
sitting on the 24 s budget). **The lever's measured effect (0) is smaller than
the run-to-run band of the measurement built to detect it (1).** Independently,
this lane's OFF arm decides 0 of 129 where [ADR-2015]'s census at the same
budget decided 2, which is the same band seen a third way.

## 8. Decision

**Record the finding; ship the lever OFF.** R4's go/no-go was **>= 6 rows net**;
it is **0**.

The diagnostic knob stays, off by default, because the next lane will want the
same A/B against a different envelope and should not have to rebuild it — and
because the constant it overrides still carries a doc comment saying nobody has
measured above it. Now somebody has: **on this population, above it is worth
zero.**

What this does *not* say is that the bound is right. It says the bound is not
what is costing us these files. The three findings that point somewhere else:

1. **Refusals dominate (70.5 %) but raising the biggest one buys nothing**,
   because the work behind it does not finish either — the refusal converts to
   a timeout. The arithmetic skeleton built from a 2,920-term ground set is not
   merely *inadmissible*, it is *undecidable inside the budget*.
2. **So the target is the SIZE of the set, not the bound that refuses it.**
   The reference refutes 21 of these same 22 files at a median of **70 ms**,
   **nine of them without instantiating a single quantifier**, and **eight of
   those nine are files where we flooded to the 8,192 admission cap**. Selection
   is the axis; [ADR-1995], [ADR-1956], [ADR-2005] and [ADR-2015] have closed
   budget, ceiling, reach and head, and none of them is selection.
3. **Two missing wirings are worth more than any bound change**, and neither is
   a policy question:
   - `combined.rs:86` **hard-declines** on the eager Ackermann bound with no
     fallback, while `auto.rs:4068` treats the same bound as a route selector
     and runs the lazy/CEGAR route instead. **17 of 17** censused replays are at
     the hard-decline site. Giving it the fallback its sibling already has is
     21.8 % of the population.
   - `oversized_admission_probe` is wired only into `check_with_arith_dpll`, so
     the UF+arith route that reaches the skeleton boundary gets **no bounded
     online-CDCL(T) shot at all**.

### Not measured here, and reported as "did not run"

- **R5** (3x per arm on every moved row): **not reached** — no row moved.
- **R9** (new verdicts against three authorities): **no new verdicts**, so the
  comparable denominator is **0/0** on each of `:status`, z3 and cvc5. Printed
  rather than omitted, per [ADR-1957].
- The `no model within the bounded integer width 32` bucket (5 of 78) is left
  **`UNSPLIT`** across its two emit sites.
- A per-round cap on the lazy function-consistency lemma batch was **not
  built**. The narrow "violated-pairs-only" policy is already closed
  (`42fc03e6e` measured and rejected it), but a *cap* is a different lever and
  is untested. It is the one this lane would pick up next.

## 9. The rules that were pre-registered, against what happened

| rule | pre-registered | outcome |
|---|---|---|
| R1 | split any string covering several sites before censusing | the 25-row largest bucket was **4** causes; 46 of 78 were behind a wrapper. One bucket (5) left `UNSPLIT` and reported |
| R2 | publish every cause with the denominator, zeros included | 10 buckets, all listed |
| R3 | no conversion RATE pre-registered | none quoted |
| R4 | ship only if >= 6 rows move net, all STABLE-GAIN | **0** -> **ships OFF** |
| R5 | 3x per arm on every moved row | **not reached** (no row moved) |
| R6 | noise floor, whole division, same arm | **1 of 129** at fixed code |
| R7 | interleaved, one binary, two env values, polarity stated | done; polarity in the runner header |
| R8 | control division that must not move, shown non-vacuous | `QF_BV` 0 moved; non-vacuous by route (`qf-bv` search-timeout) |
| R9 | new verdicts vs three authorities, denominators separate | **no new verdicts**; denominator 0/0 each |
| R10 | sat-side reference control is vacuous; control on unsat | no rewrite shipped; nothing to control |
| R11 | Wilson for every small-n proportion | every ratio here |
| R12 | the A/B measures THIS BRANCH | it does; see below |
| R13 | freshness licensed by `find -newer`, not exit status | it **fired**: a build reported exit 0 with a stale binary and the guard caught it |
| R14 | unfinished checks reported as "did not run" | R5 and R9 above |

**The pre-registered prediction was that a bound-raising lever moves fewer than
6 rows and ships OFF, most likely by converting refusals into timeouts.** It
moved **0**, and the conversion was measured directly on
`AssignToRepField_AssignToRepField.N.smt2`. The prediction was right in both
its direction and its mechanism, and is recorded here because it was written
down before the measurement.

**R12 — post-merge prediction.** The A/B arm measures this branch, which is
`main` at `4436e9cd5` plus this lane's knob. The knob is read only inside
`exceeds_pre_sat_skeleton_boundary` and `pre_sat_skeleton_boundary_reason`, and
returns the shipped constants when unset, so the default build is
byte-equivalent in behaviour. **Predicted post-merge value: unchanged — 0 rows
moved, and the shipped division totals identical to `main`.** The reason is
that no shipped call site reads a different value than it did before.

[ADR-1703]: adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md
[ADR-1956]: adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md
[ADR-1957]: adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-1976]: adr-1976-qf-nia-is-model-bound-adr-1937-took-the-sat-half-and-the-eager-split-is-worth-four.md
[ADR-1980]: adr-1980-the-cheap-check-was-the-whole-target-a-dispatch-decline-not-a-datatype-capability.md
[ADR-1995]: adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md
[ADR-2000]: adr-2000-the-front-door-refusal-was-not-the-binding-constraint.md
[ADR-2005]: adr-2005-the-instances-are-e-matchable-and-we-already-build-them.md
[ADR-2010]: adr-2010-the-sat-side-replay-cannot-see-the-parser.md
[ADR-2015]: adr-2015-the-round-head-is-a-symptom-the-ground-checker-is-the-wall.md
