# lia-warm-decider, 2026-09-08 — warming the offline conjunctive `QF_LIA` decider

Working diary. Appended as the lane ran; nothing here is retro-fitted.

## The task, and the number it came with

The offline conjunctive decider (`lra::lia_simplex_capped`) is a pure function
of an assertion list: a fresh `IntCollector`, a full term walk and
linearization, a full integer-tightening pass, then the Gomory cut round and
branch-and-bound. Its dominant caller is a lazy `DPLL(T)` loop whose literal
list differs from the previous call by one literal.

The brief carried three claims from a sibling instrumentation lane:

1. the decider is entered 363,062 times across 79 lost files, cold every time;
2. the cut engine decides 99.99% of those calls;
3. the warm rational filter in front of it refutes **nothing** on that
   population (`filter_refuted = 0`, integral 2.2%) and should be deleted or
   gated off.

**Claim 3 is refuted below on its own population.** Claims 1 and 2 were not
re-measured here — the sibling lane's instrumentation is not on `main`, and
this lane's counters answer a different question. Where a number below is this
lane's, it says so.

## What was built

`crates/axeyum-solver/src/lra/warm.rs`. Two stages of the offline decider are a
function of **one literal alone** — collection (the term walk and
linearization) and tightening (the gcd-aware strict-to-non-strict rewrite) — so
they are cached per literal, permanently. The assembled system is then kept
across calls and updated by the trail delta: truncate to the longest common
prefix of the live literal list, append the rest.

`tighten_int_constraints` and `decide_int_constraints` were factored out of
`lia_simplex_capped`, so the warm path drives the identical rewrite and the
identical engine dispatch rather than a second copy that could drift.

### The constraint that shaped the design

Both offline engines are sound on **any** input. A warm path that assembled a
permuted, padded or reordered system could therefore never return a wrong
`sat`/`unsat` — it would quietly decide a *different set of cases*, and a
verdict-only differential would pass the whole time. That is a coverage change
disguised as a performance change.

So the decider reproduces the cold path's system exactly, column numbering
included. `IntCollector` gained a per-assertion touch log (repeat touches
included, which is the load-bearing part), because the cold numbering is
exactly `dedup(concat(touch_log(l) for l in live order))` and assembly
re-derives it. `warm_assembles_the_same_system_the_cold_path_builds` compares
the assembled system — constraints, order, `origin` tags, `nvars` — against a
test-only `cold_int_system`, not the verdict.

### Configuration

`LiaWarmPolicy` is a policy object with named fields, not a compiled-in
behaviour. `LiaWarmPolicy::OFF` reproduces the pre-warm path field for field,
and `AXEYUM_LIA_WARM` selects the arm, so **an A/B is a policy flip in one
binary**. It is registered in `config_registry.rs`, so a `--trace` run's own
`; config` line says which arm produced it.

## The tests, and the proof that they can fail

Five mutations, applied one at a time in a `lane-snapshot.sh` scratch tree, each
a plausible way for a warm cache to go stale or drift. Re-run at the end against
the code that **ships**, not the code the tests were first written against
(`mutation-results-shipped.txt`); baseline 13 passed.

| mutation | what it breaks | tests killed |
| --- | --- | --- |
| `stale-columns` | a retracted literal keeps its local column mapping | 6 |
| `unchecked-prefix` | reuse `min(prev, live)` instead of the true common prefix | 6 |
| `stale-constraints` | a retracted literal's constraints stay in the system | 6 |
| `no-tightening` | a cached literal skips the tightening pass | 2 + 2 hangs |
| `sorted-columns` | allocate local columns in ascending global order, not touch order | **2** |

`sorted-columns` is the one worth reading. It produces a system that is a sound
permutation of the right one — and **every verdict-level test passes under it**,
including the theory-level differential. Only the two system-comparison tests
die. That is the measured form of the argument above: a verdict-only
differential cannot see column drift, and would have let this module silently
decide a different set of cases forever.

`no-tightening` is killed by assertion on two tests and by non-termination on
two more (branch-and-bound grinding past 60 s on random instances where the
tightened LP is exact). Recorded as detected; the hang is itself a statement
about what tightening is worth.

The adversarial staleness case is stated directly in
`a_retracted_literal_leaves_no_trace_in_the_next_verdict`: assert `x >= 5`, then
both `x >= 5` and `x <= 0` (unsat), then retract `x >= 5` **from the front** so
the survivor moves to a different position and a different column numbering.
`x <= 0` alone is sat; a system that kept the retracted literal answers unsat.

## Method for the A/B, stated because the population makes the obvious metric meaningless

The population is files axeyum **loses**, so in every arm nearly every run
spends its whole budget. Wall time is pinned to the timeout and a ratio of 1.00
would be an artefact of the harness. So:

* the score is **live-set decisions in the same budget** —
  `theory_offline_checks + theory_filter_answers`. Counting only the offline
  half would score the filter's contribution as zero work;
* plus any verdict that changes;
* arms **alternate order per repetition**, so machine drift is shared;
* files where no arm ever entered the online theory are **excluded from the
  throughput figures and reported separately** — 56 of 85. A mean over files the
  code never ran on is a measurement of the denominator;
* a decided verdict that disagrees between arms is reported as a soundness
  alarm, never averaged into a timing number.

Population: `bench-results/parity-losses-20260905/{QF_LIA,QF_UFLIA}.txt`, 85
files. Budget 8,000 ms, one repetition, three arms, one release binary at
`ca7717c5e`. Host s4, load average 8–11 throughout (another lane was running a
24 s parity sweep on the same box); the alternating-arm order is what keeps that
from landing on one arm.

### An instrument that was blind where the question is

First attempt: the counters were thread-local, like the seven `--trace` guards
already in `smtcomp_cli`. On **every one of the six hardest `QF_UFLIA` losses**
the trace printed no warm-decider counters at all — the watchdog on the main
thread gives up before the worker returns, and a thread-local snapshot is
unreachable from there. That is an instrument that goes blind precisely on the
population it exists for.

So there are two collectors now: `LiaWarmStatsGuard` stays thread-local (what a
unit test wants — its numbers cannot be polluted by the harness's other
threads), and `LiaWarmProcessStatsGuard` is process-wide relaxed atomics armed
on the main thread. The counters are monotone and nothing reads them back into
the search, so a live read from the watchdog path is a lower bound on the work
done — the only number that path has ever been able to report.

## The baseline moved under these numbers, and they say so

Everything in "Result 1" and "Result 2" below was measured **before** this lane
merged `origin/main`, at binary `ca7717c5e`. Main then landed
`c557cbe6d`, which removes the per-check `TermArena` clone from the online
integer theory — measured there at 10-49% of the binding route's budget, median
about 21%.

That is a change to the **`off` arm**: the cold baseline these ratios are
against got materially faster, so the warming ratios below are an over-estimate
of what warming adds on top of the merged tree. The filter numbers are not
affected in the same way — they are counts of what the filter answered, not a
ratio against the cold path — but they were taken on the same pre-merge binary
and are labelled as such.

"Result 4" re-runs the whole thing post-merge on an idle host. Where the two
disagree, Result 4 is the one about the code that ships. The pre-merge numbers
are kept rather than overwritten because the decision to keep the rational
filter was made on them, and a decision should be checkable against the evidence
that was actually in front of it.

## Result 1 (PRE-MERGE, binary `ca7717c5e`): the rational filter stays. The premise was wrong.

Over the 29 of 85 files where the online theory is entered:

| arm | live-set decisions | offline decisions | filter answered | filter refuted |
| --- | --- | --- | --- | --- |
| `off` (cold, filter on — today) | 92,587 (x1.00) | 12,824 (x1.00) | 79,763 | **20,102** |
| `filter` (warm, filter on) | 97,078 (x1.05) | 22,908 (x1.79) | 74,170 | 17,964 |
| `warm` (warm, filter off) | 70,107 (x0.76) | 70,107 (x5.47) | 0 | 0 |

The filter answers **86%** of live sets and **refutes a quarter of what it
answers**. Switching it off does not remove a pass that never pays — it pushes
80,000 cheap decisions onto the expensive decider and costs 24% of the
throughput. On twelve of the 29 files the offline decider is never reached at
all in the `off` arm (`off.off = 0`), so warming it cannot help there by
construction.

### CONTESTED — two measurements of the same counter, and this note settles neither

The `lia-counters` lane measured **`filter_refuted = 0`**. This lane measured
**20,102 refutations of 79,763 answers**. Both numbers stand; neither is
withdrawn here, and a reader quoting either must name which.

They do not share a population or a method:

| | `lia-counters` lane | this lane |
| --- | --- | --- |
| population | its own `QF_LIA` sweep | the 29 of 85 `QF_LIA`+`QF_UFLIA` loss files where the online theory is entered |
| budget | 24 s | 8 s (confirmed at 24 s below) |
| arm | shipped default | the `off` arm — cold decider, filter on |
| counter | `LiaCounters::filter_refuted` | `theory_filter_refuted`, incremented at the same `RationalFilter::Refuted` site |

After the 2026-09-08 merge the two counters are literally the same field
(`LiaCounters::filter_refuted`), so a future sweep can settle this without
either lane's instrument being in question. Until such a sweep exists, the
default keeps the filter — which is the conservative choice under BOTH numbers,
since a filter that refutes nothing costs only its own pass while one that
refutes a quarter of what it answers is load-bearing.

Acted on: `LiaWarmPolicy::WARM` keeps the filter; the arm that turns it off is
renamed `WARM_NO_FILTER` and documented as a diagnostic. A test pins the
reverted default, because a default that was already once wrong is one edit from
being wrong again.

## Result 2 (PRE-MERGE, binary `ca7717c5e`): what warming bought

With the filter held fixed on both arms (`filter` vs `off`, so warming is the
only difference):

* **offline decisions in the same budget: x1.79 in total, median x1.31 per
  file, max x7.12**;
* **0 of the 20 comparable files got slower** (none below x0.98);
* end-to-end live-set decisions: **x1.05 in total, median x1.03 per file**.

The gap between x1.79 and x1.05 is the honest headline: on this population the
offline decider is *not* where the budget goes. The filter handles 86% of live
sets, so making the remaining 14% 1.79x faster moves the total by 5%.

**No file changed verdict.** 11 `sat`, 74 `unknown` in all three arms; zero
disagreements between arms on a decided file; **zero files flipped from
`unknown` to decided**. Warming closed no losses at an 8 s budget.

Per-file, the families separate cleanly:

* `RF-13`, `ex*_2600_100`, `ex*_2400_100`, `xs_*`, `convert-jpg2gif` — the
  offline decider is the work, and warming gives x1.06 to **x7.12**;
* `hash_sat_*` / `hash_uns_*` (12 files) — the filter answers nearly everything,
  `off.off` is 0 on seven of them, and warming the offline path is a no-op;
* `FISCHER10-13-fair`, `prp-0-19` — likewise filter-dominated.

## Result 3 (PRE-MERGE, binary `ca7717c5e`): confirmation at the real 24 s budget, and the one flip that was not one

Stage 1 ran at 8 s to cover all 85 files. Stage 2 re-ran the 29 engaged files at
the **24 s** budget the parity sweep uses, same three arms, same alternating
order, release binary `ca7717c5e`.

| arm | live-set decisions | offline decisions | filter answered / refuted | verdicts |
| --- | --- | --- | --- | --- |
| `off` | 156,014 (x1.00) | 18,152 (x1.00) | 137,862 / 31,998 | 13 sat, 16 unknown |
| `filter` | 168,462 (x1.08) | 30,272 (**x1.67**) | 138,190 / 31,829 | 13 sat, 16 unknown |
| `warm` (no filter) | 124,848 (x0.80) | 124,848 (x6.88) | 0 / 0 | 14 sat, 15 unknown |

Both stage-1 results hold: warming gives the offline decider **x1.67** the
throughput with the filter held fixed (stage 1: x1.79), the end-to-end gain is
**x1.08** (stage 1: x1.05), and dropping the filter costs 20% of the decisions
(stage 1: 24%). The warm cache is doing more at the longer budget: **92.9% of
the live literal set reused per check, 8.3% of the constraints rebuilt.**

**The one apparent coverage change was a host artefact, and checking it is why
this section exists.** `xs_24_34.smt2` came back `unknown` in the `off` and
`filter` arms and `sat` in the `warm` arm — which would read as "dropping the
filter closed a loss". Two things say otherwise:

1. In the arm that decided it, the warm decider recorded **zero** checks
   (`off=0 flt=0`) — the online `LIA` theory was never entered, so it cannot be
   the cause of the decision.
2. Re-run alone, three repetitions per arm: **`sat` in all three arms, every
   repetition, at 13.3–17.1 s** (`xs2434-repeat.json`). Under the stage-2 sweep's
   own load two arms crossed the 24 s budget and one did not.

So: **no file changed verdict because of this work, in either stage.** Zero
disagreements between arms on a decided file at either budget.

Per file at 24 s the median offline ratio is **x1.01**, against x1.31 at 8 s,
with total x1.67 and max x4.77. The gain is concentrated, not spread: `RF-13`
x4.77, `xs_24_34` x4.21, `xs_19_29` x1.76, and most files unchanged because
another route owns their budget. Reporting the median alone would understate it
and the total alone would overstate how broadly it applies; both are above.

## What is warm and what is still cold

Warm: the per-literal collection cache (**97.7% hit rate** in the shipped
configuration at 24 s, 24,282 collections against 1.03 M hits), the tightening,
and the assembled system — **92.9% of the live literal set is reused per check**
and only **8.3% of the constraints are rebuilt**.

Still cold, and stated in the module docs rather than implied away: the
standard-form tableau and the LP. `build_gomory_tableau` writes a dense
`m x 2*nvars` body whose column layout is a function of `nvars`, so it changes
shape whenever the live variable footprint does, and the tableau the cut round
leaves behind has been pivoted away from that layout. Warm-starting it is
separate work with a separate soundness argument.

## The next thing to fix, named by the counters rather than guessed

Cold starts are the largest single assembly reason: `assembly_cold-start` =
35,949 of 82,684 checks in the shipped configuration at 24 s (43%), and 154,462
of 350,014 in the no-filter arm. The cause is visible in the reason histogram —
conflict-core
minimization drops literal **0** first, which makes the shared prefix empty, and
every subsequent probe in that minimization is a `diverged` (51,182). Iterating
the deletion loop from the other end would fix the prefix but produce a
different greedy core, which is a behaviour change and not free; a second
"probe" assembly anchored on the full live set would not be. Either way the
figure to move is `assembly_cold-start`, and it is now readable per file.

## Reproducing

```sh
cargo build --release -p axeyum-bench --example smtcomp_cli
AXEYUM_LIA_WARM=off      target/release/examples/smtcomp_cli <file> --timeout-ms 8000 --trace
AXEYUM_LIA_WARM=nofilter target/release/examples/smtcomp_cli <file> --timeout-ms 8000 --trace
                         target/release/examples/smtcomp_cli <file> --timeout-ms 8000 --trace
```

The counters are on the `; lia …` line — the warm group's fields are prefixed
`warm_`. `warm=off`, `warm=not-reached` and `warm=measured` are deliberately
three different outputs: the policy switched the group off, the group was
collected and the decider never ran, and the group ran. A bare `0` cannot tell
those apart, which is what `LiaCounters::group_reading` exists for.

On a file whose solve never returns, the same counters come back on a
`; partial lia …` line, recovered from the live-instruments board. That line is
a lower bound, never a rate's denominator — see `crate::live_instruments`.
