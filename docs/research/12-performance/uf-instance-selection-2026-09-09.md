# UF — relevance-driven instance selection does not move the population, and why

This is the follow-on to
[the loss attribution](uf-quantified-loss-attribution-2026-09-09.md), which
ended by naming three targets for this lane and putting **instance relevance**
first: *"admit instances that are `FALSE` or `UNIT`, and stop admitting `TRUE`
ones. Today the loop admits `TRUE` clauses at 81.6 % of its ceiling."*

That target is built, measured, and **it does not decide a single additional
file.** Neither does the sharper version of it that the measurements suggested
instead. The negative is the finding, and the reason for it redirects the work,
so this note leads with the reason rather than with the zero.

**The short version, in the order the measurements force.** The filter that
target 1 asked for already existed and is the largest single thing the loop does
— it declines 528,561 candidates while admitting 198,231. The "67.6 % of the pool
is already TRUE" figure that motivated the target is 98.8 % an artifact of how
the census asks the question; the actionable remainder is 0.83 %. The pool is not
full of irrelevant traffic either: **every admitted deferred candidate on this
corpus is between 1 and 4 literals from conflicting.** And the reason a relevance
signal cannot separate them is the last measurement and the one that redirects
the work: **85.6 % of the candidates the policy scores carry a literal the
congruence cannot value at all.** Congruence-based relevance is blind on six
sevenths of the population it was asked to rank.

## Protocol

Byte-identical to the attribution note's, so the two are comparable:
`MEM_LIMIT_GB=8 timeout 29 scripts/mem-run.sh smtcomp_cli <file>
--timeout-ms 24000`, plus `AXEYUM_QPROBE=1` (and `AXEYUM_FLOODPROBE=1` for the
census sweep), on the 32 files of
`bench-results/parity-losses-20260908/UF.txt`. Host s4, `taskset` pinned: the
`shipped` baseline on cores 0-7 and one comparison arm at a time on cores 8-15,
so the two arms of a comparison never shared a core. The box was not otherwise
idle. **No timing claim in this note is load-corrected, and none is load-bearing
— the reported quantity is how many files were DECIDED, which is not a wall-time
measurement.**

The arm is selected with `AXEYUM_QINST_RELEVANCE=<arm>`; an unset or
unrecognized value is `RelevancePolicy::SHIPPED`.

## What target 1 asked for was already the shipped behaviour

`IncrementalEmatchSession::lazy_clause_batches` evaluates every candidate
instance against the round's congruence before it enters any admission pool. A
candidate whose clause is `ClauseValue::True` is counted in
`LazyClauseBatch::redundant` and **pushed into no pool at all** — it is not
deferred, it is dropped. `False` goes to the urgent pool, `Unit` to the unit
pool, and only `Undetermined` (or unclassifiable) reaches the deferred pool the
ceiling fills with. The classification is recomputed from scratch every round
against that round's congruence, so it does not go stale either.

Its measured size, summed over the population:

| | count |
|---|---:|
| candidates declined as already entailed (`redundant_at_generation`) | **528,561** |
| instances actually admitted (census `instances`, 29 files reporting) | 198,231 |

**The shipped loop rejects 2.7 entailed candidates for every instance it
admits.** "Stop admitting TRUE ones" was not a missing capability; it was the
loop's largest filter, and the attribution note did not know it because nothing
counted it. It is counted now.

## The 67.6 % was 98.8 % an artifact

So where did "67.6 % of the admitted pool is TRUE" come from? From asking a
different question. `floodprobe_cap_census` evaluates each **retained** instance
against the **final** congruence, not the congruence that was in force when it
was admitted. Those instances were admitted while undetermined and became
entailed later.

But most of them became entailed *by themselves*. The matcher's e-graph merges
every top-level positive equality in the ground set, so an admitted instance
that **is** such an equality is made true by its own admission and would read
`TRUE` no matter what the rest of the congruence knew. The census now splits the
bucket:

| census over 29 files | count | share of TRUE |
|---|---:|---:|
| `clause_true` | 136,495 | 100 % |
| ├ `clause_true_self_merged` — true by its own merge | **134,856** | **98.8 %** |
| └ `clause_true_by_others` — true by the rest of the congruence | 1,639 | 1.2 % |

`clause_true_by_others` is **0.83 % of the 198,231 admitted instances**. That is
the entire population any relevance policy could have declined for being
entailed. It is not 67.6 % and it never was.

The self-merged 98.8 % are not waste either: a positive equality instance is
what *drives* the congruence. Dropping it would delete a fact, not remove noise
— which is why the eviction lever below refuses to touch that class.

## The four arms, and what each one actually did

`RelevancePolicy` is a swappable object beside `GroundBudget`
(`qinst_egraph.rs`). `GroundBudget` is the **volume** policy; this is the
**selection** policy. `SHIPPED` reproduces today's behaviour exactly, and every
other arm differs from it in a named lever, never in a threshold
(`shipped_relevance_policy_is_the_shipped_selection` pins that).

The levers:

- **`rank_by_residual`** — order the budgeted deferred slice by
  `clause_residual_width`, how many literals the congruence has *not* already
  falsified, instead of by instantiation generation alone. Generation is a
  *provenance* order; it says how deep a candidate was derived and nothing about
  whether it is close to a conflict.
- **`max_residual_width`** — decline candidates further than that from a
  conflict (`narrow`, `full`: 3).
- **`evict_entailed`** — drop retained instances the congruence has come to
  entail, freeing ceiling slots. Restricted to instances that are **not**
  themselves a top-level positive equality; see the soundness argument below.

Every arm reports a **funnel**, not a tally: `scored` (candidates the policy
computed a width for), `declined_wide`, `declined_tautology`, `evicted`, and
`reordered_rounds`. A policy that never reaches a candidate and a policy that
reaches every candidate and changes nothing produce identical verdicts; only
`scored` separates them, and it is the first column of every row below for that
reason.

| arm | criterion | scored | declined_wide | declined_taut | evict_scanned | evicted | reordered_rounds | **decided** |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| `shipped` | equality | 0 | 0 | 0 | 0 | 0 | 0 | **0 / 32** |
| `narrow` | equality | 290,116 | 8,259 | 104 | 0 | 0 | 2,534 | **0 / 32** |
| `evict` | equality | 294,293 | 0 | 104 | 846,617 | 1,368 | 2,345 | **0 / 32** |
| `full` | equality | 294,645 | 8,259 | 104 | 846,221 | 1,368 | 2,345 | **0 / 32** |
| `entail` | bool units | 259,562 | 0 | 100 | 0 | 0 | **11,877** | **0 / 32** |
| `entail-narrow` | bool units | 259,562 | 5,585 | 100 | 0 | 0 | 11,877 | **0 / 32** |

The policy ran. It saw roughly 290,000 candidates, declined 8,259 of them by
width, dropped 1,368 entailed retained instances, and changed the admitted slice
in over 2,300 rounds. **Zero files moved**, and the verdict distribution is
identical to shipped's (29-30 `unknown`, 2-3 aborts under the 8 GiB cap).

`narrow` was run twice, a rebuild apart, as a reproducibility check on the funnel
itself: 290,116 / 8,259 / 104 / 2,534 the first time and 287,077 / 8,275 / 105 /
2,537 the second. The counts move by about 1 % because a file cut off at 24 s
stops at a slightly different round under different load; the verdict column does
not move at all, which is the column the conclusion rests on.

## Why, part one: there is no far-from-conflict population to filter

The funnel reports the residual band it saw. Over every reading with
`scored > 0`, on every file in the population:

```
residual_min = 1..2      residual_max = 1..4
```

**No admitted deferred candidate anywhere on this corpus is more than four
literals from conflicting, and most are one or two.** That is the sentence that
kills the target. The attribution note's picture — a ceiling filled with
irrelevant traffic that a relevance signal could separate from the useful kind —
is not what is in the pool. The pool is almost entirely one or two facts short of
a conflict, in a population where `clause_false = 0` on every single file. These
instances are not far away. They are adjacent, and they never arrive.

`max_residual_width = 3` therefore declines only the width-4 tail: 8,259 of
290,116 scored candidates, 2.8 %. There is nothing else for it to decline. And
ranking by width reorders a set whose members all carry the same two or three
values, which is why `reordered_rounds` is large and the effect is nil.

## Why, part two: the oracle is blind on 85.6 % of what it ranks

The residual band explains why the *filter* has nothing to remove. This explains
why the *ranking* cannot work either, and it is the finding that should decide
what gets built next.

`evaluate_equality_clause_with` — the congruence classifier the whole selection
layer is built on — speaks only about equalities. On a clause carrying an
uninterpreted predicate application it returns `None`, and the candidate is
deferred **by default rather than by judgement**. The funnel counts them:

| scored candidates (`narrow`, 29 files reporting) | count | share |
|---|---:|---:|
| total scored | 287,077 | 100 % |
| **the congruence cannot value at all** (`unclassifiable`) | **245,828** | **85.6 %** |

Half the population carries predicates at all — 16 of the 32 files declare at
least one `Bool`-returning function, one of them 137 — and on those files the
deferred pool is essentially all of this kind. A residual width computed for such
a candidate counts how many *facts the oracle has no opinion about* remain. It is
a number, it is comparable, and it means nothing. Ranking two of them against
each other ranks noise.

**This is the ceiling on congruence-based relevance selection for this division,
and no arm of this policy can lift it.** It is not that the ranking function is
the wrong one; it is that the signal it ranks on is absent for six sevenths of
the candidates. Any selection policy that would work here has to score on
something the equality core does not see — which is a different capability from
the one target 1 named.

## The criterion axis, and what it says about partial-substitution pruning

A filter with one hard-coded notion of "useless" is a narrow special case of a
policy that takes the criterion as a parameter — cvc5's instantiation-evaluation
layer carries five (`NONE` / `CONFLICT` / `PROP` / `NO_ENTAIL` / `MODEL`) for
exactly that reason, and requests different ones from E-matching and from
conflict-find. `RelevancePolicy::criterion` is that axis here, with the two
values our evaluator can support:

- **`EqualityOnly`** — the shipped classifier's world. Equalities and
  disequalities in the congruence, nothing else.
- **`BooleanUnits`** — equalities plus **ground Boolean units, closed under
  congruence**. A ground conjunct that is a Boolean application asserts it; its
  negation asserts the negation; congruent applications share the value. Sound
  as an admission filter, because the unit that gives a literal its value is
  itself a ground conjunct.

That is the minimum an evaluator needs before it can have any opinion about a
predicate atom, and it is a **prerequisite** for the partial-substitution
pruning cvc5 does: a criterion that cannot value a completed body cannot value a
partial one either. So it is worth knowing exactly how much of the blindness it
removes.

| | scored | cannot value | share |
|---|---:|---:|---:|
| `narrow` — `EqualityOnly` | 287,077 | 245,828 | **85.6 %** |
| `entail` — `BooleanUnits` | 259,562 | 218,221 | **84.1 %** |

**1.5 percentage points**, and still 0 of 32 files. The arm is not inert — it
reorders 11,877 rounds against `narrow`'s 2,537, a 4.7x difference — it simply
has almost nothing to say, and the reason is the useful part:

**These files do not assert their predicates as ground units.** Their predicate
atoms occur inside clauses, and a clause gives its literals no value. cvc5's
evaluator can value a predicate atom because in a CDCL(T) search the
propositional layer has *decided* that literal and asserted it into the equality
engine — the value comes from the current assignment, not from the input's unit
conjuncts. Our instantiation loop runs **outside** any such search: it
accumulates a ground set and re-checks it from scratch with `check_auto`, so at
the moment it judges a candidate there is no partial assignment to judge
against.

**That, not earliness, is what stands between this loop and an `ieval`-shaped
pruning layer.** Building the incremental version on the present evaluator would
inherit an oracle that is blind on 84 % of the candidates, and cutting a match
search early on a criterion that cannot speak cuts nothing. The measured
comparison the coordinator asked for is therefore: post-hoc filtering gains 0
files, and an incremental version of the *same criterion* would gain 0 files
faster. The lever is the criterion, and the criterion needs an assignment.

There is a concrete route to one: the loop already builds an
`OnlineQuantifierClauseSession` — a retained CDCL(T) session over the
quantifier-free subset — and discards its assignment. Reading the criterion off
that session is the version of `ieval` this architecture can actually support,
and it is a different task from the one measured here.

## What the width score DID find, and how small it is

The width score is not the same function as the shipped classifier and it was
worth separating them. `evaluate_equality_clause_with` returns `None` at the
first literal it cannot value — an uninterpreted predicate application, say — so
on a clause that carries one, it never reaches a literal the congruence has
already made true, and the clause is deferred and admitted. The width score
counts such a literal as one more open fact and keeps walking, so it reaches the
true one and reports a tautology.

That is a real hole in the shipped entailment filter, and it is the only one.
Measured size: **104 candidates over the whole population.** Reported, closed,
and not a lever.

## Eviction: sound, and 0.16 % of what it examined

`evict_entailed` re-evaluates retained instances against the current congruence
and drops the entailed ones. It is restricted to instances that are not
themselves a top-level positive equality, and that restriction is what makes it
both sound and completeness-preserving rather than merely sound: the matcher's
congruence is generated by exactly those equalities, so a clause `C` that is not
one contributes no merge, every merge justifying `C` survives its removal, and
`ground \ {C} ⊨ C`. The two sets are equisatisfiable, so the sweep cannot cost a
refutation. Without the restriction it would evict unit equalities that are
"entailed" only by their own merge — deleting real facts from the ground check,
which is the `clause_true_self_merged` population above.

It examined 846,617 eligible retained instances and evicted 1,368: **0.16 %**.
Independent confirmation of the census split, from the other direction.

## What this does and does not establish

- **It is not a parity measurement.** No reference was re-run;
  `bench-results/PARITY.md` remains the ledger. z3 4.13.3 was re-run on the same
  32 files at the same budget as an independent reading — 18 `unsat`, 10
  timeout, 4 out-of-memory, **zero disagreements with the declared `:status`**,
  reproducing the attribution note's figure. It is a second opinion, not the
  division's reference (that is cvc5).
- **It does not refute instance selection in general.** It refutes
  *congruence-based relevance ranking over the deferred pool on this
  population*, which is the concrete thing target 1 named. A selection policy
  with a different signal is untouched by this.
- **The census covers the 29 of 32 files that printed one**, and the funnel the
  28-30 that reached an exit; three files abort under the 8 GiB cap before
  either. The `redundant_at_generation` and `scored` totals are therefore lower
  bounds.
- **The residual band is the load-bearing claim** and it is per-reading, not
  pooled: no reading anywhere reported a maximum above 4.

## Where this leaves the three targets

**Target 1 is closed, negatively.** Both its literal form (already shipped, at
528,561 declines) and its actionable residue (1,639 entailed instances, 1,368
evictable) are measured, and neither moves a file.

**Target 2 — restart with a pruned pool — inherits the same problem and should
be re-scoped before it is built.** Its premise was that the ceiling is filled
with inert traffic worth discarding. The pool is not inert in the relevance
sense; it is one or two facts short of a conflict throughout, and 85.6 % of it
cannot be judged by the congruence at all — so "pruned" has no definition here
that this layer can compute. A restart that discarded it and re-matched would
re-derive the same near-conflict instances, because the same triggers over the
same ground set produce them. What a restart would need in order to be different
is a different *trigger* set — which is target 3.

**A fourth target, which the criterion axis surfaced: give the evaluator an
assignment.** The `entail` arm establishes that widening the criterion with the
information the *input* carries buys 1.5 points of blindness, and that the
information cvc5's evaluator actually uses — decided Boolean literals — is
produced by a search this loop runs outside of. Until the criterion can read the
retained CDCL(T) session's assignment, no pruning layer built on it can be
better than blind on 84 % of candidates, whether it prunes early or late.

**Target 3 — trigger selection — is now the only one of the original three the
measurements support**, and this note strengthens the case the attribution note
made for it. Every instance the loop makes is one or two facts from conflicting
and none of them conflicts, on files an independent solver refutes in a median
116 ms. The instances that would close those files are not being *ranked* badly.
They are not being *generated*. 19 of the 32 files carry no `:pattern`
annotation at all, so every trigger on them is ours to choose, and nothing in
the selection layer can compensate for choosing them badly.

There is a second thread worth pulling that this note surfaced without pursuing:
the congruence oracle's blindness to predicate atoms is not only a selection
problem. `clause_false = 0` on every file means no admitted instance ever
conflicts — and on 85.6 % of the pool the thing that would have to conflict is a
predicate literal the equality core does not track. Whether that is a selection
gap or a *reasoning* gap is not settled by anything measured here, and it should
be settled before either target 2 or target 3 is scoped.

## Reproducing it

```sh
cargo build --release -p axeyum-bench --example smtcomp_cli

# any arm, one file; `shipped` is also what an unset or misspelled value gives
AXEYUM_QINST_RELEVANCE=narrow AXEYUM_QPROBE=1 \
  target/release/examples/smtcomp_cli <file> --timeout-ms 24000
# -> QPROBE relevance policy=narrow scored=… declined_wide=… residual_min=…

# the census split that shows the TRUE bucket is self-merged
AXEYUM_FLOODPROBE=1 target/release/examples/smtcomp_cli <file> --timeout-ms 24000
# -> FLOODPROBE cap-census … clause_true_self_merged=… clause_true_by_others=…
```

The funnel is also published to the live-instruments board under
`live_instruments::instrument::QINST_RELEVANCE` — in-flight on every round and
complete at the loop's exits — because 13 of these 32 files never reach an exit
and the printed line dies with the process.

## Registry consequences

- `RELEVANCE_NARROW_RESIDUAL_WIDTH` and `RELEVANCE_EVICT_MIN_GROUND` are new
  bounds and are registered against this note. Neither is a shipped bound:
  `RelevancePolicy::SHIPPED` sets `max_residual_width: usize::MAX` and
  `evict_entailed: false`, so neither is consulted unless an A/B arm is
  selected.
- `RelevancePolicy` itself is **struct-valued**, so — exactly as
  `ONLINE_QUANTIFIER_LIMITS` was on 2026-09-09 — the `config_registry` coverage
  scanner cannot see it: it matches only scalar and `Duration` types. Its arms
  are registered **by hand** and this sentence is the record that they had to
  be. The scanner blind spot is unchanged and is not closed by this entry.
