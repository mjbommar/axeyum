# ADR-2122: `QF_LRA` — implied-bound propagation into the SAT core, and the 24.5 % it can reach

Status: proposed
Index-summary: ADR-2111 named theory propagation the largest lever in `QF_LRA` from a RATIO -- a median **19 theory propagations against 836,531 decisions** on the 23 of 93 undecided rows that reach the online engine -- and **a ratio is not a prize**. This lane measured the prize BEFORE building: a `probe` mode that builds the identical column-bound table and offers nothing, plus a `note_decision` driver hook (the driver is the only party that can tell a BRANCH from a unit propagation, since a theory sees `assert` for both). **The ceiling is 405,738 of 1,654,631 decisions on tracked atoms = 24.5 %, and 7.0 % of ALL decisions**; median per-row share 19.0 %, **min 0.3 %, max 70.5 % -- the spread is the finding** -- and **the two `miplib/pp08a-*` rows, one of them ADR-2111's own median, have `tracked = 0`: not one of their 169,645 and 291,314 decisions is on an atom the theory tracks, so the lever provably cannot reach the division's representative file**. Built anyway, and it works: a COLUMN-bound table rather than a basis-row scan, which is FORCED here rather than chosen -- z3's `is_unit_var` makes `x <= 3` a column bound with **no row at all** (`theory_lra.cpp:807-809,856-857`) while ours makes a slack row per template, so **no problem variable ever carries a bound** and a direct port of `propagate_bounds_for_touched_rows` would have been INERT. Seeds from unit constraints, rounds over the asserted rows at one candidate per row entry per direction, emission when an atom's expression is confined to one side of zero; basis-independent, so the offered sequence does not depend on the last check's pivots. **Three of ADR-2111's citations are corrected, one of which would have cost a successor: z3 does NOT emit at most two implied bounds per row** -- `analyze()` returns at most 2 but that counts DIRECTIONS, and `limit_all_monoids_from_below` (`bound_analyzer_on_row.h:196-220`) calls `limit_j` once per row ENTRY, so a row of length n emits up to 2n; also `try_add_bound` does not exist (`add_bound`, `lp_bound_propagator.h:150-190`) and `:54-80` truncates `analyze()` mid-body. Soundness by a checker sharing NO arithmetic with the producer: every offered literal's reasons plus its own NEGATION go to the simplex, which must refute them -- **904 verified, 0 inconclusive, 0 refuted over 1,000 LCG systems**, floor asserted at 200 so a propagator that goes quiet dies rather than passing by checking nothing; the soundness-negative fixture is a PAIR with the satisfiable arm first; the positive control carries its own negative control. The five z3 differential fuzzes run in **BOTH** arms (15 tests, exit 0 each) because a lever shipping `off` is otherwise exercised by nothing. **A/B, one binary two env values, **600 rows across THREE complete populations -- the pinned `QF_LRA` board, a seeded held-out `QF_LRA` draw disjoint from it, and `QF_LIA`: pinned 107/107 net +0 with 0 movers (arm A re-deriving the board's 107 exactly), held-out 93/92 net -1, `QF_LIA` 127/127 net +0, **0 gains anywhere**, 0 flips, 0 exit-status differences, 307 `:status` comparisons with 0 disagreements** -- and the one mover re-run 3x per arm is **STABLE-LOSS** (3/3 `unsat` off, 3/3 `unknown` on), not ambient. **Implied-bound propagation buys ZERO verdicts and costs +35.4 % / +12.2 % of wall clock on the rows both arms decide.** SHIPS `off`. The mutation run found a guard that was DECORATION -- the self-explanation `continue` was removable with all 38 tests green, because every reason atom is asserted and the target is not -- now a `debug_assert!`; and it found two guards with the SAME five-test kill set, which a new fixture separates (still nested, and the ADR says so). Final run: 39-test baseline, exit 0, killed 5/2/1/6, `--check-anchors` stale=0. The capability ratchet had to be run twice and the first run is kept: it FAILED with a `TIMING REGRESSION [nia_unsat]` at 401.2 ms on a box at load 10.6 whose own reference frames said NOT COMPARABLE for two families; re-run quiet it is **18.8 ms, 12 passed, 0 REGRESSION, 0 NOT COMPARABLE** -- a 21x swing at fixed code. Two runner defects were found and fixed by reading the logs of a run that had already 'succeeded': a list of ABSOLUTE paths made every row UNREADABLE while `AB-DONE ... 0 files` printed on stdout, and a missing list made the launcher SKIP a division and silently reorder the queue; both now refuse. The five exposure divisions are reported **did not run**, never as zero movement.
Index-status: proposed
Date: 2026-09-15

## Context

[ADR-2111] measured the largest lever it did not pull. Over the **23 of 93**
undecided `QF_LRA` rows that reach the online CDCL(T) engine, a median **19
theory propagations against 836,531 decisions** — 24,509 decisions per
propagation, 3.35 M atom visits per propagation. Its conclusion was that theory
propagation here "is not weak, it is absent", and that closing it is the
largest single lever in the division.

This lane built it, measured what it could reach **before** building it, and
scored it.

Branch base: `git merge-base main HEAD` is `3c3ba0eb2`.

Compute: **s5, physical core pairs `5,13` and `6,14`**, and nothing else. Lane
LRA-TRACE had left two shards on those same cores; they were stopped before
this lane took a single timing, and the load was read at **0.00** before the
first sweep rather than inherited from the notice that said so.

## 1. Sizing first — the ceiling is 24.5 % of tracked decisions

The question a propagator has to be sized against is not "how many propagations
does it make" but **"how many of the search's DECISIONS were on an atom the
theory could already have implied"**. Those are the decisions propagation
removes; every other decision it cannot touch however good it is.

That number is not derivable from the theory's own counters. A theory sees
`assert` for a decision and for a unit propagation alike, with nothing to tell
them apart, so the driver has to say. `NativeTheory::note_decision` /
`TheorySolver::note_decision` are that hook — an empty default, called after the
decision literal is enqueued and before it is propagated, so the theory state a
probe reads is the state the decision was taken from
(`crates/axeyum-cnf/src/proof_sat.rs`, the `pick_branch` arm;
`crates/axeyum-solver/src/native_cdclt.rs`, the adapter that translates the
core's variable index into the theory's atom index).

`AXEYUM_LRA_BOUND_PROPAGATION=probe` builds the identical column-bound table and
answers the identical entailment questions, and **offers nothing**. A sizing run
with the propagator ON would count the decisions of a DIFFERENT search — the one
propagation had already changed — which cannot be compared with the thing it is
meant to size.

**Population: the 23 of 93 that reach the engine**, re-derived from ADR-2111's
committed `buckets-93.tsv` by the `decisions` column being present, which is the
same test that lane used. The other 70 die inside `lra.rs` before any online
engine runs and contribute **nothing, not a zero**; a ceiling over 93 would
carry 70 rows of silence in its denominator and would be smaller than the truth
for a reason that has nothing to do with propagation. The list is committed at
`bench-results/lra-propagation-20260915/lists/engine-23.txt`.

```text
rows: 23   counters present: 22   no warm engine (n/a): 1   no theory-layer line: 0

SUM  decisions=5,817,303   tracked=1,654,631   implied=405,738
POOLED share of TRACKED decisions already implied:  24.5 %
POOLED share of ALL decisions already implied:       7.0 %
MEDIAN per-row share of tracked: 19.0 %   min 0.3 %   max 70.5 %
MEDIAN theory_propagations on these rows today: 18.5
```

Both denominators are printed because they answer different questions. A
`QF_LRA` skeleton carries Tseitin variables the theory knows nothing about, and
a decision on one of those is not a decision propagation could have removed. So
**24.5 % is the ceiling on the decisions this mechanism can reach, and 7.0 % is
its share of the whole search.**

`18.5` re-derives ADR-2111's `19` on a different run, on a different tree, under
a different probe — so the gap that lane measured is reproducible and not a
one-run artefact.

### 1.1 Three things the pooled number hides

| file | decisions | tracked | implied | share |
|---|---:|---:|---:|---:|
| `sal/tgc/tgc_io-safe-13` | 746,140 | 192,020 | 132,693 | **69.1 %** |
| `sal/carpark/Carpark2-ausgabe-8` | 35,939 | 2,905 | 2,048 | **70.5 %** |
| `sal/tgc/tgc_io-safe-20` | 470,143 | 118,222 | 76,693 | 64.9 % |
| `sal/pursuit/pursuit-safety-16` | 200,453 | 24,935 | 15,798 | 63.4 % |
| … | | | | |
| `_half_2.i_3_6_2.bpl_7` | 426,042 | 100,385 | 264 | **0.3 %** |
| `miplib/pp08a-1000` | 291,314 | **0** | 0 | **n/a** |
| `miplib/pp08a-7349` | 169,645 | **0** | 0 | **n/a** |

**The spread is the finding, not the mean.** Propagation is not a uniform tax on
this population: it is most of the search on the `sal/*` rows and essentially
nothing on `_half_2`. A per-row A/B has to be read against that, because a
division-level `net +0` over a population this heterogeneous is compatible with
large movement in both directions.

**Two rows have `tracked = 0`.** `miplib/pp08a-1000` and `pp08a-7349` take
291,314 and 169,645 decisions and **not one of them is on an atom the theory
tracks**. Implied-bound propagation cannot move those files at all, and no
amount of it will. `pp08a-7349` is ADR-2111's own median row, and it is the one
this lever provably cannot help — which is exactly the kind of thing a census
median cannot tell you and a per-row table can.

**One row keeps no warm engine at all** (`n/a`, the Fourier–Motzkin fallback).
Its counters are `None` and not zero, and it is counted separately rather than
folded into either side. This is a real limitation of the reporting, not of the
mechanism: the ADR-2122 counters ride on the same `Option<TheoryEngineCounters>`
the simplex counters do, so a theory without a simplex reports nothing about
propagation even though its propagator ran.

### 1.2 What the number is NOT

The absolute `decisions` counts here are **lower** than ADR-2111's on the same
files — `pp08a-7349` reads 169,645 against 836,531 — because the probe spends
real time building the table and a budget-bound search therefore takes fewer
decisions inside the same 24 s. **The transferable quantity is the SHARE**, and
that is what is quoted above. All 23 rows still answer `unknown` under the probe,
so nothing was decided or lost by measuring.

### 1.3 The cost, clock-free, and it is not small

| counter | median per row | sum over 22 |
|---|---:|---:|
| `implied_bound_passes` | 140,606 | 3,890,798 |
| `implied_bound_rows_scanned` (coefficients) | 252,523,020 | 7,455,294,715 |
| `implied_bounds_derived` | 8,295,660 | 374,077,135 |

A median 140,606 passes examining 252 M constraint coefficients and installing
8.3 M column bounds. **That is what the A/B has to earn back**, and it is stated
before the A/B rather than after it.

These three are the *instrumented* cost — what the propagator did — and not a
profile. Nothing here says which part of it is expensive; §5.1 is where one
part was removed on the strength of an explicit estimate, labelled as an
estimate.

## 2. The design claims, with `file:line` on both sides

Verified against `references/z3` at `e18d63bda04fcab8240eb55314d567db3e43d540`
(2026-09-08) and `references/cvc5` at `1689f13331f7543801f82d9dcbcaac2f70a26781`
(2026-09-03). Every range was re-printed with `sed -n` before being written
down. The full table is committed at
`bench-results/lra-propagation-20260915/reference-citations.md`.

### 2.1 Three of ADR-2111's own citations are wrong, and one of them matters

This is recorded first because a successor reading only ADR-2111 would build the
wrong thing.

1. **`try_add_bound` does not exist in z3.** `grep -rn "try_add_bound" src/`
   returns nothing. The entry point is `lp_bound_propagator::add_bound`,
   `src/math/lp/lp_bound_propagator.h:150-190`.
2. **`bound_analyzer_on_row.h:54-80` is the wrong range** — it truncates
   `analyze()` mid-body. Correct: `:55-60` (`analyze_row`) and `:64-87`
   (`analyze()`).
3. **"z3 yields at most TWO implied bounds per row" is FALSE, and this is the
   one that would have cost a lane.** `analyze()` returns at most 2, but that
   counts propagation DIRECTIONS (row-max and row-min), not bounds. When every
   column in the row carries the relevant bound — the common case —
   `limit_all_monoids_from_below` (`:196-220`) and `..._from_above` (`:149-172`)
   each call `limit_j` **once per row entry**, so a row of length *n* emits up
   to **2n** `add_bound` calls. Only the singleton-unbounded paths
   (`:223-249`, `:252-277`) emit exactly one each. The de-duplication to "at
   most one lower and one upper per COLUMN" happens later, in `add_bound`.

   A propagator written to the two-per-row reading would derive a small fraction
   of what z3 derives and would then be measured against z3 and found wanting
   for a reason that is in the brief rather than in the code. This lane's rounds
   emit one candidate bound per row entry per direction, which is z3's actual
   shape.

4. `theory_lra.cpp:2841` (`mk_bound_axioms`) and `:2963` (`flush_bound_axioms`)
   are **correct**.

### 2.2 z3 — the mechanism

| claim | `file:line` |
|---|---|
| state: `m_improved_lower_bounds` / `m_improved_upper_bounds` map a COLUMN to an index into `m_ibounds`, so at most one pending implied bound per column per side | `src/math/lp/lp_bound_propagator.h:16-32`, reset at `:117-122` |
| `add_bound` keeps a bound only if strictly tighter than the pending one, or equal-and-strict where that was non-strict | `src/math/lp/lp_bound_propagator.h:150-190` |
| the "is this worth deriving" filter is a question about the SAT CORE: keep only if some UNASSIGNED arith atom on that variable would be implied | `src/smt/theory_lra.cpp:2422-2437` |
| the explanation is a CLOSURE joining one bound-witness dependency per non-target row entry | `src/math/lp/bound_analyzer_on_row.h:298-321`; held at `src/math/lp/implied_bound.h:36-40` |
| **z3's implied-bound explanation carries NO Farkas coefficients** — flattened to constraint ids, each given a hardcoded `mpq(1)`, with an in-tree TODO saying so | `src/math/lp/lar_solver.h:219-223` |
| per-row analysis, two directions | `src/math/lp/bound_analyzer_on_row.h:64-87` |
| strictness: count summands whose delta-rational bound has a nonzero infinitesimal part, minus your own | `:113-124`, `:166,169,212` |
| the delta component is LOST crossing into `theory_lra`, and z3 refuses to propagate at all rather than strengthen `x ≥ r − ε` into `x > r` | `src/smt/theory_lra.cpp:2477-2487` |
| touched-row pass, then reset | `src/math/lp/lar_solver.h:283-304` |
| rows marked touched: bound change, PIVOTING, new row, replay on pop | `lar_solver.cpp:1266-1275,1729-1733,2003,584-589`; `lp_core_solver_base_def.h:275-281` |
| the two row-skipping guards, one disjunction | `src/math/lp/lar_solver.h:112-121`, predicate at `:114` |
| `max_row_length_for_bound_propagation` default **300** | `src/math/lp/lp_settings.h:245` |
| the big-coefficient skip, unconditional | `lar_solver.cpp:379-384`; `src/util/rational.h:84-86` |
| `propagate_bounds_with_lp_solver` runs from `propagate_core()` on the FEASIBLE branch, once per SMT propagation round — **not** from `final_check_eh` | `theory_lra.cpp:2311-2328`, body `:2400-2420`, callback `:4611-4616` |
| implied bound → SAT literal; the explanation is materialised ONCE for the first assigned literal and reused | `theory_lra.cpp:2503-2542` |
| the justification is `ext_theory_propagation_justification` — antecedent literals, not a proof; the clause branch is dead (`if (false && …)`) | `theory_lra.cpp:2617-2642` |
| **no per-round count cap**: the throttle is a conflict threshold plus `m_unassigned_bounds[v] == 0` | `theory_lra.cpp:3408-3410,2387-2393,2499-2502` |
| bound ORDERING axioms as SAT clauses, against at most FOUR sorted neighbours | `theory_lra.cpp:2841-2894`, clauses at `:2897-2932` |

### 2.3 cvc5 — the same structure, tighter caps, real Farkas coefficients

| claim | `file:line` |
|---|---|
| `propagateCandidates` is the LEGACY path; `--new-prop` defaults true | `src/theory/arith/linear/theory_arith_private.cpp:4397-4415` |
| `propagateCandidateRow` dispatches on the row's BOUND COUNT: all bounded → `attemptFull`, one short → `attemptSingleton` | `:5456-5491` |
| `attemptFull` emits one candidate per row entry — the same shape as z3's all-bounded direction | `:5240-5263` |
| the candidate set is `d_updatedBounds`, populated at the three `Assert*` tails and converted to rows once per round, drained destructively | `theory_arith_private.h:639-647`; `.cpp:636,805,916`, `:5493-5518`, `:5124-5144` |
| **cvc5's explanations DO carry Farkas coefficients** (index 0 the implied constraint's, *i+1* `explain[i]`'s), collected only under `produceProofs` | `linear_equality.cpp:593-607,647-674`; `theory_arith_private.cpp:5351-5362` |
| and they become a real proof rule | `ProofRule::MACRO_ARITH_SCALE_SUM_UB`, `theory_arith_private.cpp:5409` |
| two delivery routes by row length: short rows become a CLAUSE, long rows a queued propagation | `:5363-5442` |
| `arithPropagateMaxLength` default **16**, and PROBABILISTIC above it | `src/options/arith_options.toml:113-119`; `theory_arith_private.cpp:5466-5471` |

**The two references are 19× apart on the row-length cap** — z3 refuses above
300, hard and unconditionally; cvc5 above 16, and only probabilistically. That
is not a rounding difference, it is two bets about whether wide-row propagation
pays. This lane took z3's number and registered it in `config_registry` as a
CHOICE with both values beside it rather than as a fact.

### 2.4 Ours, before this lane

`LraTheory::propagate_bounds` (`crates/axeyum-solver/src/lra_online.rs`) compares
bounds on the same canonical linear **FORM**: `x + y ≤ 3` entails `2x + 2y ≤ 8`
because the two share a form id, and that is the whole of what it can do.
`x ≤ 1` and `y ≤ 2` entailing `x + y ≤ 5` is invisible to it, because the three
atoms bound three different forms. ADR-2111's `propagatable_atoms` filter is
exactly output-preserving over that mechanism and does not widen it.

## 3. What was built, and the one structural decision in it

### 3.1 A COLUMN table, not the tableau's rows — and why that is forced here

z3 propagates over the rows of its **current basis**. That works there because a
single-variable atom `x ≤ 3` creates **no row at all**: `is_unit_var`
short-circuits and the atom becomes a column bound on `x`
(`theory_lra.cpp:807-809,856-857`).

Ours makes one slack row per constraint template, `x ≤ 3` included
(`Constraint::row`, `build_simplex_engine`). So in this encoding **no problem
variable ever carries a bound**: every bound lives on a slack, and every
pristine row relates one bounded slack to a set of unbounded problem variables.
A scan of those rows derives nothing at all. That is not a weakness of the
propagator; it is a property of the encoding, and it is why a direct port of
z3's `propagate_bounds_for_touched_rows` would have been **inert** — the same
failure mode ADR-2111 caught in its own `TableauReserve` lever, one level down.

`ImpliedBounds` supplies the missing half:

1. **Seed.** An asserted UNIT constraint gives its one variable a column bound
   directly, explained by that one atom. `−x − 3 ≤ 0` is `x ≥ −3` — a LOWER
   bound, because dividing by a negative coefficient flips the relation, and
   the sign is read explicitly rather than inferred from the value.
2. **Rounds.** Every asserted row bounds each of its variables from the others'
   column bounds: from `a·xⱼ + rest ≤ 0` follows `a·xⱼ ≤ −inf(rest)`, strict
   when the row is **or** when the infimum is not attained. One candidate bound
   per row entry, per direction — z3's actual shape (§2.1 item 3).
3. **Emission.** An atom is entailed when the interval its own expression is
   confined to lies wholly on one side of zero, and the explanation is the union
   of the `why` sets of the bounds actually used.

This is z3's `bound_analyzer_on_row` arithmetic over this engine's constraint
TEMPLATES rather than over its basis. It is therefore **basis-independent**: the
offered sequence does not depend on which pivots the last feasibility check
happened to make, which is a determinism property the basis form would not have
had.

### 3.2 Derived bounds are not persisted, and that is deliberate

Seed bounds have an undo log positionally aligned with `live`, exactly as
`bound_log` does for the form tables, so `pop` restores them by truncation.
Derived bounds are **scratch**, rebuilt from the seeds every pass. They depend
on other derived bounds, so undoing one on `pop` would mean undoing a dependency
graph — and a structure whose invalidation is hard to get right is where a wrong
answer hides. Recomputing is `O(asserted rows × rounds)` and runs only when the
touched filter says something moved.

### 3.3 The touched filter is a counter, not a flag

`ImpliedBounds::epoch` is bumped once per live constraint pushed and once per
pop that truncates; a pass runs only when `epoch != scratch_epoch`. It is a
counter rather than a length comparison for one reason: **a pop followed by an
assert can leave `live` the same LENGTH with different CONTENT**, and a length
test would then read a stale scratch table as current — which `note_decision`
would report as a decision that was "already implied" when it was not.

### 3.4 What `off` costs, stated rather than claimed

`off` allocates no table, builds no `var_atoms` index, and the pass returns on
its first line. It is **behaviourally identical to `main`, not byte-identical**,
and the difference is worth naming because a claim of byte-identity would be
false: the driver now calls `note_decision` on every branch, which in the `off`
build is a variable→atom lookup, a virtual call, and an `Option` test that finds
`None`. Three loads per decision, on a path that takes hundreds of thousands of
them — real, and far below anything the 24 s envelope can resolve.

What makes arm A a BASELINE rather than something near one is therefore not that
argument; it is the measurement: **arm A must re-derive the committed board's
`QF_LRA` figure of 107**, and §5 reports whether it does.

### 3.5 The caps, and where each number comes from

All five are in `config_registry` with both references' values beside them.

| constant | value | provenance |
|---|---:|---|
| `MAX_IMPLIED_BOUND_ROW_LENGTH` | 300 | **z3 verbatim** (`lp_settings.h:245`). cvc5's is 16. |
| `MAX_IMPLIED_BOUND_ROUNDS` | 2 | ours. Exact-rational tightening over a CYCLE of rows does not converge — it approaches a limit one strictly-tighter step at a time — so a fixpoint loop would not terminate. Not measured as optimal; round 3 is unpriced. |
| `MAX_IMPLIED_BOUND_EXPLANATION` | 16 | ours. An explanation is a clause the core learns and carries. Neither reference has a comparable number. |
| `MAX_IMPLIED_BOUNDS_PER_PASS` | 4,096 | ours, a belt on the rounds' braces. Neither reference has a counterpart; both bound the work by what CHANGED instead. |
| `MAX_IMPLIED_BOUND_PROPAGATIONS_PER_CALL` | 256 | ours, and free for the same structural reason as `MAX_BOUND_PROPAGATIONS_PER_CALL`: the driver runs propagation to a FIXPOINT, so a capped pass defers work rather than discarding it. |

## 4. Soundness is the method

A propagated literal is sound iff its explanation clause `¬⋀why ∨ lit` is a
valid implication over ℝ. Four independent things check that, and none of them
is the producer agreeing with itself.

### 4.1 The checker does not share arithmetic with the producer

`LraTheory::implied_propagation_is_valid` hands the reason literals' own
constraints **together with the NEGATION of the propagated literal** to
`simplex::feasible_within_sparse` and requires `Infeasible`. That engine shares
no code with the interval reasoning in `extremum`, so a sign error in one is not
a sign error in the other. It answers `Some(true)` / `Some(false)` /
`None` (the engine declined) and the three are kept distinct — an inconclusive
check is not a passing one.

A checker that recomputed what the producer computed would agree with the
producer's own sign errors. That is the shape this repository has been caught by
and it is why the check is routed through the decision procedure instead.

It runs in a `debug_assert!` on every offered literal, and as a test over a
generated population.

### 4.2 The generated population, with its denominator

`every_offered_implied_bound_explanation_is_a_valid_implication` runs 1,000
LCG-generated linear systems over 2–4 variables with 3–8 atoms of mixed
relations, asserts a random prefix, and checks every literal the propagator
offers:

```text
verified = 904    inconclusive = 0    refuted = 0
```

The asserted floor is **200**, not the measured 904 and not `> 0`: `> 0` alone
would let a propagator that went almost completely silent still pass, and
pinning the exact count would fail on any harmless generator change. **An empty
result from a checker that never pointed at its subject is indistinguishable
from a strong negative**, which is precisely what the floor exists to refuse.

### 4.3 The soundness-negative fixture is a PAIR, satisfiable arm first

The one way `unit_col_bound` can be wrong that nothing else catches is the
SIDE. `a_seed_bound_on_the_wrong_side_would_propagate_into_a_satisfiable_system`:

- **`x ≥ −3 ∧ x > 0` is FEASIBLE** (`x = 1`), and `final_check` says so. This arm
  is first, so the refutation below is read as a distinction the engine draws
  and not as a blanket refusal.
- From **`x ≥ −3` alone the propagator must refute `x ≤ −5`**, explained by that
  one literal, and the explanation must verify through §4.1.
- `x ≥ −3 ∧ x ≤ −5` is INFEASIBLE and the engine reports it.

Reading the seed as an UPPER bound (`x ≤ −3`) makes the second propagation
**disappear** — `−x` then has no upper bound at all — so the mutation is caught
by an absence, and the first arm is what shows the absence is not the whole
mechanism being off.

### 4.4 The positive control carries its own negative control

`implied_bounds_propagate_an_atom_no_form_bound_could` asserts `x ≤ 1` and
`y ≤ 2` and requires `x + y ≤ 5` to be offered with the explanation
`{atom 0, atom 1}` — **and then runs the pre-existing form-level scan on the
same state and requires it to offer nothing.** Without that half the test would
pass over a mechanism that is a second route to something we already had, which
is worth nothing.

### 4.5 The pre-merge gates, run in BOTH arms

The five z3 differential fuzzes are the only checks in this repository that
compare our verdicts against an independent solver, and they compile to **zero
tests** without `--features z3` — the silent-inertness trap. Counts confirmed
nonzero every time.

**They are run twice, and that is the point.** A lever that ships `off` leaves
the new path exercised by nothing: running the fuzzes only in the default arm
would be a gate that structurally cannot see this change. So every suite runs
again with `AXEYUM_LRA_BOUND_PROPAGATION=on`, which is the arm where the
soundness risk actually lives.

| suite | tests | `off` | `on` |
|---|---:|---|---|
| `difference_logic_differential_fuzz` | 4 | ok | ok |
| `qf_lia_differential_fuzz` | 4 | ok | ok |
| `qf_lra_differential_fuzz` | 5 | ok | ok |
| `qf_uflra_differential_fuzz` | 1 | ok | ok |
| `simplex_lra_fallback_differential` | 1 | ok | ok |
| **total** | **15** | **exit 0** | ****exit 0**** |

The suites are `qf_lra_differential_fuzz` (5), `qf_lia_differential_fuzz` (4),
`difference_logic_differential_fuzz` (4), `qf_uflra_differential_fuzz` (1) and
`simplex_lra_fallback_differential` (1). Note what the shape of that list says:
**difference logic had no oracle coverage at all until 2026-09-09**, and it is a
COMPLETE decider that runs FIRST in the dispatch ladder, so a wrong answer there
is caught by nothing downstream. It is in this gate for that reason and not
because this change touches it.

**The rest of the gate list**, each with a nonzero count confirmed:

| gate | measured |
|---|---|
| `--lib --features full lra` | **141 passed**, 0 failed |
| `--lib --features full simplex` | **41 passed**, 0 failed |
| `--lib --features full config_registry::tests` | **18 passed**, 0 failed |
| the 21 dispatch/reason integration suites | all green, every count nonzero (7, 10, 20, 11, 12, 3, 3, 12, 12, 9, 6, 6, 6, 6, 7, 18, 13, 2, 20, 6, 7) |
| `--lib --features full -- --skip reconstruct::` | **1,536 passed**, 0 failed, 320 filtered (399.7 s) |
| `cargo check --workspace --all-targets` | rc 0, **0 errors** |
| clippy `-D warnings`, solver + bench + cnf, `--all-targets --features full` | rc 0, **0 errors** |
| `cargo fmt --all --check` | ok |
| `mutation_controls.py --check-anchors` | 146 suites, 1,086 anchors, **stale = 0** |
| `scripts/check-links.sh` | all links ok |
| `progress_frontier --features full -- --test-threads=1` | **12 passed**, 0 failed; **0 REGRESSION, 0 NOT COMPARABLE** |

### 4.6 The capability ratchet had to be run twice, and the first run is why

The first `--nocapture` run **failed**, exit 101, with a
`TIMING REGRESSION [nia_unsat]`: 401.2 ms calibrated against a committed ceiling
of 115.6 ms. Its own reference-frame lines say what it was:

```text
NOT COMPARABLE [bv_reduction]: throughput moved 100 % during the sweep
  (142.9 ms -> 285.2 ms) — the ratchet below is not enforced on it.
NOT COMPARABLE [lia_cuts]: throughput moved 39 % during the sweep
reference frame [nia_unsat]: load 10.61 -> 10.76, calibration 139.9 ms vs 127.0
```

The box was at load 10.6 with this lane's own mutation sweep and two peer lanes'
cargo jobs on it. Re-run with nothing of this lane's on the machine:

```text
FRONTIER bv_reduction = 35 (baseline 30), PROGRESS (+5, ratchetable)
FRONTIER lia_cuts     = 35 (baseline 26), PROGRESS (+9, ratchetable)
FRONTIER nia_unsat    = 40 (baseline 40)
FRONTIER nra_degree   = 40 (baseline 40)
FRONTIER string_bound = 40 (baseline 8),  PROGRESS (+32, ratchetable)
TIMING   nia_unsat    = 18.8 ms (ceiling 115.6 ms)
12 passed; 0 failed — 0 NOT COMPARABLE, 0 REGRESSION
```

`nia_unsat`'s 401.2 ms became **18.8 ms**, a 21× swing at fixed code. The first
run is recorded rather than deleted because it is the reference-frame problem in
one page: the ratchet's verdict and the ratchet's own comparability marks
disagreed, and the marks were right. **No baseline is raised from either run** —
the clean one labels its three PROGRESS results `ratchetable`, and this lane
leaves them alone; raising a frontier baseline is not this lane's change to
make.

**The 21 suites are read out of `hooks/pre-push` at run time, not copied.** A
copied list measures the maintainer's memory of what the hook runs, and a
shrinking list then reports as a passing one; `run-gates.sh` extracts the list
and refuses if it finds fewer than 15, so an extraction that silently matched
nothing cannot look like a clean sweep.

## 5. The A/B

### 5.0 One binary, two env values — and where the vacuity guard moved

[ADR-2100]'s runner refuses unless its two BINARIES hash differently, because
two identical arms produce a perfect zero that looks exactly like agreement.
This change is a lever, so the same risk exists in a different place: **two arms
that differ only in an environment variable the binary never READS are equally
vacuous and equally invisible.** The guard moved rather than being dropped —
`ab-run.sh --mechanism-check` runs one file under both values and requires
`implied_bound_passes` to be absent-or-zero in A and NONZERO in B.

```text
mechanism-check: off=0 on=17494
mechanism-check OK: the lever moves the engine on this file
```

One binary also removes a confound the two-binary form has: arm A here is the
same machine code as arm B, so a difference cannot be a codegen or layout
accident.

### 5.1 The run was restarted once, and the reason is in §1.3 rather than in a result

The first A/B was stopped part-way and re-run on a rebuilt binary. **The change
that caused it came out of the SIZING table, which was published and committed
before the A/B started**, not out of the A/B's own partial numbers — no
aggregate of the partial run was computed, and the change is a pure performance
fix with no effect on what is offered.

`ImpliedBounds::reset_scratch` walked `0..nvars` once per pass. §1.3 measured a
median **140,606 passes**; ADR-2111's shape census measured a median **1,706
variables** on the undecided half. Multiplying those gives about **240 M slot
reads** per file to copy a handful of bounds — the same order as the 252 M
coefficient reads the row analysis itself does.

**That product is an ESTIMATE, not a measurement, and it is labelled as one
here.** The two medians come from different populations — 22 rows' pass counts
against 93 rows' variable counts — so they do not multiply into a fact about any
single file, and no profile was taken. What it is enough for is a decision: a
per-pass loop over every variable, run six figures of times, is work with no
arithmetic in it, and removing it cannot make the mechanism worse. It now walks
only the variables that have ever held a seed bound.

The A/B therefore measures the version that ships. Measuring the other one would
have reported a cost that does not exist — and would have reported it as the
propagator's, which is the wrong attribution as well as the wrong number.

### 5.2 600 rows across three complete populations

One binary (`935ad9cd…`), two env values, arms back to back on the same file on
the same pinned core, arm order alternating per file, 24 s / 8 GiB.

| population | rows | A | B | net | gain | LOSS | FLIP | A rc≠0 | B rc≠0 | cmp | DIS |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `QF_LRA` pinned | 200 | 107 | 107 | +0 | 0 | 0 | 0 | 0 | 0 | 97 | 0 |
| `QF_LRA` held-out | 200 | 93 | 92 | **−1** | 0 | **1** | 0 | 0 | 0 | 86 | 0 |
| `QF_LIA` | 200 | 127 | 127 | +0 | 0 | 0 | 0 | 0 | 0 | 124 | 0 |
| **TOTAL** | **600** | **327** | **326** | **−1** | **0** | **1** | **0** | **0** | **0** | **307** | **0** |

- **Arm A re-derives 107 on the pinned draw**, which is the committed board's
  `QF_LRA` figure exactly and the number [ADR-2111] is written against. The base
  arm is the baseline, not something near it.
- **0 soundness disagreements against the files' declared `:status`, at a
  comparable denominator of 307**, published beside the count.
- **0 flips and 0 exit-status differences** anywhere, on any population.
- **0 gains.** Not "few": none, on 600 rows.
- **`QF_LIA` is the exposure division that matters most** — it drives the same
  simplex — and it moves nothing in either direction.

### 5.3 The one mover is a STABLE-LOSS, not ambient

One raw mover, re-run **3× per arm** on one pinned core pair with the arms
alternating within the passes:

```text
file                                                    A1     A2     A3     B1       B2       B3       verdict
clock_synchro/clocksynchro_7clocks.worst_case_skew…    unsat  unsat  unsat  unknown  unknown  unknown  STABLE-LOSS
```

Three for three in both directions. This is not the 1–1.5 % ambient flip rate
these boxes carry — ADR-1966 had 11 of 18 movers vanish under exactly this
recheck, and this one does not. **1 STABLE-LOSS, 0 STABLE-GAIN, 0 UNSTABLE.**

### 5.4 What it costs on the files both arms decide

Verdicts are not the only axis, and the time axis is where the §1.3 cost
actually lands:

| population | rows both decide | A total | B total | delta |
|---|---:|---:|---:|---:|
| `QF_LRA` pinned | 107 | 81,478 ms | 110,300 ms | **+35.4 %** |
| `QF_LRA` held-out | 92 | 100,385 ms | 112,589 ms | **+12.2 %** |

The pinned median is **unchanged** at 107 ms, and 15 of 107 rows are more than
10 % slower under `on` against 1 more than 10 % faster. So the cost is not a
uniform tax either — it is concentrated on the rows where the propagator has
something to chew on, which is the same shape §1.1's spread showed.

### 5.5 The exposure divisions: one ran, four did not

`QF_LIA` ran to **200 of 200** and is in the table above: `net +0`, 0 movers, 0
disagreements over 124 comparisons. It is the exposure division with the
strongest claim on this change, because it drives the same simplex.

**`QF_UFLRA`, `QF_UFLIA`, `QF_IDL` and `QF_RDL` DID NOT RUN.** They were queued
behind the two `QF_LRA` draws and `QF_LIA` on the same two pinned core pairs and
had not started when this lane closed. They are reported as **did not run**, not
as zero movement: a division with no rows is not a division with no movement,
and ADR-2111's own exposure arm had to make exactly this distinction after
reporting four empty divisions.

One `QF_LIA` attempt was **discarded rather than reported**, and it is worth
recording why: clearing a core pair for the mover recheck, this lane ran
`pkill -TERM -f smtcomp_cli.arm-c`, a pattern that matched **both** shards'
solvers and killed the one it did not mean to. The 48 rows that shard had
produced were deleted and `QF_LIA` was re-run whole. A partial from a run
stopped by the measurer is not a measurement of anything, and the repository's
own rule — never `pkill` on a broad pattern — is the one that was broken.

**That gap does not change the decision**, because the decision is already
`off` on the treatment division's own evidence, and `off` is the shipped
default. It would matter for a decision to ship `on`, and that decision is not
being made.

The lists, the runner and the launcher are committed, so a successor resumes
rather than rebuilds: `launch-ab.sh <shard> <cores> <bin>` picks up any job
whose output file is absent and refuses the whole shard if a list is missing.

## 6. The mutation run, and the guard it found was decoration

`scripts/tests/mutation_controls.py lra-implied-bound-propagation`, baseline
green at **38 tests**, filtered to `lra_online::tests` rather than to one test so
a kill count is a claim about a population. `--check-anchors`: 146 suites, 1,086
anchors, **stale = 0**.

### 6.1 The first run found a SURVIVOR, and it is reported rather than removed

The fourth guard was a `continue` refusing a literal explained by itself.
**Deleting it left all 38 tests green.** That is a real finding: the guard is
unreachable, because every atom in a `why` set came from a bound installed by a
LIVE constraint and is therefore assigned, while the candidate atom reached that
line only because it is NOT assigned. A `continue` that cannot fire, shaped like
a soundness filter, is worse than no filter — it is a line a reader counts as
protection.

It is now a `debug_assert!` stating exactly that invariant, and the mutation
suite watches a guard that is real instead (the skip for an atom the search has
already assigned).

### 6.2 The second run, and the second thing it said

Baseline green at **39 tests**; every mutation `killed N`, the harness's only
outcome that supports a coverage claim; the run exits **0**.

| guard removed | kind of damage | killed |
|---|---|---:|
| one bound dropped from every explanation | **soundness** | 5 |
| the side a negative coefficient puts the unit bound on | **soundness** | 2 |
| the attainment flag a strict bound clears | strictness | **1** |
| the guard skipping an atom the search has already assigned | no-op flood | 6 |

**Only the third kills exactly one**, and that is reported rather than
engineered. The rule this repository keeps — delete one guard, require exactly
one test to die — exists because six of seven guards in one suite were removable
with everything still green, since they all rejected through one shared check.
The property it protects is that distinct guards have distinct CONSUMERS, and a
mutation constructed to hit exactly one number is the opposite of what the rule
is for.

The first run failed that property outright: **the explanation-drop and the
assigned-atom skip killed the same five tests**, so no test in the suite could
tell those two guards apart.
`the_pass_never_offers_an_atom_the_search_has_already_assigned` was written for
exactly that — it asks only about the atoms and never about the explanations.
The sets are no longer identical.

**They are still nested, and that is stated rather than smoothed over.** The
explanation-drop's five are a proper SUBSET of the skip's six: the new test
separates them in one direction only, and no test in this suite dies on the
explanation drop while surviving the skip. A guard whose kill set is contained
in another's is weaker evidence than one with a disjoint set, and the honest
reading is that these two guards are separated but not independently witnessed.

The explanation-drop mutation is the one this ADR exists to be checked against:
the literal it offers is still *correct*, only its justification is short, so
**no verdict comparison and no propagation count can see it**. The five tests
that die are the ones that read the explanation — including the simplex-backed
checker over the 1,000-system population, which is the only one that would still
have caught it if every hand-written fixture had been deleted.

## 7. Decision

**The lever ships `off`, and the mechanism ships with it.**

Against the criteria in §7.1, written before the numbers:

1. **0 soundness disagreements** at a comparable denominator of 183 — **met**.
2. **0 flips** — met. **0 stable losses on the pinned draw** — met (0 movers at
   all). Pinned `net +0`.
3. **0 stable losses on the HELD-OUT draw — NOT MET.** One, and the 3× recheck
   says it is real: 3/3 `unsat` under `off`, 3/3 `unknown` under `on`.
4. **`QF_LIA` ran to 200 of 200 and moves nothing** — `net +0`, 0 movers, 0
   disagreements over 124 comparisons — so the shared simplex is not
   regressed by the propagator being available. `QF_UFLRA`, `QF_UFLIA`,
   `QF_IDL` and `QF_RDL` **did not run**.

Criterion 3 alone settles it. `AXEYUM_LRA_BOUND_PROPAGATION` stays `off`.

### 7.2 The result is a measured negative, and it is the useful kind

**Implied-bound propagation buys ZERO verdicts on `QF_LRA` at 24 s — 0 gains
over 600 rows across three complete populations — and costs one file and 12–35 % of the wall clock on what both
arms decide.** That is not a weak positive that needs more tuning to become a
strong one; it is a clean negative on the axis the division is scored on.

It is worth stating why it is not a surprise in hindsight, because the sizing in
§1 said most of it before the code was written and the ADR is the place that has
to admit it:

- **The ceiling was 24.5 % of TRACKED decisions, which is 7.0 % of all of
  them.** A 7 % reduction in decisions on a search that is losing by a factor is
  not a verdict.
- **The two rows ADR-2111 made its median were `tracked = 0`.** `pp08a-7349`
  and `pp08a-1000` spend 169,645 and 291,314 decisions and not one on an atom
  the theory tracks. The lever cannot reach the division's own representative
  file, and §1.1 said so.
- **The spread, not the mean.** 0.3 % to 70.5 %. A mechanism that is most of the
  search on four `sal/*` files and nothing on the rest does not move a
  200-file board.

What the lane got wrong, and it is the part worth carrying forward: **ADR-2111
ranked this as "the largest single lever in the division" from a RATIO —
836,531 decisions per 19 propagations — and a ratio is not a prize.** The
number that sizes a lever is how many of those decisions the lever could
actually have removed, and nobody had measured it. Measuring it took one
env-gated probe and one driver hook, and it would have re-ordered the work.

### 7.3 What ships anyway, and why it is not dead code

- **The `note_decision` hook and the six counters.** They are what turned "the
  largest lever" into a number, and they are the instrument the NEXT propagation
  lever has to be sized against too. They are diagnostic-only and cost three
  loads per decision in the `off` build.
- **The propagator itself, behind the lever.** It is correct, it is checked by
  an engine that shares no arithmetic with it, and it is the thing bound-AXIOM
  generation (§8) would be measured against. Deleting it would mean rebuilding
  it to answer the next question.
- **`ImpliedBounds::probe`**, which measures a ceiling without changing the
  search that produced it. Nothing else in the tree can do that.

The honest risk of shipping a default-off lever is the one [ADR-2055] names: a
path defaulting `off` is exercised by no gate. That is why the five z3
differential fuzzes run in BOTH arms here (§4.5) and why the mutation suite
(§6) targets the propagator rather than the route.

### 7.4 What would change the answer

Not tuning. The three caps that could be loosened — rounds, explanation size,
row length — all buy more propagations, and more propagations of a mechanism
that bought 0 verdicts is more cost. What would change the answer is a different
mechanism on the same gap:

1. **Bound-AXIOM clauses** (§8). z3 moves the unate half OUT of the theory
   entirely; this lane moved it *into* a better theory scan, which is the more
   expensive of the two places to do it.
2. **One row per distinct compound term, unit atoms as pure column bounds**
   ([ADR-2111] item 5, `theory_lra.cpp:807-809,856-857`). That is the change
   that would make a basis-row propagator possible here at all, and §3.1 is the
   measurement saying why: in this encoding no problem variable carries a bound.
3. **"Model did not replay"** ([ADR-2111] item 2), which is what stops an
   admitted file paying off at all, and which no amount of propagation touches.

### 7.1 The criteria, written before the numbers

The ship criterion is not "net ≥ 0". It is, in order:

1. **0 soundness disagreements** against the files' declared `:status`, at a
   comparable denominator that is printed rather than implied.
2. **0 stable losses and 0 flips** on the pinned `QF_LRA` draw, where "stable"
   means the 3×-per-arm recheck agrees — a raw mover is not a finding, and
   ADR-1966 had 11 of 18 vanish under exactly this recheck.
3. **0 stable losses on the HELD-OUT draw too.** The pinned list is the
   population every number in [ADR-2111] and on the board was measured on, so an
   A/B on it is an A/B on the training set.
4. **No regression in the five exposure divisions**, each with its own
   denominator, and a division with no rows reported as **did not run** rather
   than as zero movement.

Anything short of all four ships `off`, and `off` is the default the code
already carries.

## 8. What this lane did not do

**The cold re-solve — ADR-2111's second claim — was NOT taken**, and it is named
here with what is known about it rather than left implied. `cube_simplex_calls =
651` with `cube_matrices = 0` on `_standard_init5_ground.i_3_2_2.bpl_7.smt2` is
651 simplex solves from scratch, one per SAT model, against four references that
all keep the basis across backtracking. That is a separate mechanism in a
separate route (the OFFLINE lazy-SMT loop in `lra_route.rs`, not the online
engine this ADR changes), it has its own budget, and this lane's compute went to
sizing and scoring the first lever properly rather than half-building two.

Also not taken, and still the largest remaining piece of ADR-2111's claim 2:
**bound-AXIOM generation**. z3 pre-axiomatises the bound ORDERING on each
variable as SAT clauses (`mk_bound_axioms`/`flush_bound_axioms`), so `x ≤ 3 →
x ≤ 5` is a unit propagation in the SAT core and never reaches the theory at
all. `OpenSMT` does the same eagerly (`LASolver::getSimpleDeductions`),
`SMTInterpol` queues every `BoundConstraint` in the interval inside `setBound`.
**We generate none.** That is a different and larger change — it moves work out
of the theory rather than making the theory better at it — and the interaction
between it and this propagator is unmeasured.

[ADR-2045]: adr-2045-the-bound-is-not-the-wall-qf-lra-is-one-offline-dense-engine.md
[ADR-2055]: adr-2055-the-tableau-is-the-memory-and-capping-it-costs-eighteen-clean-exits.md
[ADR-2100]: adr-2100-typed-route-ownership.md
[ADR-2111]: adr-2111-qf-lra-what-the-same-simplex-does-differently.md
