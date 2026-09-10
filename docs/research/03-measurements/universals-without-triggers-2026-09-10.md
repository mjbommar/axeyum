# Category A: the universals with no trigger at all — DO NOT BUILD

**Date:** 2026-09-10
**Lane:** Q1-triggers
**Verdict: DO NOT BUILD.** The fallback that applies was implemented and
measured. It fires on 13 universals across 9 files and moves **zero** verdicts
(1 of 32 decided before, 1 of 32 after). Half of category A is structurally
incapable of affecting a verdict at all, and 40% of it can never have a trigger
of any kind, so no trigger heuristic reaches it.

**Follows:** [`why-the-instantiation-loop-produces-nothing-2026-09-10.md`](why-the-instantiation-loop-produces-nothing-2026-09-10.md),
whose category A is 919 of 19,975 universal-**rounds** (4.6%) with `patterns=0`.
**Population:** the 32 files of `bench-results/parity-losses-20260908/UF.txt`.
**Method:** `AXEYUM_QPROBE=1 target/release/examples/axeyum_cli <file> --timeout-ms 24000`,
four at a time, plus a new compile-time probe (`diagnose_triggerless`) that
classifies each triggerless universal as it is compiled.
**Reproduce:** the fallback implementation measured here is commit `«FALLBACK»`,
reverted in `«REVERT»`; the probe it was measured with is on `main`.

## 1. How many distinct universals, on how many files

A round-count cannot answer this: a triggerless universal reappears in every
round, so 919 rows could be 8 universals or 900. Two independent readings agree
that it is neither.

**728 distinct triggerless universals, on 24 of the 32 files.**

- The matcher's own `triggerless` field on the `egraph-fixpoint` line counts
  `CompiledUniversal`s with `pattern_indices.is_empty() && !vars.is_empty()`.
- The new compile-time probe emits one line per triggerless universal per
  matcher build. A query builds the matcher several times (retry budgets,
  discovery rebuilds) and indices restart each time, so segmenting the stream on
  a non-increasing index and taking the **largest** build gives the file's
  widest universal population.

Those two numbers are equal on **all 19 files that print a fixpoint line at
all** — f01 7, f03 4, f05 98, f06 23, f09 7, f10 58, f11 101, f12 79, f13 53,
f18 58, f19 8, f20 14, f21 3, f23 6, f24 4, f26 4, f28 10, f31 2, f32 66. That
agreement is the check on the segmentation.

**Correcting my own first number.** An earlier commit in this lane reported 535
on 17 files, read from the fixpoint field alone. That was an undercount: the
fixpoint line only prints when the loop reaches a fixpoint having admitted
nothing, so 8 files that time out or exit earlier contributed 0 while in fact
carrying triggerless universals (f32 alone carries 66). **728 on 24 files is the
number.** The refutation for it: any file whose fixpoint field exceeds its
largest probe build would break the agreement above.

| | value |
|---|---:|
| distinct triggerless universals | **728** |
| files carrying at least one | **24 of 32** |
| bound-variable widths | 1 (187), 2 (118), 3 (163), 4 (77), 5 (99), 6 (43), 7 (37), 8, 9, 11 |
| uncovered bound-variable slots | 1,050 |

## 2. Why trigger selection returns nothing

`select_triggers` (`qinst_egraph.rs`) is **not** limited to single patterns — it
already builds multi-patterns by greedy set cover, which is what the `patterns=2`
and `patterns=3` probe rows are. It returns empty in exactly one situation:

```rust
_ => return Vec::new(), // some variable is in no function application
```

Candidates come from `collect_app_candidates`, which keeps a subterm only when
its operator is `Op::Apply(_)` — an uninterpreted function or predicate — and
which refuses to descend into a nested binder. A bound variable occurring only
under interpreted operators is coverable by nothing, and the greedy cover then
discards the **entire** trigger, including every variable it had already covered.
That all-or-nothing behaviour is the defect.

Of the 1,050 uncovered variable slots: **0 are absent** from the body, 441 occur
only inside a nested binder, and 609 occur only under an interpreted operator.
Of the operators those 609 sit directly under, **`Eq` is 988 occurrences against
`BoolImplies`'s 18** — it is an equality story almost exclusively.

`f31` (`UF/sledgehammer/TypeSafe/smtlib.1098821.smt2`, 2.4 KB, `:status unsat`,
z3 refutes it in 0.02 s with 4 instantiations) is the whole mechanism on one
page:

```
universal[0] vars=8  patterns=1 joined=44537 starved_joins=0 admitted=419
universal[1] vars=11 patterns=0 joined=0     starved_joins=0 admitted=0
universal[2] vars=7  patterns=0 joined=0     starved_joins=0 admitted=0
universal[3] vars=3  patterns=2 joined=2937  starved_joins=0 admitted=0
```

`universal[1]` is the file's nested `forall ((?v8 S6) (?v9 S7) (?v10 S7))`,
compiled by `collect_nested_registrations_rec` with the enclosing prefix it uses
— 8 outer variables plus its own 3, hence `vars=11`. Its body is

```smt
(=> (= ?v7 f9)
  (=> (= (f3 ?v0 ?v1 ?v2 ?v3 (f10 f11 ?v8)) f1)
    (=> (= (f12 ?v0 ?v8 ?v4 ?v9 ?v5) f1)
      (=> (= (f3 ?v0 ?v1 ?v2 ?v6 ?v10) f1)
        (=> (= (f13 ?v0 ?v10 ?v9) f1) false)))))
```

The application candidates cover ten of the eleven variables. `?v7` occurs
exactly once, as `(= ?v7 f9)` — `Op::Eq`, never a candidate — and one uncoverable
variable throws away a cover that was otherwise complete.

**The refutation for this claim:** if the cause were "no single term covers all
N variables", `select_triggers` would still return the greedy multi-pattern and
`patterns` would be ≥ 2, not 0. It is 0, which is reachable only through that
`return Vec::new()`.

This also disposes of the width correlation — the two widest universals being
the triggerless ones. Width is not a threshold, it is more chances to contain
one uncoverable variable.

## 3. Half of category A cannot affect a verdict, by construction

This is the finding that decides the item, and it is not about triggers.

A universal compiled from a `NestedRegistration` carries `active == false`. Its
tuples reach two places, and both drop them unless it has a `PositiveContext`:

- `generate_urgent_batch`: `if !quantifier.active { continue; }`.
- `lazy_clause_batches`: `if !quantifier.active { if quantifier.context.is_some()
  { … pending_positive … } batches.push(default); continue; }`.

`QuantifierDiscovery::stage` then consumes only `pending_positive`, and skips any
entry whose `context` is `None`. So a registration with `active == false` and
`context == None` is **inert**: matched, joined, and every tuple discarded.
Giving it a trigger cannot change a verdict — it can only spend the shared
per-round join ceiling that category C is already starving on.

| | universals | share |
|---|---:|---:|
| assertions (`active`) | 351 | 48% |
| registrations with a positive context | 17 | 2% |
| **inert registrations** (`!active`, no context) | **360** | **49%** |

**Both of `f31`'s triggerless universals are inert.** Category A is therefore not
why we fail on the coordinator's reproducer, and a trigger fallback could not
have decided it.

Positivity is dropped whenever the scan crosses a binder
(`collect_nested_registrations_rec`: "The path would now cross this binder, so
positivity is dropped"), so every `forall` nested inside another `forall` lands
in the inert bucket. In sledgehammer output that is most of them.

**The refutation:** if an inert registration's tuples reached any admission path,
one of the three `!active` guards above would not `continue`.

## 4. What a fallback could reach, partitioned

Each triggerless universal falls in exactly one bucket (first match wins), and
"actable" means `active || context.is_some()` — the only ones whose instances
could matter.

| bucket | universals | actable |
|---|---:|---:|
| **no candidate application at all** (`candidates=0`) | **290** | 267 |
| every gap has an equality partner, some needing the tuple | 336 | 51 |
| blocked by a nested binder | 73 | 25 |
| every gap has a **ground** equality partner | 20 | 16 |
| some gap has no equality partner | 9 | 9 |
| **total** | **728** | **368** |

Two rows carry the verdict:

- **290 universals (40%) have no `Op::Apply` subterm mentioning any bound
  variable outside a nested binder.** There is nothing to e-match on. No trigger
  heuristic — single, multi-pattern, or otherwise — produces a trigger for them,
  because a trigger is a term and there is no term. 267 of them are actable, so
  they are not dismissible as inert. Reaching them means model-based
  instantiation, not better trigger selection.
- The largest fixable row, 336, is only **51 actable**. Its fix needs the
  matched tuple substituted into the partner term, which the join cannot do
  (`witness_tuples_for_group` has no arena).

## 5. The fallback that does apply, implemented and measured

The narrow case — every gap has a *ground* equality partner — needs no
substitution: the binding is a fixed `TermId` known at compile time. It was
implemented as `select_triggers_with_fixed_bindings` plus a `fixed_bindings`
field on `CompiledUniversal`, consumed in `witness_tuples_for_group`'s
completeness check, and gated to actable universals so it cannot spend budget on
the inert half.

Soundness is not at stake and should not be argued as though it were: **every**
instance of a universal is entailed by it, whatever terms are substituted. The
equality is only the reason to expect the instance to be *useful*. The one real
requirement is that the substituted term be binder-free, or the "instance" would
carry a free variable; `is_binder_free_term` enforces that against the query's
whole binder set, not just the universal's own variables.

**Measured, same command and slice, before and after:**

| | value |
|---|---:|
| universals rescued (triggerless count fell) | **13**, on 9 files |
| files decided `unsat` before | **1 of 32** |
| files decided `unsat` after | **1 of 32** |
| files whose verdict changed, either direction | **0** |

The 13 is the check that the change is live rather than dead: f02 −1, f05 −2,
f12 −2, f13 −2, f19 −1, f20 −1, f21 −2, f23 −1, f24 −1. A change that fired zero
times and reported "no verdict change" would not be evidence of anything.

**The behaviour change was reverted; the diagnostic probe was kept.** This
follows the precedent the source note records for this same loop: rotation of the
join walk was also measured-neutral and also reverted, because
`qinst_egraph.rs`'s admission schedule is perturbation-sensitive (a per-pattern
match split once cost a scored refutation), so a measured-neutral perturbation
here is a bad trade. The implementation is recoverable at `«FALLBACK»` if a
later measurement gives it a reason to exist.

## 6. Verdict, and what would refute it

**DO NOT BUILD trigger fallbacks for category A.** Four measurements, any one of
which would have to be wrong:

1. 49% of category A (360 of 728) is inert registrations whose tuples are
   discarded by three explicit guards. *Refuted by:* an admission path that
   accepts a tuple from an `!active`, contextless universal.
2. 40% (290 of 728, 267 actable) has no candidate term to trigger on at all.
   *Refuted by:* a `candidates=0` universal for which some trigger exists.
3. The applicable fallback was built and moved 0 of 32 verdicts. *Refuted by:*
   re-running the slice at `«FALLBACK»` and counting more than one `unsat`.
4. The reproducer that motivated the item, `f31`, has both of its triggerless
   universals in the inert half. *Refuted by:* either of them reporting
   `active=true` or `context=true`.

## 7. Where the next measurement should go instead

Not further into trigger selection. The source note's own ordering already
points at the two categories that are decisions rather than absences — B (8,219
rounds matching nothing) and D (3,110 rounds where joins existed and admission
dropped every one). This lane adds one constraint to that work: **368 of the
728 triggerless universals are actable and 267 of those have no trigger term in
existence**, so whatever reaches them will be model-based instantiation or
another non-e-matching route, and it should be scoped as that from the start
rather than as a trigger heuristic.
