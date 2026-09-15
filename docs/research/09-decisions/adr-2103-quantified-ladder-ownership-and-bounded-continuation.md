# ADR-2103: the quantified ladder under the same ownership rule, and a bounded continuation for the two files it cost

Status: accepted
Index-summary: ADR-2100 typed the quantifier-free dispatch ladder and measured, on the way, that **482 of 643 undecided Tier 1 rows — 75 % — never reach it**: their budget goes to the `q:` rungs of the quantified ladder in `solve`, "a different ladder with its own decline discipline", and it said typing that one was the obvious next slice. This is that slice, plus the budget fix for the two stable losses ADR-2100 published rather than smoothed. **SIZING FIRST, and the ceiling over the 482 is ZERO — for every possible ownership table, not merely for the one this ADR ships.** No row in the population had its ladder ended by a rung's non-decision at all: 211 ran out of rungs and 271 ran out of clock. The sizing needed two corrections of its own and made a finding worth more than the ceiling. **`RouteTrace::record_result` maps `Unknown` to `record_declined`**, so a rung whose `Unknown` WAS the answer and a rung that declined are the same word on the trail; the first pass tested that word and got 0 of 482, which is exactly what a detector that cannot fire prints. **Six rungs record nothing when they decline**, so their absence is not evidence of a skip. And the 53 rows the corrected script did flag as candidates were all at the 24 s budget (24,015–24,950 ms of trail time, 0 of 53 under 90 % of it), clock-ended through **the one budget exit in the quantified ladder that records nothing** — `finish_quantified_solve_or_induct`'s `config_with_remaining_timeout` guard, which every other exit reaches via `quantified_timeout`. 11 % of the population, and 48 of `UF`'s 108, were invisible to the sink that exists to catch them. What shipped: `quant_ownership::QuantRoute`, seventeen rungs with exhaustive `owns`/`kind`, reusing `Construct`/`ConstructSet`/`RouteKind`/`Ownership`/`DispatchError` rather than growing a parallel mechanism; `solve`'s body moved to `solve_inner` over the typed channel, where **`rustc` named 29 sites**. The live defects it closed were not in the sizing's population: `q:checked-fast-path` had **eight bare `?`s**, each turning a probe's fragment refusal into `solve`'s ERROR with the whole ladder below unreached — ADR-1927's defect with eight instances in one function — and its five refutation searches were one short-circuiting disjunction of `?`s, so one probe declining skipped the four below it too. `q:egraph` asked `mbqi_source_shape_supported` and, when that said no, returned a retained finite-expansion `unknown` as the query's verdict: **one route reasoning about what another route can do**, which ADR-2065's own doc comment names as the thing a route cannot do soundly. That predicate is DELETED; the preference it existed for is applied at the end of the MBQI arm off a typed flag rather than a scan of the detail string. For ADR-2100's two stable losses — which were the price of an ATTEMPT and not routing, the same `decided_by`/`bound_by` to the millisecond and **25 instantiation rounds instead of 35 and 45** — `OWNERSHIP_CONTINUATION_SHARE` gives the rungs below a converted non-decision a quarter of the remaining clock, and **only inside a quantified rung's sub-solve**, because at the outermost dispatch the continuation IS the answer and capping there would pay for the losses with ADR-2100's two gains. Its nesting signal is a NEW unconditional counter: `route_trace`'s is gated on attribution being collected, so a budget policy keyed on it would branch one way under `--trace` and the other without — the instrument changing the thing it measures. The lane's own first patch turned **nine assertions red in five suites**, ADR-1966's experience exactly, and every one was the lane's bug and not the fixture's: the four quantifier-free HAND-OFFS are ladder TAILS, so routing their `check_auto` through the decline funnel broke ADR-1980's `propagate` lever and replaced its sentence with an invented "budget exhausted". Reclassified as `DispatchError::ladder`-style propagation, **no assertion was weakened and all nine came back**.
Index-status: accepted
Date: 2026-09-15

## Context

[ADR-2100] applied one rule to the quantifier-free dispatch ladder: **whether a
rung's non-decision stops the ladder is a declaration on the route, not the
error variant a function happened to return.** It closed a defect class that had
shipped five times ([1927], [1966], [1980], [2030], [2065]), four of the five
found by accident.

It also said, in its own "what this ADR does not claim":

> **The quantified ladder in `solve` is untouched.** It is a different ladder
> with its own decline discipline ([1927]), and **75 % of Tier 1's undecided mass
> ends there**. Typing its rungs the same way is the obvious next slice and
> nothing here is evidence about it.

And it shipped with exit criterion 3 **NOT MET on losses**: two files,
reproducible 3/3, named so a later lane could take them rather than rediscover
them.

This ADR is both halves.

## Part A — sizing first, and the ceiling is ZERO of 482

**The number up front, because the exit criterion asks for it there: 0.**

### The method, and why it needs no ownership table

"An enterable owning rung below the terminal one" presupposes that a **rung**
ended the ladder. On this ladder that presupposition is checkable on its own,
and checking it first is the whole analysis, because a ceiling computed over
rows the CLOCK ended is a ceiling on nothing. Three things end the quantified
ladder in `solve`:

1. **A rung's non-decision** — the only class an ownership declaration can
   reach. On the trail: rung `R` ran, a rung below `R` did not, and neither
   `q:timeout` nor a partial (watchdog-killed) trail explains the absence.
2. **The clock** — `config_with_remaining_timeout` returns `None` and
   `quantified_timeout(..)` records `q:timeout`, or the harness watchdog kills
   the process and the trail carries the `; partial ` prefix.
3. **Running out of rungs** — `q:nat-induction` ran and declined.

So the ceiling is bounded above by |class 1|, computed from the ladder ORDER and
the trail alone. It is zero, which makes the ceiling zero for **every possible
ownership table** — a stronger statement than one derived from the particular
table this ADR ships, and the statement `size-q-ceiling.py` actually makes.

No sweep was re-run. The evidence is ADR-2100's own committed `--trace` capture
of the same rows, joined by corpus-relative PATH to lane PLAN-SIZING's inventory
— **643 of 643 join, and the script ABORTS rather than reporting a smaller
number** if one is missing from either side.

### The numbers, per division, over the 482

| division | rows | candidate | clock | watchdog | exhausted |
|---|---:|---:|---:|---:|---:|
| AUFDTLIRA | 67 | 1 | 12 | 0 | 54 |
| AUFLIRA | 20 | 0 | 16 | 1 | 3 |
| UF | 108 | 48 | 19 | 6 | 35 |
| UFDTLIRA | 50 | 1 | 0 | 0 | 49 |
| UFLIA | 107 | 3 | 68 | 7 | 29 |
| UFNIA | 130 | 0 | 80 | 9 | 41 |
| **total** | **482** | **53** | **195** | **23** | **211** |

`AUFLIRA` contributes 20 rather than PLAN-SIZING's 22 and `UFNIA` 130 rather
than 147 because **this is the 482-row no-QF-dispatch SUBSET** of ADR-2100's
643-row re-capture, not PLAN-SIZING's 645-row `undecided` column. The
denominator is 482 throughout, and it is the same 482 ADR-2100 published.

**The 53 candidates are the clock too**, and the channel that says so is the
wall clock rather than another record: every one sits between **24,015 and
24,950 ms** of trail time against the sweep's 24,000 ms budget, **0 of 53 under
90 %** of it. `check-candidates.py`'s exit status depends on that finding.

So: **candidates after refutation = 0. The ceiling is 0 of 482.**

### Three corrections the sizing produced, each of which would have been a claim

**First, the detector could not fire.** `RouteTrace::record_result` maps
`CheckResult::Unknown` to `record_declined`, so a rung whose `Unknown` WAS the
ladder's answer and a rung that declined and let it continue carry the **same
word** on the trail. The first pass tested `outcome != "declined"` and got
**0 of 482** — which is precisely what a detector that cannot fire prints, and it
would have been published as "no rung ever stopped the ladder" with the right
conclusion for the wrong reason. Terminality is read off the ladder's control
flow and the ABSENCE of rungs below, never off the outcome word.

**Second, six rungs record nothing when they decline.**
`q:checked-fast-path`, `q:skolem-qf`, `q:vacuous-universal-qf`,
`q:eq-partition`, `q:unsat-universal` and `q:fourier-motzkin` call
`record_quant_rung_result` only on a DECISION. Their absence from a trail is
therefore not evidence they were skipped, and treating it as such reports every
one of the 482 rows as a candidate. They are excluded by name in
`SILENT_ON_DECLINE`, and two of them — `q:eq-partition` and `q:unsat-universal`
— now record their declines, so the next reader does not have to know.

**Third, the candidate list was capped at 40.** `check-candidates.py`'s first run
verified 40 of 53 rows and printed "EVERY candidate row is at the budget". The
cap is gone and the published run covers 53 of 53. A checker whose population is
a prefix of its subject reports on the prefix and says "every".

### An independent cross-check: [ADR-2090] agrees, on a population this lane never touched

[ADR-2090] (lane CORE-SELECT) asked a different question — whether picking the
right ASSERTIONS would convert undecided rows — and answered no. Its §7 breaks
down the hardest rows it found, **193 of 230 where we return `unknown` even when
handed z3's own minimal core**, into their named terminal reasons:

> 12 rows where e-matching reaches a fixpoint and says more rounds cannot help;
> **17 where `mbqi` declines a datatype fragment in three distinct wordings**;
> 5 where instantiation does not reach nested or existential quantifiers;
> 4 bounded at integer width 32.

Every one of those is a `q:` rung's terminal reason, which is exactly the
surface this ADR types. Two things follow, and they point in opposite
directions:

**It confirms the declaration.** `q:mbqi` is declared to own
`{Int, Real, BvOrFloat, Function}` and **not** `Datatype`, derived from its own
refusal messages on this lane's population. ADR-2090 measured the same refusal
independently, on a different population, at 17 rows in three wordings. Two
lanes reading the same rung's behaviour from different directions and getting
the same fragment boundary is the strongest evidence available here that the
declaration is derived rather than invented.

**And it confirms the ceiling of 0.** Under the rule those 17 `mbqi` datatype
declines stop being terminal — but the only rungs below `q:mbqi` are
`q:uf-fmf-full` (sat-only, pure-UF) and `q:nat-induction` (refutation-only), and
**both already run** on an `Unknown` from MBQI. So the rule reaches those rows
and changes nothing about them, which is the same answer this lane's sizing
gives by a different route. The e-matching fixpoints, the unreached nested
quantifiers and the width-32 bound are capability and budget limits, not
ownership: no declaration on any route converts them. ADR-2090's own summary
line is *"None of these is selection"*; this ADR adds that none of them is
ownership either.

ADR-2090 also measured `bound_by` on those 193: `q:mbqi` ResourceLimit 40,
`q:mbqi` Incomplete 37, `int-blast-ladder` Timeout 31, `q:egraph` ResourceLimit
26, Watchdog 17 — at a **13.1 s median and 20 attempts**. That is the same
picture as this lane's 482: the engine worked hard and ran out of clock. It is
also why Part B is the half of this ADR with something to win.

### The finding worth more than the ceiling

The 53 rows are clock-ended through **the one budget exit in the quantified
ladder that records nothing**:

```rust
// finish_quantified_solve_or_induct
let Some(induction_config) = config_with_remaining_timeout(config, deadline) else {
    return Ok(result);          // <-- no route record, no q:timeout
};
```

Every other budget exit goes through `quantified_timeout(..)`, which records
`q:timeout` from nine program points. This one did not, so **11 % of the
population — and 48 of `UF`'s 108 — were invisible to the sink that exists to
catch exactly them**, and any census keyed on `q:timeout` under-reported the
ladder's budget exits by that much. It records now.

Artifacts: `bench-results/quant-ladder-ownership-20260915/` — the four
exploratory scripts, `size-q-ceiling.py`, `check-candidates.py`, and the runs.

## Part A — what shipped

`quant_ownership`, a module beside `route_ownership` in `auto.rs`:

- **`QuantRoute`** — the seventeen rungs of the quantified ladder, in the order
  `solve` → `finish_quantified_solve` → `finish_quantified_solve_or_induct`
  RUNS them. `owns`, `kind` and `route` are exhaustive `match`es, so a rung added
  to `solve` without a declaration does not compile.
- Its `label` delegates to [ADR-2101]'s `route_trace::Route`, so the wire
  strings have **one** source rather than two that agree today — the shape
  ADR-2060 found lying.
- `Construct`, `ConstructSet`, `RouteKind`, `Ownership` and `DispatchError` are
  **reused, not re-spelled**. A second spelling of a rule is a second thing that
  drifts, which is the defect the first module exists to close.
- `ConstructSet::EVERY` — what the ladder assumes when the feature scan misses
  its deadline. Nothing owns it, so every non-decision declines, which is the
  direction that can only lose completeness.

### How each rung's ownership is derived

The quantified rungs do not open with a `Features` conjunction the way the
quantifier-free ones do — they gate on quantifier SHAPE, and their theory
refusals come out of the sub-solve underneath. So the derivation is from each
rung's own documented contract, and it falls into three families:

**One-directional accelerators own nothing.** A rung that can only ever return
one verdict is not a decision procedure for any fragment: its non-decision says
nothing about whether a later rung can decide. `q:ground-subset`,
`q:bool-skeleton`, `q:eq-partition`, `q:unsat-universal`, `q:egraph` and
`q:nat-induction` are refutation-only; `q:forall-exists-witness`,
`q:uf-fmf-probe` and `q:uf-fmf-full` are sat-only. All nine own `{}` and are
`FastPath`. ADR-1927 reached the same conclusion from the other side: it wrote a
guard for `checked_quantified_fast_path`, measured it firing **0 times in 800
files**, and deleted it.

**The four quantifier-free hand-offs own what the OTHER ladder owns.**
`q:skolem-qf`, `q:valid-universal-qf`, `q:vacuous-universal-qf` and
`q:fourier-motzkin` each end by handing a quantifier-free residual to
`check_auto` and returning its verdict. That union is **not retyped**:
`the_qf_handoffs_own_exactly_what_the_qf_ladder_owns` re-derives it from
`DispatchRoute::ALL`, so a class added to the other table moves this one or
fails.

**The two engines own the fragment their sub-solve reaches.**
`q:finite-expansion` is complete for finite domains, so it owns `{BvOrFloat}` —
and its own refusal sentence on this population is "quantifier over
non-enumerable domain Int" 516 times and "(Uninterpreted N)" 278 times, which is
the same statement from the other side. `q:mbqi` owns
`{Int, Real, BvOrFloat, Function}`: its ground rounds go through the
bit-blasting backend, and the declared carrier sorts and non-BV arrays it
refuses by name are left out.

**Conservative in which direction, and it is not the same direction as
ADR-2100's.** Declaring too LITTLE makes a rung decline where it used to stop
the ladder: more rungs run, which cannot lose soundness but CAN cost budget —
and on this ladder budget is the binding constraint on **271 of 482** undecided
rows. So "when a gate is ambiguous, declare less" is not free here the way
ADR-2100 could treat it. Where the contract is genuinely ambiguous this table
declares the value that PRESERVES today's behaviour, and the alternative is
named below as untested.

### The compiler named twenty-nine sites

`solve`'s body moved to `solve_inner` returning
`Result<CheckResult, DispatchError>`, and `DispatchError` still has no
`From<SolverError>`, so every `?` and every `return Err(..)` in the quantified
ladder was a type error until its site named a rung. `rustc` printed **29**:

| what | count | closed as |
|---|---:|---|
| `q:checked-fast-path`'s eight probes | 8 | `quant_rung_or_decline(CheckedFastPath, …)` |
| `q:forall-exists-witness` | 1 | `quant_rung_or_decline` |
| `q:uf-fmf-probe` — the finder and its `check_model` gate | 2 | `quant_rung_or_decline` |
| `q:mbqi-quick` | 1 | `quant_rung_or_decline` |
| `q:mbqi` — the non-`Unsupported` arm and its `check_model` gate | 2 | `DispatchError::at_quant` / `quant_rung_or_decline` |
| `q:uf-fmf-full` — the finder and its `check_model` gate | 2 | `quant_rung_or_decline` |
| `q:egraph`'s non-`Unsupported` arm | 1 | `DispatchError::at_quant(Egraph, e)` |
| `q:finite-expansion`'s deciding arm | 1 | `DispatchError::at_quant(FiniteExpansion, e)` |
| `q:ground-subset`, `q:bool-skeleton` | 2 | `quant_rung_or_decline` |
| `q:valid-universal-qf`'s non-`Unsupported` arm | 1 | `DispatchError::at_quant` |
| `q:vacuous-universal-qf`'s elimination pass | 1 | `quant_rung_or_decline`, declining to the un-eliminated list |
| `q:nat-induction` | 1 | `quant_rung_or_decline` |
| the four quantifier-free HAND-OFFS' `check_auto` | 4 | `DispatchError::at_quant`, **propagating** — see below |
| the normalization, the skolemization and the lazy-BV hook | 3 | `DispatchError::ladder` |

The three `ladder` sites prepare the assertion list for every rung underneath or
belong to a quantifier-free opt-in, so a failure there is not any one rung's
fragment refusal. ADR-2100 classified `lift_arith_ite` the same way.

The value of the type is not the one-off list. It is that the list stays
produced by the compiler as the ladder changes: ADR-1966's own instrument went
from 37 sites to 72 the moment it counted tail position, and warned that *"any
future scan of this kind that counts only `?` is under-reporting by about
half"*. Nothing here counts.

### The live defects this closed, none of which are in the sizing's population

The ceiling is 0 over the 482 **undecided** rows, and these are not about those
rows — they are about queries whose ladder ended in an ERROR, which
`stopped_by_unknown` excludes by construction. They are the bug class the plan
says Phase 1 is measured in.

**`q:checked-fast-path` had eight bare `?`s.** A probe refusing its own fragment
became `solve`'s ERROR — not merely this rung's non-decision but the whole
query's, with finite expansion, the e-graph refuter, MBQI, the finite-model
finder and ℕ-induction never reached. That is [1927]'s finding with **eight live
instances in one function**. Worse, its five refutation searches were one `||`
chain of `?`s, which **short-circuits**: one probe declining skipped the four
below it as well as the rest of the ladder. They accumulate now.

**`q:egraph` asked what another route could do.** Its `Unsupported` arm branched
on `mbqi_source_shape_supported` and, when that said no, returned a RETAINED
finite-expansion `unknown` as the query's verdict, ending the ladder before
MBQI, the finite-model finder and ℕ-induction. [2065]'s own doc comment names
that shape:

> The obvious repairs … all require this route to reason about what OTHER routes
> can do, which it cannot do soundly and which would need re-deciding every time
> the ladder changes.

`q:egraph` is refutation-only, so it owns nothing and is a `FastPath`: its
refusal is a decline and no cross-route predicate is consulted at all. The
predicate is **deleted**, exactly as ADR-2100 deleted `hand_back_unless_refuted`.
`finite_unknown` is not lost — the preference it existed for ("a narrower
quantified fallback cannot replace an already-classified finite-expansion
`unknown` with an operational shape error") is applied at the END of the MBQI
arm, where it costs no rung its turn, and off a **typed flag** rather than a
scan of the `detail` string, which would be ADR-2060's defect exactly.

**`q:nat-induction` swallowed every error.** Its outcome was matched with
`if let Ok(Some(CheckResult::Unsat))`, so a refusal left no trace at all. It
records now, and still declines, so the caller's already-formed `unknown` is
returned exactly as before.

### What is declared to PRESERVE behaviour, and the untested alternative

The four quantifier-free hand-offs are declared `Decider`. Declaring them
`FastPath` would give `q:nat-induction` — the one rung below them that still
reads the ORIGINAL assertions, and whose own doc says skolemization has already
destroyed the negated universal it matches on — a turn it does not get today.
That is a plausible gain and it is **not taken here**, because **no row in the
482-row population exercises it**: none of the four ever probed there, so there
is nothing to measure it on. `settle_quant_rung` is wired at all four sites and
`nat_induction_after_declined_handoff` is the continuation, so the rule is live
and the change is one `kind()` arm — but it fires only when the query carries
`NestedArray` or `WideInt`, the two classes nobody owns.

## Part B — the bounded continuation

### The mechanism, read off ADR-2100's own trails

ADR-2100's two stable losses were **not a routing change**:

```
Q525-025 …length_check
  A unsat    decided_by=q:egraph bound_by=q:mbqi last=q:egraph bound_ms=10616 total_ms=14822 attempts=35
  B unknown  give-up kind=Watchdog
             decided_by=none    bound_by=q:mbqi last=q:egraph bound_ms=10599 total_ms=15528 attempts=25
```

Same route, same `bound_by`, same cost **to the millisecond** (10,616 vs
10,599). What changed is the **price of an attempt**: the same fifteen seconds
bought 25 instantiation rounds instead of 35 and 45, because each round's ground
check — a `check_auto` sub-solve — now runs the rest of the quantifier-free
ladder where it used to stop at a rung's terminal `Unknown`.

ADR-2100 declined to trade the rule for the two files, and was right to: every
narrowing of an ownership declaration puts a route back in the position of
deciding on another route's behalf, which is the defect. **The fix is not in
ownership, it is in budget.**

### `OWNERSHIP_CONTINUATION_SHARE`

When `settle_rung` converts a would-be-terminal non-decision into a decline, the
rungs BELOW it run under `1/4` of the clock remaining at that moment. The
continuation is still tried — ADR-2100's two stable gains came from it — but it
cannot consume what the deciding rung above needs.

Four is the divisor `UF_ARITH_LADDER_RESERVE_SHARE`,
`ABV_ONLINE_LADDER_RESERVE_SHARE` and `DL_LADDER_RESERVE_SHARE` already use, and
this is the second in the tree that GRANTS a fraction rather than withholding a
reserve. `AXEYUM_OWNERSHIP_CONTINUATION_SHARE=off` restores the pre-ADR-2103
behaviour and is the control arm; the lever **fails closed** (an unset or
malformed value keeps the shipped divisor), because a policy that silently
reverted on a typo would let an A/B measure the shipped arm in both halves and
report the resulting zero as a null.

**Only inside a quantified rung's sub-solve.** At the outermost dispatch the
continuation IS the answer, so capping there would pay for ADR-2100's two losses
with its two gains, which is not a fix.

### Both named files come back, 3/3 in both arms

The two files ADR-2100 named as its own stable losses were re-run through that
ADR's own `recheck-movers.sh`, unchanged, three passes per arm, arms alternating
within the three, on one pinned physical core pair at the same 24 s / 8 GiB
envelope:

| file | A (`51baff9ef`) | B (this branch) | |
|---|---|---|---|
| `AUFDTLIRA/…/Q525-025__controlling_result__fixed_string.adb_18_11_length_check` | `unknown` / `unknown` / `unknown` | `unsat` / `unsat` / `unsat` | **STABLE-GAIN** |
| `AUFDTLIRA/…/R509-011__higher_order_proof__why_bfafe7_…fold-T-defqtvc` | `unknown` / `unknown` / `unknown` | `unsat` / `unsat` / `unsat` | **STABLE-GAIN** |

Read the direction carefully, because the arms are not the ones ADR-2100 used.
**A here INCLUDES ADR-2100**, so A is the arm that lost these two files and B is
the arm with the bound. `STABLE-GAIN` therefore means exactly what the exit
criterion asks: the bound recovers both, reproducibly, 0 of 6 passes
disagreeing with its classification. Exit status is `0` on all twelve passes.

`bench-results/quant-ladder-ownership-20260915/named-losses-recheck.tsv`.

### The nesting signal is a new counter, and that is the point

`route_trace::NestedDispatchGuard` answers "am I inside a quantified ladder"
and is armed at exactly the right place — but it is **gated on attribution being
collected**, so outside a `--trace` run its counter never moves. A budget policy
keyed on it would take one branch under tracing and the other without, which
makes **the instrument change the thing it measures** — and every measurement in
this ADR and in ADR-2100 is a `--trace` capture. `QuantifiedLadderDepth` is
maintained unconditionally, costs one `Cell` read and one write per quantified
solve, and is disarmed at the same four hand-off points the trace guard is.

## The lane's first patch turned nine assertions red, and every one was the lane's bug

ADR-1966 was reverted for turning seven assertions red in four ADRs' suites.
This lane's first patch turned **nine** red in five: `dt_uf_gate` (1),
`dt_capability_1935` (3), `dt_constructor_arg_1942` (2),
`dt_valued_result_1946` (1) and `dispatch_rung_refusal_declines` (2).

The message was the finding:

```
expected a clean Unsupported under the `propagate` arm, got
Ok(Unknown(UnknownReason { kind: ResourceLimit,
  detail: "quantified solve time budget exhausted after existential skolemization" }))
```

**The four quantifier-free hand-offs are ladder TAILS, not rungs.** Their
`check_auto` call IS the other ladder, so an `Unsupported` out of it is that
ladder's terminal answer and there is nothing below to hand it to. Routing it
through the decline funnel turned ADR-1980's `propagate` lever into a decline
**and** replaced its sentence with a manufactured "budget exhausted" — a message
that is simply false about what happened. ADR-2100 classified its own two tails
the same way for the same reason:

> declining there would return `Ok(None)` to a ladder with nothing below it and
> force the dispatcher to manufacture a second `unknown` that says strictly less
> than the one it discarded.

Reclassified as propagation, **all nine came back and no assertion was
weakened** — ADR-1980's method with the happier outcome that relocation was not
needed, because the fixtures were right and the patch was wrong. The same
mistake appeared a second time on `q:vacuous-universal-qf`'s elimination pass,
which IS a rung: its decline value is the un-eliminated assertion list, which is
what the `q:valid-universal-qf` GUARD one rung above has always returned, not a
manufactured timeout.

## Exit criteria, each MET or NOT MET

**1. Sizing for Part A, per division over the 482, with the denominator, before
any code — MET, and the number is 0.** Published above and committed at
`531a593eb`, before the first line of Rust. The ceiling is 0 for every possible
ownership table, because no row's ladder was ended by a rung's non-decision.

**2. The `q:*` ladder under the ownership rule with the same types; `rustc`
enumerates the sites; each named — MET.** `quant_ownership::QuantRoute` reuses
`Construct`, `ConstructSet`, `RouteKind`, `Ownership` and `DispatchError`; the
error channel still has no `From<SolverError>`; `rustc` named **29**, and the
table above names each one and how it is closed.

**3. The named suites green with nonzero counts — MET.** All **19** suites of `hooks/pre-push`'s `dispatch/reason:` block — the
list read out of the hook rather than retyped — **183 tests, 0 failed, 0
inert**, and the runner's own two guards (a zero-count suite is reported as
`ZERO TESTS -- an inert suite is not a passing one`, and a missing result line
as `DID NOT RUN` rather than as a pass) both stayed quiet.
`bench-results/quant-ladder-ownership-20260915/dispatch-reason-suites.txt`.

**The solver unit sweep: `cargo test -p axeyum-solver --lib --features full`
— 1,813 passed, 0 failed**, a nonzero count confirmed rather than assumed.
`route_attribution` 8/8 green too, which is the suite that would have caught the
two decline records added to `q:eq-partition` and `q:unsat-universal` changing
an attempt count something pins.

This is the run AFTER the nine-red episode above, on the corrected tree, and it
is the same nineteen-suite list ADR-2100 gated on.

**The capability ratchet: `progress_frontier` 12 of 12, no regression**, every
family `comparable: true` and `ratchetable: true` — so the ratchet was
*enforced*, not skipped, which is the distinction
`frontier-ratchet-reference-frame.md` exists to make.

**The five artifacts are deliberately NOT re-pinned**, and ADR-2100 made the
same call on the same family one commit earlier. The run rewrote its own JSON,
and one family — `bv_reduction` — read **36 against a committed 39**, at a
baseline of 30, so far above the ratchet that it passed. ADR-2100 saw **38**
against the same committed 39 and recorded why it did not move the pin: that
family's committed history is **40 → 34 → 39 at a fixed baseline**, so a single
point inside its own variance is not grounds to move a shared pin in either
direction. 36 is inside that band too, and this run had the lane's own mutation
builds on the box beside it. The artifacts are restored; the observation is
recorded here instead of being re-pinned silently or dropped.

**4. Interleaved A/B — see the status file for the run.**

**5. Mutation — MET. Three mutations, each killing EXACTLY ONE named fixture,
and three different fixtures.**

| mutation | baseline | kills |
|---|---:|---|
| `quant-route-ownership-rule` — the ownership check on a one-directional quantified rung | 101 green | **1**: `a_one_directional_quantified_rungs_unknown_never_terminates_the_ladder` |
| `quant-route-ownership-marker` — the inconsistency report on an owning quantified decider's refusal | 101 green | **1**: `an_owning_quant_deciders_refusal_is_reported_and_a_one_directional_rungs_is_not` |
| `quant-continuation-bound` — the bound on the ownership rule's continuation, set to unbounded | 101 green | **1**: `the_continuation_bound_applies_only_inside_a_quantified_ladder` |

The third is the budget half the exit criterion asks for, and the mutation is on
the SHARE GUARD rather than on the constant. Editing
`const OWNERSHIP_CONTINUATION_SHARE: u32 = 4;` would also kill
`the_ownership_continuation_share_lever_fails_closed`, which pins that literal
and would die from ANY edit to the line — a kill set that includes a test fired
by the changed line measures the edit, not the guard. ADR-2100 declined the same
temptation for the same reason on `DispatchRoute::owns`.

Three runners and not one, for the reason ADR-2100 gave: the halves fail in
opposite directions, and a shared rejection path is how six of seven guards in
one suite here were once removable with everything still green.
`--check-anchors` reports `suites=137|anchors=1059|stale=0`.

Its first run came back **BASELINE IS NOT GREEN**, killing
`every_route_budget_in_this_file_goes_through_the_slice_policy` — and the reason
is worth recording because it is the same shape as the anchor collision above.
That guard scans for a hand-written timeout assignment **as text**, and the
comment written beside `ownership_continuation_config` to explain why the code
goes through `LadderSlice` **quoted the spelling the guard rejects**. The guard
fired on the comment. A guard that cannot tell code from a comment about code is
still the guard; the comment names the spelling in prose now.

[1927]: adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md
[1966]: adr-1966-a-rungs-refusal-of-a-construct-a-later-rung-owns-is-a-decline.md
[1980]: adr-1980-the-cheap-check-was-the-whole-target-a-dispatch-decline-not-a-datatype-capability.md
[2030]: adr-2030-the-fallback-was-already-offered-and-the-lemma-batch-is-the-whole-set-at-once.md
[2065]: adr-2065-the-real-collector-can-hold-a-term-and-the-sat-exits-close-by-type.md
[ADR-2100]: adr-2100-typed-route-ownership.md
[ADR-2101]: adr-2101-the-trace-is-the-api.md
[ADR-2090]: adr-2090-the-cores-are-small-and-findable-and-we-do-not-decide-them.md
