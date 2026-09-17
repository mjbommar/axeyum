# ADR-2149: nested-binder activation was already built; what the caps were spent on was duplicates, and the crossed-binder class is 9 cores wide

Status: proposed
Date: 2026-09-17
Index-status: proposed
Index-summary: QUANT-COMPOSE read `qinst_egraph.rs` and concluded that no activation reaches a universal nested inside another universal's binder — `collect_nested_registrations_rec` drops polarity tracking on entering a `forall` body before any level is consulted, so the registration has no `PositiveContext` and its tuples die at `inactive_dropped`. **Two fixtures decide it against the strong form.** The brief's own fixture `∀x.(P(x) ⇒ ∀y.Q(x,y))` is `unknown` through the isolated loop at the shipped level with 14 tuples dropped — in the `untracked` class (the `⇒` step ADR-2120's level 0 refuses), not the crossed-binder one, because the outer prefix is peeled before the walk; at level 1 it is `unsat`, and the front door refutes it at level 0 by normalising `⇒` away. The genuinely crossed shape `∀x.(P(x) ⇒ ∀u.(R(x,u) ⇒ ∀y.Q(u,y)))` refutes at level 1 **through the registrations `NestedDiscovery::scan` adds from the outer instance and the staged replacement** (`discovered=2`, `handed_off≥1`) while its static registration's 4 tuples are dropped in the new `crossed-binder` class — z3's "the instance exposes the universal" (`qi_queue.cpp:336` → `smt_internalizer.cpp:656`) is already built, as ADR-2120's slice 3. So `inactive_dropped` is now split by the FIRST refusal on the path (`InertReason`: crossed-binder / negative / untracked), readable in-process (`NestedActivationStatsGuard`) and on the `AXEYUM_QPROBE` line, which now prints at EVERY loop exit (it was missing on 35 of 53 cores) and survives discovery rebuilds. **The 53-core split**: shipped arm 2,520,232 untracked / 17,685 crossed on 5 cores / 0 negative; at `AXEYUM_QINST_POSITIVE_PATH=1` 1,611,516 crossed on **9** cores / 231,040 negative / 57,014 untracked — and 13.7 M contextful tuples cut by the 256-per-round handoff cap, 17,600 handed off and refused because they bind a variable to ITSELF, `MAX_DISCOVERED_REGISTRATIONS` hit on 26 of 53 and `MAX_POSITIVE_INSTANCES` on 19. What fills the caps: instance-exposed registrations arrive before the crossed-binder ones and take the registration cap; re-derived conclusions spend the positive-instance cap; and the matcher walks the residual `forall` bodies of admitted instances as if ground. **`AXEYUM_QINST_NESTED_ACTIVATION` ships `0`**: level 1 scans the universals a staged replacement exposes BEFORE the ones a plain instance exposes (so the registration cap goes to the crossed-binder class first) and lets only a first-time conclusion spend the positive-instance cap; level 2 adds a quantifier inside a ground formula as ONE opaque e-graph leaf. Two earlier level-1 rules that SKIPPED instance-exposed registrations as duplicates each lost `TokenQueue.576` on the sweep and are recorded, not shipped: trigger selection over the instantiated body differs from the static one, so those registrations are handles. Every level goes through ADR-2120's unchanged producer/checker; level 1 changes an order and a counter, level 2 offers the matcher a subset of level 0's terms. A fixture built to size (300 instance exposures, then one crossed-binder refutation) is `unknown` at level 0 with all three caps hit, `unknown` at level 1 (the self-binding flood remains), `unsat` at level 2 with 5 tuples joined; its SAT twin and four more are not refuted at any level of either lever through loop or front door. 22 tests, 6 mutation guards each killing a named test (2 exactly one), `--check-anchors` stale=0. The 53-core sweep is in §6.

## Context

Resume-queue item 4 of the five-divisions stock-take (2026-09-16): UFLIA and
AUFDTLIRA are instance reach. Of z3's 1,025 proof instances over ADR-2113's 53
reference-minimal UFLIA cores, 46 % are nested instantiations, 36 % never
match, 17 % match and are rejected (QUANT-REACH-DIFF). QUANT-COMPOSE read the
engine and named the discard: `PositiveContext` is forced to `None` for the
whole subtree on entering a `forall` body (`collect_nested_registrations_rec`),
before ADR-2120's level is consulted, so "no activation reaches a universal
nested inside another binder". Not a fixture decision — the lane stopped before
the code half. This lane was briefed to decide it with two fixtures, split
`inactive_dropped` per core into crossed-binder versus other, build the
activation record z3 and cvc5 derive from the instance, and sweep.

## 1. The fixtures decide the reading — against its strong form

`crates/axeyum-solver/tests/quant_nested_activation_2149.rs`. Every counter
below is read through `NestedActivationStatsGuard` /
`last_nested_activation_stats`, which arms the loop's per-universal admission
census in-process; a verdict alone cannot tell "activated and refuted" from
"refuted by another route".

| fixture | isolated loop, level 0 | level 1 | front door, level 0 |
|---|---|---|---|
| (a) `∀x.(P(x) ⇒ ∀y.Q(x,y))`, `P(a)`, `¬Q(a,b)` | `unknown`: 1 registration, 0 with context, **`inert_untracked=1`**, 14 joined, 14 dropped, `dropped_untracked=14`, `dropped_crossed_binder=0`, 0 discovered | `unsat`: 1 handed off, 1 discovered (the outer instance), 1 staged, 0 dropped | `unsat`: the front door rewrites `⇒` into `or`/`not`, the path is `or`-only, level 0 tracks it |
| (b) `∀x y.(P(x) ⇒ Q(x,y))`, same facts | `unsat`, 0 registrations | `unsat` | `unsat` |
| (c) `∀x.(P(x) ⇒ ∀u.(R(x,u) ⇒ ∀y.Q(u,y)))`, `P(a)`, `R(a,c)`, `¬Q(c,b)` | `unknown`: 2 registrations, both `untracked` (first cause wins: the `⇒` above the binder) | `unsat`: **`inert_crossed_binder=1`**, 4 dropped, all crossed-binder; **`discovered=2`** (the middle universal from the outer instance, the inner one from the staged replacement), 7 handed off, 2 staged, 1 rebuild | `unsat` |
| (d) = (c) with `or`/`not` | `unsat` with the same counters as (c) at level 1 | `unsat` | `unsat` |

**So: the STATIC registration of a crossed-binder universal is inert, exactly
as read, and the engine still activates the universal — through
`NestedDiscovery::scan`, which re-walks every admitted instance and every
staged replacement for positive-position universals and registers them with
the instance as owner. That is the reference solvers' mechanism, and it
shipped as ADR-2120's slice 3.** The brief's fixture (a) is not the crossed
shape at all: the outer prefix is peeled before the walk (ADR-2120 §1a), so its
inner universal is in the outer's matrix and its block at level 0 is the
`⇒` whitelist, not the binder.

**What the counters also showed.** Every `rejected` replacement on (c) is a
tuple binding a variable to itself: the matcher walks the residual
`∀y.Q(c,y)` inside an admitted instance as if it were ground and matches the
registration's own trigger against its own body. Fail-closed at
`positive_instance_formula` (`contains_any_symbol`), after the handoff slot is
spent, every round. Counted as `rejected_by_checker`; §3 sizes it.

## 2. The split, as an instrument

`InertReason` is recorded on every `NestedRegistration` at the walk
(`PathTracking`: a tracked polarity or the FIRST reason tracking was lost —
first cause wins, because it names the outermost obstacle a remedy has to
remove first). The drop at the join is charged to it
(`inactive_dropped_{crossed,negative,untracked}`, printed as
`rej_nocontext_{crossed,negative,untracked}=` with `kind=` on the
`AXEYUM_QPROBE` per-universal line). Two instrument defects fixed on the way,
both of which had made the existing table a sample:

- **the table printed only at the fixpoint exit.** ADR-2120 §7a found it
  missing on 35 of 53 cores, all clock and ceiling exits. It now prints at
  every exit, labelled `exit=`; on this sweep 37 of 53 cores print it on the
  shipped arm, and the 16 that do not are 12 decided on an earlier rung
  (`q:mbqi-quick`, `q:bool-skeleton`), 1 decided by the loop's own `unsat`
  return, and 3 sledgehammer cores whose loop never reaches an exit.
- **the census and the join counters reset on every discovery rebuild**, so
  the table reported the LAST matcher's counts. They are now carried across the
  rebuild re-keyed by assertion term (a promotion shifts every registration's
  index, so carrying by position would misattribute).

The `nested-discovery` line reports the driver's own counters at every exit:
registered, uncompiled (registered but never compiled because
`MAX_DISCOVERY_REBUILDS` was spent), rebuilds, positive, staged, promoted,
rejected, rejected by the checker.

## 3. The 53-core split

`bench-results/quant-nested-activation-20260917/split.tsv`, from
`census-run.sh` + `split.py` (self-tested, with an `re.M` mutant that dies —
the trap QUANT-REACH-DIFF's classifier fell into). One binary at `faa6cac11`,
s6 physical pairs 5,13 / 6,14, 24 s / 8 GiB, `$EPOCHREALTIME`. Both arms decide
**15 of 53**, the same 15 as ADR-2120 §7 and ADR-2130 §6 measured on their OFF
arms.

| arm | cores printing a table | registrations context / crossed / negative / untracked | handed off | cut by the per-round handoff cap | `rej_nocontext` crossed / negative / untracked | cores with crossed drops | discovered | handed off and refused by the checker | cores hitting the registration / rebuild / positive-instance cap |
|---|---:|---|---:|---:|---|---:|---:|---:|---|
| shipped | 37 | 4,762 / 54 / 0 / 1,029 | 131,229 | 2,328,593 | 17,685 / 0 / 2,520,232 | 5 | 4,344 | 2,713 | 11 / 0 / 2 |
| `AXEYUM_QINST_POSITIVE_PATH=1` | 36 | 11,990 / 178 / 44 / 2 | 935,313 | 13,687,328 | 1,611,516 / 231,040 / 57,014 | 9 | 10,677 | 17,600 | 26 / 2 / 19 |

Read in order:

1. **On the shipped arm the crossed-binder class is 0.7 % of the drops**
   (17,685 of 2,537,917). ADR-2120's connective class is the other 99.3 %, and
   the untracked-first attribution is why: `⇒` above a binder is charged to
   the `⇒`. This is the histogram the brief asked for, and it says the
   crossed-binder mechanism cannot be what moves the shipped arm.
2. **At level 1 of ADR-2120's lever the crossed class is 1.6 M tuples on 9
   cores** (`TypeSigVec.005` 942,980, `ImportDeclVec.015` 380,131,
   `TypeModifierPragmaVec.013` 238,731) — real, but
   dwarfed by what happens to the tuples that DO have a context: 13.7 M are
   cut by `MAX_POSITIVE_TUPLES_PER_ROUND = 256`, and the registration cap is
   hit on 26 cores in the first round. The reach block on this arm is not the
   binder; it is the budgets.
3. **What the budgets are spent on.** The registration cap goes to whatever
   discovery scans first, and at level 0 that is the plain instances — which
   on the cap fixture leaves the one crossed-binder rescue as the 301st and
   refused. (This lane first read those instance-exposed registrations as
   duplicates of the static ones and built two rules to skip them; both lost
   `TokenQueue.576` and are recorded in §4. They are handles: trigger
   selection over the instantiated body picks different patterns.) The
   positive-instance cap is spent in part on re-derived conclusions, counted
   before the dedup. And the matcher ingests the residual `forall` bodies of
   admitted instances, so triggers match their own bodies: 17,600 handoffs
   refused by the checker at level 1.
4. **The per-core table is in the README**; the cores whose crossed class is
   nonzero are the simplify/ESC-Java ones (`TypeSigVec.005`,
   `ImportDeclVec.015`, `TypeModifierPragmaVec.013`, `Java2Html.832`,
   `NewInstanceExpr.271`, …), where a nested universal sits inside a
   registered universal's body; the boogie cores have none.

## 4. The lever

`NESTED_ACTIVATION_LEVEL = 0` (`AXEYUM_QINST_NESTED_ACTIVATION`,
`NestedActivationLevelGuard`; `config_registry.rs` row).

- **Level 1.** The universals a STAGED replacement exposes are scanned before
  the ones a plain instance exposes. Nothing is skipped: under
  `MAX_DISCOVERED_REGISTRATIONS` the order decides which class the budget
  goes to, and at level 0 the instances went first — on the cap fixture the
  one registration that refutes it was the 301st and was refused. And a
  conclusion `produced` already holds no longer spends
  `MAX_POSITIVE_INSTANCES` — the matcher re-emits a registration's tuples
  after every rebuild, and at level 0 the counter moved before the dedup,
  which is how a fixture with 248 distinct replacements reached 4,096.

  **Two earlier versions of level 1 were refuted by the sweep and are
  recorded.** The first did not scan admitted instances at all, on the
  argument that a universal a plain instance exposes sits at the same
  position of the assertion's matrix where the static walk already
  registered it with the same context and a larger tuple set. Run 1 lost
  `simplify_javafe.parser.TokenQueue.576` (`unsat` by `q:mbqi` in 4 s at
  level 0, `unknown` at 13 s with the rule). The second skipped only when the
  static registration's conclusion is ground (every binder of the assertion
  is used by the inner body) — and lost the same core on run 2, and on a
  local probe at levels 0/1/2/3 with the skip isolated at 3. The argument is
  wrong at the TRIGGER: selection over the instantiated body has fewer
  variables to cover and picks a different, often more permissive, pattern,
  so the instance's registration fires on ground terms the static one
  cannot. An instance-exposed registration is a handle, not a duplicate.
  `level_1_registers_exactly_what_level_0_registers` pins that it stays, on
  the crossed shape and on the shape whose inner universal does not use the
  outer binder.

- **Level 2.** In addition, `InstBridge::add_term` adds a `Forall`/`Exists`
  inside a ground formula as one opaque leaf keyed by the term and never walks
  its body. z3 internalizes a nested quantifier as one Boolean variable
  (`smt_internalizer.cpp:656`) and its body not at all until instantiated;
  this is the same rule.

**Soundness does not depend on the level.** Every registration any level
compiles goes through the same `positive_instance_formula` producer and
`check_positive_replacement` checker (ADR-2120); level 1 registers a subset of
level 0's registrations; level 2 offers the matcher a subset of level 1's
terms, and a match on a non-ground term was never a sound instance — the
checker refused every one. The certificate route is unchanged:
`the_level_2_refutation_carries_a_checked_replacement_chain` requires the cap
fixture's refutation to carry a `PositiveReplacement` whose owner is itself
derived, and every derivation to pass `check_quantifier_ground_derivation`.

## 5. Tests and mutation

22 tests. The lever's own: the shipped level fails the cap fixture with all
three caps hit and self-binding handoffs refused; level 2 refutes it through a
discovered registration with 5 tuples joined, nothing capped, nothing refused;
level 1 stops the positive-instance spend (`positive_instances < 4096`) but
the flood remains and it is still `unknown` — stated, not inferred; the cap
fixture's SAT twin and the four SAT shapes at every level of both levers
through loop and front door; level 1 registers exactly what level 0 registers
on the crossed shape and on the `TokenQueue.576` shape; level 2 hands off no
self-binding tuple; no-loss across levels; the certificate chain; the guard's
thread-locality.

`mutation_controls.py qinst-nested-activation`, baseline 22 green:

| guard deleted | killed |
|---|---|
| crossing a binder is attributed to the binder | 3 |
| the first refusal on the path is the one attributed | **1** — `at_level_0_the_connective_above_the_binder_is_the_attributed_obstacle` |
| a crossed-binder drop is charged to the crossed-binder class | 2 |
| level 1 scans the staged replacements before the instances | 2 |
| a re-derived conclusion does not spend the positive-instance cap again | **1** — `level_1_stops_spending_the_positive_instance_cap_on_duplicates_but_the_flood_remains` |
| level 2 adds a quantifier as an opaque leaf | 4 |

`--check-anchors`: `suites=205 anchors=1193 stale=0`. Two of six kill exactly
one test; the rest are reported as measured rather than trimmed.

## 6. The 53-core sweep

SWEEP-PLACEHOLDER

## Consequences

CONSEQUENCES-PLACEHOLDER

[ADR-2113]: adr-2113-uflia-the-instance-we-never-produce.md
[ADR-2120]: adr-2120-quantifier-activation-by-assignment.md
[ADR-2130]: adr-2130-the-quantifier-session-hosts-arithmetic.md
