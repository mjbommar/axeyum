# ADR-1913: B4's dormant-variable blocker is refuted and its subject was the wrong file; the warm BV client is a measured swap gated on one probe, not a redesign

Status: accepted
Index-summary: Phase B4 — the last un-migrated `CdclT` route — was described as a redesign needing three absent features, and ADR-1908 placed it "last **or not at all**". Verification changes the answer. (1) **The subject was the wrong file**: B4's "warm BV client" was read as `incremental.rs` / `IncrementalBvSolver`, which contains **zero** `CdclT` (control: `ufbv_online.rs` has 18) — it is the warm *bit-blasting* solver over `IncrementalCnf`, already native, nothing to migrate. The real subject is `ufbv_online.rs` (R-A's C1), which ADR-1908's own text names correctly. (2) **Obstacle 3 is refuted**: dormant variables DO exist in `axeyum-cnf`, under the name `branchable` (21 occurrences) — R-A's grep for the three obvious spellings of the name was name-blind, and its zero is real but its conclusion is not. The native constructor *derives* the dormant set (`proof_sat.rs:2416-2418`) where `CdclT` makes the caller pass it, and `ufbv_online.rs:2973-2975` is that same computation re-implemented by hand. The dormancy is also not verdict-load-bearing: the refinement scan reads `theory.bv.candidate_assignment()`, not the trail. (3) **Obstacles 1 and 2 are confirmed but mispriced**: the warmth mid-search insertion protects is ONE ROUND DEEP — a fresh `CdclT` is built at `ufbv_online.rs:1386` inside the outer `loop` at `:1048`, so the route already discards its whole search routinely. Decision: B4 is **reclassified from redesign to a swap plus one loop restructure**, ordered after B3, and **gated on a decoupling probe that measures the migration's only real cost without doing the migration** — keep `CdclT`, replace mid-search insertion with backtrack-to-root-then-insert, and compare. Pre-registered falsifiers, any one of which returns B4 to "stay on `CdclT`": any verdict change, any decided→`Unknown` move, PAR-2 up more than 15%, or a fixture showing `cdclt.rs:1382`'s propagation skip is verdict-load-bearing. "One driver" is explicitly NOT a reason (ADR-1908 keeps `CdclT` as the oracle anyway); the reason is evidence, and even that is bounded — `warm_theory` sets `record_proof: false` and the artifact is a refutation modulo trusted theory lemmas.
Date: 2026-09-10

## Context

Phase B4 of
[`docs/solver-comparison-2026-09/12-cdcl-consolidation-plan.md`](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md),
resting on
[the `CdclT` → native core site inventory](../03-measurements/cdclt-native-migration-inventory-2026-09-10.md)
(lane R-A) and
[warm CDCL(T) on the native core](../03-measurements/warm-cdclt-native-2026-09-10.md)
(lane E3, [ADR-1909](adr-1909-warm-cdclt-is-one-theory-push-pop-scope-per-solve.md)).

[ADR-1908](adr-1908-the-native-core-is-the-one-cdclt-driver-cdclt-is-demoted-to-an-oracle.md)
made the native core the one CDCL(T) driver and migrated its routes
cheapest-first, deliberately refusing to assume this one in:

> **`ufbv_online` last, or not at all.** It needs three features the native core
> lacks, one of which (dormant variables) does not exist in `axeyum-cnf` in any
> form … It is a **redesign, not a swap** … it is re-argued on measured benefit.

This ADR is that re-argument. The verification behind it, with every claim at a
`file:line` and status words used strictly, is in
[the B4 verification note](../03-measurements/warm-bv-cdclt-b4-verification-2026-09-10.md)
(lane E7). Nothing was migrated to produce it and no shipping code changed.

### The subject was the wrong file, and that is not a clerical point

The plan's B4 prose says "the warm BV client". That resolves naturally to
`crates/axeyum-solver/src/incremental.rs`, `IncrementalBvSolver` — and it is
wrong:

```
$ grep -o 'CdclT' crates/axeyum-solver/src/incremental.rs | wc -l
0
$ grep -o 'CdclT' crates/axeyum-solver/src/ufbv_online.rs | wc -l          # positive control
18
$ grep -o 'IncrementalCnf' crates/axeyum-solver/src/incremental.rs | wc -l # control: the file is read
9
```

`IncrementalBvSolver` (`incremental.rs:795`) is the warm **bit-blasting** BV
solver — `IncrementalLowering` + `IncrementalCnf` (`:796-797`). It is already
entirely on `axeyum-cnf`'s native stack and has **nothing to migrate**. ADR-1908
never claimed otherwise; its decision text says `ufbv_online` throughout. The
ambiguity is the plan's summary line, and it survived into a lane brief.

The real B4 subject is `ufbv_online.rs`: one shipping `CdclT::new` at `:1386`
inside `solve_cdclt_round` (`:1338`), plus one `#[cfg(test)]` helper at `:3330`,
reached from `auto.rs:4196` / `:4198` as routes `aufbv-online-cdclt` and
`ufbv-online-cdclt`, and from `auto.rs:5381`.

The general form is one this repository keeps paying: **a phase summary is not a
site inventory, and a lane that inherits the summary's noun can verify the wrong
file for a day.**

### The three obstacles, verified

| obstacle | status | evidence |
|---|---|---|
| 1. never backtracks | **confirmed** | 8 `backtrack` occurrences in `ufbv_online.rs`, all module prose (`:32`, `:34`, `:886`) or test names (`:3403`, `:3994`-`:3998`). No `backtrack_to_root`. Control: `qinst_egraph.rs:3652` |
| 2. `add_permanent_clause` with a full trail | **confirmed** | calls at `:1453`, `:2364`, `:2393`, inside the refinement loop at `:1400`, after `Outcome::Sat`; `solve_inner` (`cdclt.rs:2361`) resets nothing; the method's own doc (`cdclt.rs:774-777`) says "under a partial or total assignment". Native: `debug_assert!(self.trail.is_empty())` (`proof_sat.rs:2561`) |
| 3. dormant variables absent from `axeyum-cnf` | **REFUTED** | the concept exists as `branchable`, 21 occurrences |
| 4. mid-search variable growth (folded into 3 by R-A; separate) | **present**, one behavioural difference | `Cdcl::register_theory_atoms` (`proof_sat.rs:3921`) via `NativeTheory::take_new_atoms` |

#### Why obstacle 3 is refuted

R-A established it by grepping `axeyum-cnf` for `inactive|dormant|activate_variables`.
That zero **reproduces** — and the conclusion drawn from it does not follow. The
mechanism is there under a different name:

| mechanism | `CdclT` | native core |
|---|---|---|
| the flag | `active: Vec<bool>` | `branchable: Vec<bool>` (`proof_sat.rs:2021`) |
| initial dormant set | **caller computes and passes** it (`with_inactive_variables:705`) | **constructor derives it**: `vec![false; n]` then `true` per literal occurrence (`proof_sat.rs:2416-2418`) |
| activate on insertion | `add_permanent_clause` → `activate_variables:752` | inline in `add_input_clause` (`proof_sat.rs:2602-2609`) |
| append dormant | `add_theory_variable` → `active.push(false)` (`:726`) | `ensure_vars` → `branchable.resize(count, false)` (`proof_sat.rs:2540`) |
| public reservation API | — | `NativeIncrementalCdcl::reserve` (`proof_sat/incremental.rs:470`) |
| decision filter | `pick_unassigned:1942` | heap holds only branchable, asserted both ways (`proof_sat.rs:6335-6341`) |

And `ufbv_online.rs:2973-2975` computes `skeleton.active_variables` as "true for
every variable occurring in a clause" — the **same computation** as
`proof_sat.rs:2416-2418`. The whole dormancy apparatus this route carries
(`inactive_reserved_row_variables:1292` + `with_inactive_variables`) is a
hand-rolled re-implementation of a native default. On this axis the native core
is *more* automatic, not less.

Empirically anchored, with nonzero counts confirmed rather than exit statuses:
`axeyum-cnf --lib` **634 passed**;
`unused_low_variables_do_not_delay_sparse_high_projection` **1 passed**
(200,000 variables, 2 branchable, `proof_sat.rs:6348`);
`proof_sat::incremental::warm_theory` **11 passed**.

**Is the dormancy essential?** No, on two independent grounds. The capability
exists natively (above); and it is not verdict-load-bearing here, because the
dormant set is by construction "occurs in no clause" and the refinement scan
takes its model from `theory.bv.candidate_assignment()` (`ufbv_online.rs:1416`),
never from the Boolean trail.

**One asymmetry survives and is stated, not waved past.** `CdclT` also *drops*
theory propagations naming an inactive variable (`cdclt.rs:1382`); the native
`theory_round_body` (`proof_sat.rs:5052-5100`) has no such guard and enqueues
them. Both are sound. It is a search-trajectory difference, and it is the first
pre-registered falsifier below.

#### Why obstacles 1 and 2 are confirmed but mispriced

`solve_cdclt_round` builds a **fresh `CdclT`** at `:1386` and is called from a
bare `loop {` at `ufbv_online.rs:1048`. The route therefore **already throws away
the entire search** — learned clauses, VSIDS activities, saved phases — at every
outer refinement round; `stats.rounds` counts the rebuilds.

So the warmth that mid-search insertion protects is *one round deep*, and the
cost of restructuring to backtrack-to-root-then-insert is bounded above by a loss
this route already absorbs routinely at a coarser grain. That is what moves B4
from "redesign" to "measure it" — and it is a bound, not a measurement: how much
of the per-round work the inner loop actually saves is **not known**.

## Decision

### 1. B4's subject is `ufbv_online`; `IncrementalBvSolver` is not a migration target

The plan's B4 line is to be read as naming `ufbv_online.rs`. `IncrementalBvSolver`
is already on the native stack and no work is owed against it. Any future brief
that says "the warm BV client" must give the path.

### 2. B4 is reclassified from a redesign to a swap plus one loop restructure

ADR-1908's "three features the native core lacks" is now: **one feature it has
under another name** (dormancy → `branchable`), **one it has with a stated
behavioural difference** (mid-search variable growth → `register_theory_atoms`),
and **one genuine restructure** — the inner refinement loop must adopt the
`qinst_egraph` discipline of `backtrack_to_root` → insert → resume, which
[ADR-1909](adr-1909-warm-cdclt-is-one-theory-push-pop-scope-per-solve.md)'s warm
object supports directly.

This is a reclassification of difficulty, **not an instruction to migrate.**
B4 stays behind B3 in the queue: `qinst_egraph` exercises the warm native path on
a real shipping route first, and B4 inherits whatever that finds.

### 3. B4 is gated on a decoupling probe, which measures the cost without paying it

The migration bundles two changes — a loop restructure and an engine swap — whose
costs would be inseparable after the fact. They are separable before it.

**The probe:** keep `CdclT`, and replace the three mid-search
`add_permanent_clause` calls (`:1453`, `:2364`, `:2393`) with
`backtrack_to_root` → insert → resume. `CdclT` already has
`backtrack_to_root` as an addressable op (`cdclt.rs:905`), so this needs no new
core feature in either engine. It isolates **the only thing the migration costs
that the native core cannot do**, with the engine held fixed.

**The population:** the committed QF_UFBV / QF_AUFBV corpus slice, plus
`crates/axeyum-solver/tests/ufbv_online_differential_fuzz.rs` and
`aufbv_online_differential_fuzz.rs`, plus the full
`-p axeyum-solver --lib --features full` sweep, which ADR-1908 establishes as the
gate that catches engine-swap deltas the route's own suite misses.

**Recorded per run:** every verdict; `InterfaceRefinementStats.rounds`; PAR-2 on
the slice; and the reference-frame lines the frontier ratchet prints, since these
numbers move with machine load.

**If the probe passes** (definition in §4), B4 is admitted as a swap onto
`NativeIncrementalCdcl::warm_theory` + `NativeTheoryAdapter`, carrying the
obligations in §6.

### 4. Pre-registered falsifiers

Any **one** of these returns B4 to "stays on `CdclT`", and this ADR is reopened
rather than amended:

1. **A fixture where `cdclt.rs:1382`'s propagation skip is verdict-load-bearing.**
   Delete the `if !self.active[var] { continue; }` guard in a scratch tree and run
   the population. If any verdict moves, the dormancy is doing semantic work this
   ADR says it is not, §Context's ground B is wrong, and the refutation of
   obstacle 3 is incomplete.
2. **The probe changes any verdict** on the corpus slice or either differential
   fuzz. Verdict-invariance, not speed, is ADR-1908's acceptance test and it is
   absolute here.
3. **The probe moves any benchmark from decided to `Unknown`.** A budget give-up
   is a lost verdict wearing a different word, and `ea85c9813` is the recorded
   precedent for an engine change costing a give-up *reason* alone.
4. **The probe raises PAR-2 on the slice by more than 15%**, measured with the
   reference-frame lines read and the run not marked NOT COMPARABLE. 15% is
   chosen against the one measured migration in the tree, QF_IDL's `9a6786e84`
   at PAR-2 **−12.9%**: a regression larger than the only migration gain we have
   ever measured cannot be paid for by an evidence improvement that is itself
   partial (§5).
5. **Turning `record_proof: true` on for this route is not affordable.** If the
   artifact cost makes the evidence gain unrealizable in practice, the sole
   remaining reason to migrate is gone and B4 should stay put.

Falsifier 1 is runnable today and does not depend on the probe. It is the
cheapest way to find out this ADR is wrong, and it should be run first.

### 5. What is at stake, stated without inflation

**The reason to migrate is evidence.** `ufbv_online.rs` has **0** occurrences of
`Evidence`/`trusted_step`/`TrustedStep`, and `auto.rs:4205-4211` returns a bare
`Ok(Some(CheckResult::Unsat))`. Every QF_UFBV / QF_AUFBV refutation from this
route reaches the front door with no trusted step — exactly the condition
ADR-1908 gives as the reason for the whole consolidation.

**The gain is bounded, and this ADR will not let it be quoted as more:**

- `NativeIncrementalCdcl::warm_theory` sets `record_proof: false`
  (`proof_sat/incremental.rs:276-281`); the doc prices the alternative as
  gigabytes on a long CDCL(T) search, and
  `the_warm_path_records_no_proof_by_default` pins it. Migration produces an
  artifact only if that knob is turned on, and its cost here is **not measured**.
- The artifact is the ADR-1704 two-stream shape: a DRAT refutation of
  (skeleton ∧ installed theory lemmas). This route's BV conflicts are re-solved
  UNSAT conjunctions (`ufbv_online.rs:60-61`), not certificates, so the lemmas
  are trusted by assertion. The honest claim is "a checkable Boolean refutation
  modulo named theory lemmas", not "a proof".

**"One driver" is explicitly not a reason.** ADR-1908 keeps `CdclT` in the tree
as the differential oracle regardless — `native_cdclt/tests.rs:312` is the check
that decides whether a shipping route may be moved — so consolidation for its own
sake buys nothing here. Anyone citing tidiness for B4 is citing something this
ADR refuses.

**Speed is not a reason either, in either direction: did not run.** No A/B exists
for this route, and no corpus route census for `ufbv-online-cdclt` exists in the
tree — three tracked files mention the route name and none counts benchmarks
through it. Producing that census is a prerequisite of the probe, not a finding
of it.

### 6. If B4 migrates, three obligations travel with it

1. **Carry the release-active alignment check forward.** `ufbv_online.rs:873-878`
   returns a `SolverError::Backend` when `euf_atom != bv_atom || bv_atom !=
   solver_atom`. The adapter's equivalent is a `debug_assert_eq!`
   (`native_cdclt.rs:445`) over a **mirrored** `next_var` (`:262`) — the exact
   shape E3 found desyncing silently in release. `ufbv_online` is the only
   un-migrated route that both grows variables mid-search and inserts clauses, so
   it is the most exposed. It must not trade a release check for a debug one.
2. **Do not compare models across the boundary.** E3's finding stands: a warm
   model is not the one-shot model and cannot be, because phase retention is what
   warmth is. Any test or consumer asserting a specific `ufbv` model must be
   re-anchored on replay, which this route already does
   (`ufbv_online.rs:63-65`), not on model identity.
3. **Decide `record_proof` explicitly and record the number.** Migrating with it
   off delivers none of the benefit in §5 while paying all of the risk. The
   migrating lane records the measured artifact cost or states that it did not
   run — it does not inherit E3's "gigabytes" as though it were this route's
   measurement.

## Consequences

- ADR-1908's §1 item 4 is **superseded in its reasoning, not its ordering**:
  `ufbv_online` still moves last, but "or not at all" is narrowed to "or not at
  all, if a falsifier in §4 fires". The three-absent-features justification is
  withdrawn — one of the three was a name-blind grep.
- The plan's Phase B4 text should be read through this ADR. Its "warm BV client"
  names `ufbv_online.rs`, and its "dormant variables … do not exist in
  `axeyum-cnf` in any form" is false.
- **R-A's inventory row for dormant variables is wrong and the inventory is
  otherwise sound.** This is the third time R-A's method has mis-served a
  consumer (ADR-1908 records two `#[cfg(test)]` mis-classifications) and the
  second distinct mechanism: the first was a classifier limitation R-A named, and
  this one is a name search standing in for a capability search. A future
  inventory of "does the target have feature X" must search for the **step**, not
  the name, and must state which it did.
- Nothing in the shipping path changes as a result of this ADR.

## What would falsify this decision

Beyond the five pre-registered falsifiers in §4, which are about B4's *outcome*:

1. **`branchable` turns out not to be reachable from the route's shape** — for
   instance if a warm CDCL(T) route cannot reserve dormant variables because
   `NativeIncrementalCdcl::reserve` and `take_new_atoms` growth interact badly
   across a solve boundary. §3.1's correspondence is established by reading and
   by `axeyum-cnf`'s own tests, not by a route using it.
2. **B3 (`qinst_egraph`) does not migrate cleanly.** This ADR assumes the warm
   native path works on a real route. If B3 finds otherwise, B4's cost estimate
   rests on a premise that failed and must be rebuilt from B3's findings.
3. **Someone measures the inner refinement loop saving a large share of
   per-round work.** §Context bounds that saving above by the outer rebuild; it
   does not measure it. If the inner loop turns out to carry most of the search
   on real instances, falsifier 4's threshold is the wrong instrument and the
   probe should be redesigned before it is run.
