# ADR-1908: The native core is the one CDCL(T) driver; `CdclT` is demoted to a differential oracle; `Dpll` is a separate, still-open question

Status: accepted
Index-summary: `axeyum-solver` runs THREE theory-search implementations, and [ADR-1703](adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md) — which retired BatSat — **never mentions `CdclT`** (0 hits against a 24-occurrence `BatSat` positive control in the same file), so the older CDCL(T) driver's retirement had never been decided. Decision, in three parts. (1) **The native core (`solve_native` over `axeyum-cnf`'s proof-producing `Cdcl`) is the one CDCL(T) driver**; the four remaining `CdclT` shipping sites migrate in the inventory's dependency order, cheapest-first: `uflia_online`+`uflra_online` together (one dispatch arm split by sort at `auto.rs:4484`), then warm CDCL(T) as a standalone slice, then `qinst_egraph`, and `ufbv_online` last **or not at all** — it is a redesign needing three features the native core lacks, and must be re-argued on measured benefit rather than assumed into the plan. The reason is evidence, not speed: a `CdclT` refutation reaches the front door as `Evidence::Unsat(None)` with `trusted_steps` empty, and whether the native core is *faster* on these routes is unknown and not claimed. (2) **`CdclT` is demoted, not deleted** — ADR-1703's own precedent. It IS the differential oracle for the native core (`native_cdclt/tests.rs:312`, 8,000 runs, three-way against an independent brute force, "the check that decides whether a shipping route may be moved"), and it caught both defects of `24cb85901` including a wrong-`unsat` shape. Its 32 non-shipping construction sites — eight times its route count — are the oracle's own correctness suite and stay, and the differential must keep RUNNING: ADR-1703's BatSat referee never ran automatically once, and this demotion does not repeat that. (3) **`Dpll`/`IncrementalArithDpll` is NOT retired here and this ADR does not claim "one driver"**: it has **7 shipping sites against `CdclT`'s 4**, two of them (`uflra_online.rs:1500`, `uflia_online.rs:1981`) inside the very modules migrated first, where it is the enumerative fallback *beneath* the CDCL(T) body rather than a competitor to it. After every `CdclT` route moves, the solver has two theory-search implementations, not one. Verdict-invariance, not speed, is the acceptance test: this repo has already measured an engine swap costing a give-up REASON (`ea85c9813`), a verdict (`f429b3b8a`, `Sat`→`Unknown` on a different-but-correct model), and `--trace` twice (`fdfd3a04d`, `cb5cd9090`) — two of the four caught only by the FULL `--lib --features full` sweep, so that sweep, not the route's own suite, gates every migration.
Date: 2026-09-10

## Context

Phase B0 of
[`docs/solver-comparison-2026-09/12-cdcl-consolidation-plan.md`](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md),
resting on
[the `CdclT` → native core site inventory](../03-measurements/cdclt-native-migration-inventory-2026-09-10.md)
(lane R-A, 2026-09-10).

### The gap this record closes

[ADR-1703](adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
made `axeyum-cnf`'s proof-producing core the SAT engine and demoted BatSat to a
differential oracle. It is routinely read as having settled the engine question.
It did not settle this one:

```
$ grep -c 'CdclT' docs/research/09-decisions/adr-1703-*.md
0                                  # exit 1
$ grep -o 'BatSat' docs/research/09-decisions/adr-1703-*.md | wc -l
24                                 # positive control
```

Re-verified by this lane. (R-A reported 30 for the control; `grep -c` counts
matching *lines* and `grep -o | wc -l` counts *occurrences*, and this file has
24 of the latter. The discrepancy does not touch the claim — the control is
strongly non-empty on either method, so the zero is a real negative and not an
empty grep reported as a finding.)

So **the retirement of the older CDCL(T) driver has never been decided**, and a
lane migrating a route has been acting on an inference from a neighbouring ADR.

### What is actually running

Three theory-search implementations coexist in `crates/axeyum-solver`, and the
intuitive framing — "retire the second CDCL(T) driver, leaving one" — is wrong
on its face:

| driver | shipping construction sites | proof output |
|---|---:|---|
| `solve_native` (native core, `native_cdclt.rs:536`) | 5 | ✅ ADR-1704 two-stream artifact |
| `CdclT` (`cdclt.rs`, 4,176 lines) | 4 | **✗ none** |
| `Dpll` / `IncrementalArithDpll` | **7** | ✗ none |

The two CDCL(T) sets are **disjoint**: no module has both a shipping `CdclT`
site and a shipping `solve_native` site. The migration is done-or-not per
module, cleanly — 5 done, 4 remaining — not half-done everywhere. Where a
module appeared to have both, the `CdclT` half was always a unit test. (The
plan's iteration-1 claim that three modules ran both engines came from a
`grep -c` that classified `#[cfg(test)]` sites as routes; its §6 records the
correction.)

`CdclT` is pinned by **32 non-shipping construction sites** — eight times its
route count. Retiring the *type* is mostly a test-rewrite problem; retiring the
*routes* is not, and this ADR is about the routes.

### The `Dpll` composition, recounted

This lane re-classified every `Dpll::new` / `IncrementalArithDpll::new` site by
hand, because R-A's classifier tracks `#[cfg(test)] mod` and **not `#[cfg(test)]`
on a bare item** — a limitation R-A names, and which it caught once
(`euf_egraph.rs:2695`) and missed twice. The total is unchanged at 7; the
composition is not:

| site | R-A | recounted | why |
|---|---|---|---|
| `lra_online.rs:4106` | shipping | shipping | — |
| `lia_online.rs:2154` | shipping | shipping | — |
| `uflra_online.rs:1500` | shipping | shipping | the enumerative fallback beneath C4 |
| `uflia_online.rs:1981` | shipping | shipping | the enumerative fallback beneath C3 |
| `lra_online.rs:4247` | shipping | **test** | inside `#[cfg(test)] fn run_online_diag` (`:4191`) |
| `lia_online.rs:2306` | shipping | **test** | inside a `#[cfg(test)]` item at `:2277` |
| `auto.rs:~10973` | shipping | **test** | inside `#[cfg(test)] mod tests` (`:10160`) |
| `euf_egraph.rs:2695` | test (flagged) | test | the `Dpll` struct itself is `#[cfg(test)]` (`:2182`) |
| `euf.rs:905` | shipping | shipping | before the file's only `#[cfg(test)]` (`:2184`) |
| **`dpll_lia.rs:1384`** | **absent** | **shipping** | `new_with_deadline`, in `arith_dpll_admission_preflight` |
| **`dpll_lia.rs:1465`** | **absent** | **shipping** | `new_with_deadline` |

7 either way, so the headline "`Dpll` has more shipping sites than `CdclT`"
survives — but two of the three rows it rested on are tests, and two
`new_with_deadline` sites it never counted are real. The general form is one
this repository keeps paying for: **a classifier's stated limitation fires more
than once, and a count can be right while the inventory under it is wrong.**

## Decision

### 1. The native core is the one CDCL(T) driver

Every shipping `CdclT` route moves to `solve_native` over `axeyum-cnf`'s
proof-producing `Cdcl`, in R-A's dependency order, which inverts the intuitive
one:

1. **`uflia_online` + `uflra_online`, together.** One dispatch arm split by
   sort at `auto.rs:4484`; moving one leaves QF_UFLIA and QF_UFLRA on different
   engines with different give-up reasons, which is the failure mode
   `ea85c9813` already recorded once. Their recorded deferral reason — the
   `--trace` gap — **was fixed in the same commit that recorded it**
   (`fdfd3a04d`), verified by this lane against that commit's body and the
   `layer_stats_enabled()` bridge now in `solve_native`.
2. **Warm CDCL(T) as a standalone slice.** Nothing migrates in this step. It is
   the one missing feature under both hard sites, and the core already poses
   the design question itself (`proof_sat.rs:2572-2579`): a new `NativeTheory`
   trait method, or a fresh theory instance per solve.
3. **`qinst_egraph`.** Its `add_checked_batch` is already `backtrack_to_root` →
   insert → `solve`, which *is* `NativeIncrementalCdcl`'s between-solves
   discipline. Highest evidence payoff per unit of work: it is refutation-only
   ("never produces product SAT", `qinst_egraph.rs:3547`), so every verdict it
   produces today reaches the front door with no trusted step.
4. **`ufbv_online` last, or not at all.** It needs three features the native
   core lacks, one of which (dormant variables) does not exist in `axeyum-cnf`
   in any form, and one of which (mid-search clause insertion at a non-root
   level) contradicts `add_input_clause`'s own
   `debug_assert!(self.trail.is_empty())` (`proof_sat.rs:2486`). It is a
   **redesign, not a swap**, and unlike `qinst_egraph` it is not
   refutation-only, so the evidence payoff is smaller. It is explicitly **not**
   assumed into this decision: if warm CDCL(T) lands and `qinst_egraph`
   migrates cleanly, `ufbv_online` is re-argued on measured benefit.

**The reason is evidence, not speed.** `CdclT` emits no proof of any kind — no
DRAT stream, no theory-lemma enumeration, no checkable artifact; established by
grepping the whole file for `drat|proof|refutation|certificat|lrat|clause_trace`
and finding only prose citing `proof_sat.rs`, the English word "refutation" for
the `Unsat` verdict, and a `farkas_certificates` counter copied from the theory.
A `CdclT` refutation reaches the front door as `Evidence::Unsat(None)` with
`trusted_steps` empty.

Whether the native core's heuristics are *faster* on these four routes is
**unknown and not claimed**. No A/B is committed for any of them; the only
measured migration numbers in the tree are QF_IDL's (`9a6786e84`: 27/50 → 31/50,
PAR-2 −12.9%, zero verdict changes). The native core's heuristic advantage is
also mostly latent rather than shipped — `solve_native` deliberately pins
`initial_phase: true, target_rephase: false` to keep the swap a swap, and mode
switching and the phase schedule are opt-in experiment arms behind
`AXEYUM_SEARCH_PROFILE`.

### 2. `CdclT` is demoted to a differential oracle, not deleted

ADR-1703's precedent applies exactly, and with a stronger warrant than it had.

`native_cdclt/tests.rs:312`,
`the_two_engines_and_a_brute_force_agree_on_random_instances`: 4,000 random
CDCL(T) instances × both explanation channels = 8,000 runs, each decided by
`CdclT`, by `solve_native`, **and** by an independent brute force over the
Boolean skeleton and the theory's semantics — so "the engines agree" cannot
mean "both are wrong". It asserts zero disagreements and requires >100 sat and
>100 unsat in the population, so it cannot pass vacuously. Its own docstring:
*"The gate. … A single disagreement is a hard failure: this is the check that
decides whether a shipping route may be moved."*

It has already earned its keep. Running the two engines against each other
found both defects of `24cb85901` — a panic in `CdclT`, and a **wrong-`unsat`
shape** in `proof_sat.rs` where `explain` was asked for a conflict CORE at a
site where the handle stood for a propagation REASON, producing 39 engine
disagreements and installing as an ADR-1704 *input* clause something the theory
does not entail. Neither was found by inspection.

Therefore:

- **`CdclT` stays in the tree** after all four routes migrate, moved behind
  `#[cfg(test)]` or a feature gate — a retirement from *shipping paths*, which
  is precisely what ADR-1703 did to BatSat.
- **Its 32 non-shipping construction sites stay** as the oracle's own
  correctness suite. They are not migration debt; a differential oracle with no
  tests of its own is not an oracle.
- **The differential must RUN.** ADR-1703's BatSat referee never ran
  automatically at all — no gate, CI job, justfile recipe or hook uses
  `--features batsat-reference` — so it provided zero automatic assurance from
  the day it landed. This demotion does not repeat that: `CdclT`'s differential
  is inside `axeyum-solver`'s `--lib --features full` sweep today and stays
  there. **A gated oracle nothing invokes is decoration**, and at this
  repository's scale a checker that cannot fail is worse than no checker.
- The `#[cfg(feature = "bench-internals")] #[doc(hidden)]` re-export at
  `lib.rs:272` is not an obstacle: its sole consumer is
  `benches/cdclt_propagate.rs`, one bench to keep or drop, not an API break.

### 3. `Dpll` is out of scope, and this ADR does not claim "one driver"

`Dpll`/`IncrementalArithDpll` has 7 shipping sites to `CdclT`'s 4, and two of
them sit inside `uflra_online` and `uflia_online` — the first two modules this
plan migrates. It is **not** a competing CDCL(T) driver: at those two sites it
is the *enumerative fallback beneath* the CDCL(T) body, reached when the
combined driver declines. A different layer, not a duplicate of the same one.

This ADR therefore:

- **does not retire `Dpll`**, and
- **does not claim the solver reaches "one theory-search implementation".**
  After every `CdclT` route migrates, the solver has **two**: the native core on
  the CDCL(T) paths, and `Dpll` on the enumerative fallbacks. Claiming otherwise
  would be the exact defect this record exists to fix — a decision that reads as
  settling more than it measured.

Whether the `Dpll` fallbacks should themselves be consolidated is a separate,
open question, and it needs its own inventory first: the recount in §Context
shows that even the site list for it is not yet reliable.

## Consequences

**The acceptance test for every migrated route is verdict-invariance, not
speed.** This repository has already measured, at four separate sites, that
moving a route between these engines changes things other than the clock:

| what moved | commit | shape |
|---|---|---|
| a **verdict** | `f429b3b8a` | native decides `false` first and rephases to the best assignment on restart; `CdclT` decides `true` first and does not rephase. Both find correct models; they find *different* ones. An MBQI test went `Sat` → `Unknown` on that alone, because MBQI picks its instantiation terms out of the model it is handed. |
| a **give-up reason** | `ea85c9813` | `CdclT` tests its deadline at the top of its loop; the core checks less eagerly. On `x > 0 & x < 1` at a zero budget the core returned `Sat`, which `lia_theory` turned into `Unknown{Incomplete}` where `CdclT` gave `Unknown{Timeout}` — and `dpll_lia::check_with_arith_dpll` **branches on that kind**, so which fallback ran had changed with no verdict moving. |
| `--trace` | `fdfd3a04d` | `CdclT` reads the collection flag at construction; the core takes it as a solve option. Nothing bridged them, so every migrated route silently stopped answering `--trace`. |
| `--trace`, again | `cb5cd9090` | seven counters left at `Default` behind a comment claiming they were "not measured", when every one was already in the argument in hand. `final_check_core_widenings=n/a` on every QF_LRA file — and **an absent number reads as a settled one** to anyone who measured it on the old route. |

Two of those four were losses of *observability*, not verdicts, and **both were
caught only by the full `--lib --features full` sweep, not by the route's own
suite.** So:

- **Every migrated route runs the full `-p axeyum-solver --lib --features full`
  sweep**, plus `--test corpus_regression`, plus the z3 differential fuzzes for
  an arithmetic route — with a **nonzero test count stated**, since all three
  compile to nothing and exit 0 without their feature flag, and a
  "running 0 tests ... ok" is not a gate that ran.
- **A migration reports its before/after verdict columns** on the committed
  corpus and on the parity slices. A changed verdict, give-up reason or model is
  **the finding**, to be reported — never something to tune until it disappears.
- **`solve_native`'s pinned `initial_phase: true, target_rephase: false` is
  load-bearing and stays pinned** until a measurement says otherwise. It is the
  mitigation for `f429b3b8a`; unpinning it is a separate decision.
- **An observability channel a migrated route feeds is part of its contract.**
  Where `CdclT` maintains a counter unconditionally and the native core
  maintains it only under `collect_layer_stats`, the counter is *ungated on the
  native side* rather than the route's consumer being weakened — an unmeasured
  run is not a measured zero, and a route that starts reporting zero where it
  used to report a number is the `cb5cd9090` shape again.

**What this ADR deliberately leaves open**, so a later reader does not mistake
it for settled:

- Whether the native core is *faster* than `CdclT` on the four remaining
  routes. Unknown; no A/B is committed for any of them.
- Whether `ufbv_online` migrates at all.
- Whether warm CDCL(T) is a `NativeTheory::reset` method or a fresh theory
  instance per solve.
- Whether the `Dpll` enumerative fallbacks consolidate, and on what evidence.

## Alternatives rejected

**Delete `CdclT` once its routes migrate.** It is the differential oracle (§2),
and it caught a wrong-`unsat` shape. Deleting it leaves the native CDCL(T) core
checked only against itself and against brute force on instances small enough to
enumerate. Rejected on the same reasoning ADR-1703 used for BatSat, with a
stronger warrant: BatSat's referee had never fired; this one has.

**Fold this into ADR-1703's Slice 2 (the BatSat cleanup).** Rejected. Slice 2 is
a documentation-and-dependency sweep over a decision already made; this is a
decision not yet made about a different driver. Riding in as a neighbour is how
`CdclT`'s retirement came to be treated as decided in the first place.

**Migrate `ufbv_online` for uniformity.** Rejected. Three absent features, one
with no counterpart anywhere in `axeyum-cnf`, and its refinement loop is built
around two the core forbids. "Uniformity" is not a measurement.

**Claim "one theory-search driver" as the exit criterion.** Rejected as false
(§3). `Dpll` has more shipping sites than `CdclT` does, two of them inside the
first two modules to migrate.

**Lead with warm CDCL(T)** because it unblocks the most sites. Rejected: it
unblocks 2 of 4 and carries an open design question, while the other 2 are
unblocked by a few lines of plumbing and were waiting on a deferral reason that
had already been fixed in the commit that recorded it. Half the remaining
migration is cheap; leading with the expensive half has the order backwards.

## References

- [Consolidation plan, Phase B](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md)
- [`CdclT` → native core: site inventory, parity matrix and dependency order](../03-measurements/cdclt-native-migration-inventory-2026-09-10.md)
- [ADR-1703 — the native core is the SAT engine; BatSat is demoted to a differential oracle](adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
- [ADR-1701 — the theory interface gains `final_check`, a driver-owned queue, lazy explanation and dynamic atoms](adr-1701-the-theory-interface-gains-final-check-a-driver-owned-queue-lazy-explanation-and-dynamic-atoms.md)
- [ADR-1704 — CDCL(T) `unsat` is two streams](adr-1704-cdclt-unsat-is-two-streams-a-boolean-refutation-over-cnf-plus-enumerated-theory-lemmas.md)
