# `CdclT` → native core: the site inventory, parity matrix and dependency order

Measured 2026-09-10 against `f91570117` (local `main`, merged into this lane's
worktree). Lane `R-A-cdclt-inventory`. **Research only — no behaviour was
changed and nothing was migrated.**

Two CDCL(T) drivers coexist in `crates/axeyum-solver`:

- `crates/axeyum-solver/src/cdclt.rs` — `CdclT`, 4,176 lines. The older driver.
  Emits no proof.
- `crates/axeyum-solver/src/native_cdclt.rs` — `solve_native`, 764 lines. A thin
  adapter onto `axeyum-cnf`'s proof-producing core
  (`crates/axeyum-cnf/src/proof_sat.rs`, 8,945 lines, plus
  `proof_sat/theory.rs`, `proof_sat/refutation.rs`, `proof_sat/incremental.rs`).

[ADR-1703](../09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
made the native core the SAT engine and retired BatSat. **It does not mention
`CdclT` at all** — verified by grepping the ADR for `CdclT` (zero hits) against a
positive control on `BatSat` (30 hits) and on `cdcl` in every casing (8 hits,
none of them `CdclT`). So a retirement plan for `CdclT` is not covered by
ADR-1703 and needs its own decision record.

---

## 0. Three corrections to the briefed picture

### 0.1 The briefed count classifies unit tests as shipping routes

It was produced by `grep -c`. Corrected:

| module | brief said `CdclT::new` | **shipping `CdclT::new`** | `#[cfg(test)]` | **shipping `solve_native`** |
|---|---:|---:|---:|---:|
| `lia_theory` | 2 | **0** | 2 | **1** |
| `lra_theory` | 2 | **0** | 2 | **1** |
| `string_theory` | 1 | **0** | 1 | **1** |
| `ufbv_online` | 2 | **1** | 1 | 0 |
| `uflia_online` | 1 | **1** | 0 | 0 |
| `uflra_online` | 1 | **1** | 0 | 0 |
| `qinst_egraph` | 1 | **1** | 0 | 0 |
| `euf_egraph` | 0 | 0 | 0 | **1** |
| `dl_online` | 0 | 0 | 0 | **1** |
| `cdclt.rs` itself | — | 0 | 24 | — |

Exact totals for `CdclT::new(`: **4 shipping, 30 `#[cfg(test)]`, 2 in test
files** (the differential harness `native_cdclt/tests.rs:289` and the bench
`benches/cdclt_propagate.rs:83`) — 36 construction sites, plus one doc-comment
match at `native_cdclt.rs:526`.

Three consequences:

1. **No module has both a shipping `CdclT` site and a shipping `solve_native`
   site.** The two sets are disjoint. The migration is not "half-done per
   module"; it is done-or-not per module, cleanly. Where a module appeared to
   have both, the `CdclT` half was always a unit test.
2. **5 routes migrated, 4 remaining** — not the even split the brief implies.
3. **`CdclT` is pinned by 32 non-shipping construction sites, eight times the
   route count.** Retiring the type is mostly a test-rewrite problem.

The brief's table also omits every module that *mentions* `CdclT` without
constructing one — `combined_theory` (9), `combined_theory_lia` (8), `layers`
(7), `lib.rs` (4), `lra_online` (3), `dpll_t`, `smtlib`, `auto`. Those are doc
comments and one `#[doc(hidden)]` re-export (§4.6), not call sites.

### 0.2 Retiring `CdclT` does not leave one driver — a third family has more shipping sites than it does

`Dpll` — a `DPLL(T)` search with 1-UIP learning and non-chronological
backjumping, generic over `TheorySolver`, documented at `lra_online.rs:2557`.
There are **two distinct structs of that name**, and `Dpll::new(` has **7
shipping sites in `axeyum-solver`** against `CdclT::new`'s 4:

| site | which `Dpll` |
|---|---|
| `lra_online.rs:4106`, `:4247` | `lra_online::Dpll` (`pub(crate)`, `:2566`) |
| `lia_online.rs:2154`, `:2306` | same |
| `uflra_online.rs:1500`, `uflia_online.rs:1981` | same, as the enumerative fallback beneath C3/C4 |
| `euf_egraph.rs:2695` | a private `euf_egraph::Dpll` — but its struct is `#[cfg(test)]` (`:2182`), so this one is test-only |

Plus `IncrementalArithDpll` (`euf.rs:905`, `auto.rs:10973`) and an unrelated
`xor_dpll::Dpll` in `axeyum-cnf`. **A plan framed as "retire the second CDCL(T)
driver" will finish and leave the solver with three theory-search
implementations.** `uflra_online` and `uflia_online` each contain *both* a
`CdclT` site and a `Dpll` site — the CDCL(T) body and the enumerative fallback
it degrades to.

### 0.3 `native_cdclt.rs`'s own route table is stale, and was wrong when written

Its module doc (`native_cdclt.rs:15-18`) lists `ufbv_online` as the **sole**
client of the incremental protocol, and the scoping commit `24cb85901`
(2026-09-07) states it outright: *"The incremental refinement protocol has ONE
client, not ten."* **`qinst_egraph` is a second one and is absent from both.**
It was not added later: `git show 24cb85901:crates/axeyum-solver/src/qinst_egraph.rs`
already contains its `CdclT::new`. The under-count is original, and it is still
the table a reader consults.

---

## 1. Site-by-site inventory

### 1.1 Shipping sites still on `CdclT` (4)

| # | site | enclosing fn | reached by | protocol |
|---|---|---|---|---|
| **C1** | `crates/axeyum-solver/src/ufbv_online.rs:1386` | `solve_cdclt_round` (`:1338`) | `check_qf_ufbv_online_cdclt` (`:931`) / `check_qf_aufbv_online_cdclt` (`:963`) ← `auto.rs:4144`, `:4146`, `:5329` | **incremental, mid-search insertion** |
| **C2** | `crates/axeyum-solver/src/qinst_egraph.rs:3628` | `OnlineQuantifierClauseSession::new_with_limits` (`:3553`) | `::new` (`:3549`) ← `qinst_egraph.rs:2194` | **incremental, root-only insertion** |
| **C3** | `crates/axeyum-solver/src/uflia_online.rs:1819` | `cdclt_combined` (`:1747`) | `check_qf_uflia_online` (`:226`) ← `auto.rs:4488`, `abv.rs:2240` | one-shot |
| **C4** | `crates/axeyum-solver/src/uflra_online.rs:1354` | `cdclt_combined` (`:1294`) | `check_qf_uflra_online` (`:143`) ← `auto.rs:4486` | one-shot |

Routing:

- C1 is the QF_UFBV / QF_AUFBV arm; `auto.rs:4137` picks `aufbv-online-cdclt`
  when `features.has_array`, else `ufbv-online-cdclt`.
- **C3 and C4 are the same function duplicated per sort.** Both are named
  `cdclt_combined`, both one-shot, both over a `CombinedIncremental*`, and
  `auto.rs:4484` splits between them on one condition: *"a real-sorted term
  anywhere routes to the `QF_UFLRA` decider, otherwise the integer one."*
- C2 is the ADR-0119 retained equality-abstraction accelerator inside the
  quantifier-instantiation loop. Contract at `qinst_egraph.rs:3547`: *"It can
  prove refutations early but never produces product SAT."*

### 1.2 Shipping sites already on the native core (5)

| # | site | enclosing fn | reached by |
|---|---|---|---|
| N1 | `euf_egraph.rs:1330` | `check_qf_uf_online_cdclt` (`:1248`) | `auto.rs:3985`, `euf_egraph.rs:912` |
| N2 | `lia_theory.rs:219` | `check_qf_lia_online_cdclt` (`:162`) | `dpll_lia.rs:568`, `:1453` |
| N3 | `lra_theory.rs:363` | `check_qf_lra_online_cdclt` (`:242`) | `dpll_t.rs:384` |
| N4 | `string_theory.rs:1069` | `check_qf_s_online_cdclt_with_memberships` (`:1040`) | `smtlib.rs:806`, `string_theory.rs:887` |
| N5 | `dl_online.rs:2279` | `try_check_qf_dl` (`:2189`) | `evidence.rs:2616` |

Each carries the same four-line comment above the call (`euf_egraph.rs:1322`,
`lia_theory.rs:212`, `lra_theory.rs:356`, `string_theory.rs:1063`,
`dl_online.rs:2271`): *"The NATIVE proof-producing core, not `CdclT` … S1b
ported all three into `CdclT` verbatim so this is a swap and not a
reconciliation."* ("All three" = watch scheme, order heap, clause minimizer.)

### 1.3 `CdclT` sites that are tests, not routes (32)

| site | test | what it pins |
|---|---|---|
| `lia_theory.rs:514` | `terminates_within_a_tight_step_budget` | `with_step_budget` + `step_budget_hit` |
| `lia_theory.rs:585` | `cdclt_driver_counts_forwarded_lia_propagation` | `theory_propagations` |
| `lra_theory.rs:850` | `terminates_within_a_tight_step_budget` | `with_step_budget` + `step_budget_hit` |
| `lra_theory.rs:923` | `cdclt_driver_counts_forwarded_lra_propagation` | `theory_propagations` |
| `string_theory.rs:1966` | `cdclt_driver_counts_string_theory_propagation` | `theory_propagations`, `value` |
| `ufbv_online.rs:3330` | `raw_solve_stats` helper (`:3292`) | driver stats for the UFBV suite |
| `cdclt.rs:2720 … :4173` (24) | the driver's own unit suite | every heuristic in §2 |
| **`native_cdclt/tests.rs:289`** | **`the_two_engines_and_a_brute_force_agree_on_random_instances` (`:312`)** | **the differential gate — see §4.5** |
| `benches/cdclt_propagate.rs:83` | `cdclt_propagate` bench | propagation throughput |

The five outside `cdclt.rs` sit in modules whose shipping route has **already**
moved — they test a driver their own module no longer uses. Two of them
(`lia_theory.rs:514`, `lra_theory.rs:850`) are the only callers of
`with_step_budget` / `step_budget_hit` anywhere; both are `#[cfg(test)]` on
`CdclT` itself (`cdclt.rs:923`, `:978`) and are **not compiled into production
at all**.

### 1.4 What distinguishes the two entry points, where a module has both

**In every module that has both, the `CdclT` entry point is a unit test and the
`solve_native` entry point is the shipping route.** No module has two shipping
entry points that differ in capability. For `lia_theory`, `lra_theory` and
`string_theory` the question dissolves: the distinction is test-vs-production,
and those modules need a test rewrite, not a migration decision.

The real split is between the four remaining sites, and it is **protocol shape,
not logic**. Methods called on the `CdclT` value:

| method | C1 `ufbv` | C2 `qinst` | C3/C4 `uf{lia,lra}` |
|---|:-:|:-:|:-:|
| `solve`, repeated/resumed | ✅ | ✅ | ✗ (once) |
| `with_inactive_variables` | ✅ | ✗ | ✗ |
| `activate_variables` | ✅ | ✗ | ✗ |
| `add_theory_variable` | ✅ | ✅ | ✗ |
| `add_permanent_clause` | ✅ | ✅ | ✗ |
| `theory_variable` | ✅ | ✅ | ✗ |
| **`backtrack_to_root`** | **✗** | **✅** | ✗ |
| `variable_count` / `clause_count` | ✅ | ✅ | ✗ |
| `value` | ✗ | ✅ | ✅ |
| `theory_propagations` | ✅ | ✗ | ✅ |

**The `backtrack_to_root` row is the load-bearing one, and it points the
opposite way to intuition.** C2 calls `backtrack_to_root` *first thing* in
`add_checked_batch` (`qinst_egraph.rs:3652`), then inserts clauses and atoms,
then resumes — i.e. it inserts **at level zero**. C1 never backtracks at all
(`grep 'backtrack' ufbv_online.rs` finds only prose and a test name); its
`add_permanent_clause` calls at `:1453`, `:2364`, `:2393` all happen after
`solve` returned `Sat`, so **with a full trail, at a non-root level**.

That matters because the native core's `add_input_clause` carries
`debug_assert!(self.trail.is_empty(), "add_input_clause between solves only")`
(`proof_sat.rs:2486`). **C2's protocol is already exactly the native
between-solves discipline; C1's violates its central precondition.** The two
"incremental" sites are not one migration.

---

## 2. Feature-parity matrix

Legend: ✅ present · ✗ absent · ⚠️ present but different.

### 2.1 Theory interface (ADR-1701)

| capability | `CdclT` | native core | verdict |
|---|---|---|---|
| `assert` | ✅ `cdclt.rs:1031/:1035` | ✅ `proof_sat.rs:4903` | parity |
| `push` / `pop` | ✅ `:2419` / `:1785` | ✅ `:4812` / `:4762` | parity |
| `propagate_into` | ✅ `:1358` | ✅ `:4919` | parity |
| **`final_check`** | ✅ `:2313`, via `run_final_check` `:2310` | ✅ `:3650`, `timed_final_check` | parity |
| **driver-owned queue** | ✅ `prop_queue` `:551`, `mem::take` `:1353` | ✅ `theory_queue` `:2246`, `mem::take` `:4934` | parity |
| **lazy explanation** | ✅ `deferred_reason` `:546`, `resolve_explanation` `:1283` | ✅ `Reason::theory` `:1850`, 62-bit packed handle, `resolve_reason` `:4188` | parity; native additionally rewrites the reason so a handle resolves **at most once per assignment** (`:8018`) |
| **dynamic atoms** | ✅ `register_new_atoms` `:1335` → `add_theory_variable` `:720` | ✅ `take_new_atoms` `:4966` → `register_theory_atoms` `:3804`, sets `branchable` | parity |
| `explain(handle, implied)` | ⚠️ `explain(handle)` only | ✅ takes `implied` | **native is ahead** — `CdclT`'s signature cannot express the core/reason distinction whose absence was a wrong-`unsat` shape (§4.1) |
| `engine_counters` | ✅ `:2244` | ✅ read adapter-side, `native_cdclt.rs:648` | parity |

**ADR-1701 parity is complete**, and on `explain` the native core is strictly
better specified.

### 2.2 Proof / DRAT emission (ADR-1704)

| capability | `CdclT` | native core |
|---|---|---|
| any proof output | **✗ — none** | ✅ |
| Boolean DRAT stream | ✗ | ✅ `proof_sat.rs:3542`, empty clause `:3177/:3192/:3488`, deletions `:4644` |
| enumerated theory-lemma stream | ✗ | ✅ `install_theory_lemma_clause:3738`, `install_theory_lemma:4114`; lemmas are **input** clauses (`:3751`, `:4151`) so `reduce_db` cannot delete them |
| checkable artifact | ✗ | ✅ `TheoryRefutation` `refutation.rs:58`, `check()` `:202` |
| recording opt-in | n/a | ✅ `record_proof` `:1236`; off by default |
| recording budget | n/a | ✅ `proof_literal_budget` `:1259`; on overflow drops the sink and reports the artifact **absent** `:1447` |

`CdclT`'s absence was established by grepping the whole file for
`drat|proof|refutation|certificat|lrat|clause_trace`: every hit is prose citing
`proof_sat.rs`, the descriptive word "refutation" for the `Unsat` verdict, or the
`farkas_certificates` **counter** copied from the theory (`cdclt.rs:2292`). There
is no sink field in the struct (`:376-560`) and no proof accessor.

**This is the whole reason the migration exists.** A `CdclT` refutation reaches
the front door as `Evidence::Unsat(None)` with `trusted_steps` empty.

### 2.3 Incrementality and assumptions — the gap that decides the plan

| capability | `CdclT` | native core |
|---|---|---|
| resumed `solve` retaining the learned DB | ✅ `solve_inner:2353` resets nothing; tests `:3325`, `:3370` | ⚠️ **`NullTheory` only** — `NativeIncrementalCdcl` `incremental.rs:124` |
| **a persistent solver with a theory attached** | ✅ | **✗ — type-level impossible** |
| dormant / inactive variables | ✅ `with_inactive_variables:705`, `activate_variables:752` | **✗ — no such concept** |
| `add_theory_variable` returning `(atom, var)`; `theory_variable(atom)` | ✅ `:720`, `:747` | ✗ — only the count-based `take_new_atoms` convention |
| add a permanent clause **mid-search** | ✅ `:781`, assignment-aware attach | **✗** — `add_input_clause` asserts an empty trail `:2486` |
| add a permanent clause **at root, between solves** | ✅ | ✅ `NativeIncrementalCdcl::add_clause` `incremental.rs:256` (calls `between_solves()` first) |
| `backtrack_to_root` as an addressable op | ✅ `:905` | ⚠️ exists as private `backtrack_to:4753` / `reset_search_state:2549`; public only as `between_solves` `incremental.rs:265` |
| SAT assumptions + failed-assumption core | **✗** (`grep assumption` → one English usage at `:2306`) | ✅ `Cdcl::run(assumptions,…)` `:3159`, `analyze_final:4222` — but **unreachable from the theory path**, which hard-codes `run(&[], …)` `:1557` |
| `step_budget_hit()` — an observable stop reason | ✅ `:978` (but `#[cfg(test)]`) | ✗ — folded into `Interrupted` |
| configurable step budget | ✅ `with_step_budget:923` (`#[cfg(test)]`) | ✗ — `THEORY_STEP_BUDGET` is a hard `const` `:78` |

**The decisive fact.** `NativeIncrementalCdcl` is declared
`cdcl: Cdcl<'static, IncrementalSink>` (`incremental.rs:125`) — `T` defaults to
`NullTheory` — and its seed constructor `Cdcl::new_empty` lives in
`impl<S: DratSink> Cdcl<'_, S, NullTheory>` (`proof_sat.rs:2290`). **There is no
public constructor that pairs a `NativeTheory` with a persistent `Cdcl`.**

So the one-shot restriction is **not** an adapter shortcut. It is a limitation of
the core, and the core says so: `proof_sat.rs:2572-2579` — *"a warm CDCL(T)
across solves needs a theory-side reset the trait does not have yet, and slice 2
proper has to decide whether that is a new trait method or a fresh theory
instance per solve."* `NativeTheory` (`theory.rs:137-199`) has no `reset`.

`native_cdclt.rs:12-22`'s framing ("deliberately only the one-shot half … porting
it is a separate slice") is accurate but understates it: the adapter *could not*
implement the incremental half today.

### 2.4 Search heuristics

| capability | `CdclT` | native core |
|---|---|---|
| watch scheme | 2WL + blocking lit, `Watch{clause,blocker}` `:247` | 2WL + blocking lit, 16-byte packed `WATCH_BYTES:1715`, binary-clause tag |
| VSIDS | ✅ decay `0.95`, rescale `1e-100`/`1e100` (`:282-287`) | ✅ **identical constants** `:83-88` |
| clause minimization | ✅ recursive `ccmin=2`, `minimize:1652` | ✅ recursive `ccmin=2`, `minimize:4296` |
| **clause-DB reduction** | ⚠️ LBD half-deletion, `REDUCE_FIRST 2_000` + `REDUCE_INCREMENT 300`, glue `≤2` protected (`:2191`) | ✅ **tiered** `clause_db_policy.rs:530`: `KeepRule::Tiers`, `GlueThenSize`, ramped 500–900‰, `ConflictInterval{1_000,1_000}`, `promote_on_use` |
| **phase policy** | ⚠️ last-polarity saving only, initialized **`true`**; no target, no rephase (`saved_phase` occurs at exactly `:471,656,742,1022,2424`) | ✅ `PhasePolicy` `phase_policy.rs`, `(Best,Inverted,Best,Original)` cycle, separate `best_trail_len`/`target_trail_len` |
| **restart policy** | ⚠️ Luby only, `LUBY_UNIT 100` (`:2027`); no EMA, no blocking, no mode switch | ✅ Luby **and** Glucose EMA (`:109-123`), blocking restarts, stable/focused mode switching (`consider_mode_switch:2644`, tick-denominated) |
| inprocessing | ✗ | ⚠️ `solve_with_drat_proof_inprocessed:867` — **`NullTheory` path only** |
| progress sink / tick counters | ✗ | ✅ `ProofSearchProgress:200`, `SearchCounters` |
| chronological backtracking, clause shrinking, VMTF | ✗ | ✗ (searched `shrink|chronolog|hyper|vmtf` — no hits either side) |

**On `set_policies` and the shipped default.** `Cdcl::set_policies`
(`proof_sat.rs:2609`) now has three callers — the one-shot SAT entry `:764`, the
CDCL(T) entry `:1549` (added by `4d2fdf068`, "the CDCL(T) driver could not select
a search policy at all"), and one test `:6033`. But the CDCL(T) path selects via
`SearchProfile`, whose `#[default]` is `Shipped` (`:1173`), and `solve_native`
reads `AXEYUM_SEARCH_PROFILE` per call (`native_cdclt.rs:689`). **So the shipped
CDCL(T) behaviour is still pinned phases + Luby restarts** — the tiered clause
DB is live, but mode switching and the phase schedule are opt-in experiment arms.
`SearchPolicies::ema_restart()` (`:665`) has no production caller at all and is
not even reachable from the theory path (`SearchProfile` has no `EmaRestart`
variant).

This is a real parity nuance for a plan: **the native core's heuristic advantage
over `CdclT` is mostly latent, not shipped.** What ships differently today is the
clause-DB tiering, the `initial_phase`/`target_rephase` pinning that
`solve_native` sets deliberately (`native_cdclt.rs:608-620`), and nothing else.

### 2.5 Deadline and conflict-budget plumbing

| capability | `CdclT` | native core |
|---|---|---|
| deadline checked at top of main loop | ✅ `:2380`, plus a second at `:2392` | ⚠️ `:3229`, **only inside `if T::HAS_THEORY`**, and on a 1,024-iteration cadence |
| deadline cadence inside BCP | ✅ every `DEADLINE_CHECK_LITERALS = 256` trail literals `:1150` | ✗ — only `handle_conflict:3513`, every `DEADLINE_CHECK_INTERVAL = 1_024` conflicts |
| eager check on an already-expired deadline | ✅ (top of loop) | ✗ in the core — **restored in the adapter** at `native_cdclt.rs:554` |
| step budget | `DEFAULT_STEP_BUDGET = 16_000_000` `:278`, overridable (`#[cfg(test)]`) | `THEORY_STEP_BUDGET = 16_000_000` `:78`, **same value**, not overridable |
| conflict cap | **✗ none** | ✅ `max_conflicts` param, `DEFAULT_PROOF_SAT_CONFLICT_LIMIT = 2_000_000` `:48` — but `solve_native` passes `usize::MAX` (`native_cdclt.rs:640`), deliberately, so no route changes verdict on it |
| stop reason observable | ✅ `step_budget_hit()` distinguishes budget from clock | ⚠️ `ResourceOut` vs `Interrupted` are distinct at the `axeyum-cnf` API, **but `Interrupted` is a union of six causes** and `solve_native:667` maps both to `Unknown` |

### 2.6 Layer stats and `--trace`

| capability | `CdclT` | native core |
|---|---|---|
| collection flag read | ⚠️ **once at construction** (`:497`, set `:678`) — enabling the guard after `CdclT::new` has no effect | ✅ per solve, `TheorySolveOptions.collect_layer_stats`; `solve_native` bridges via `cdclt::layer_stats_enabled()` |
| all 41 `TheoryLayerStats` fields | ✅ exhaustive literal `:2246-2299`, no `..Default` | ✅ via `theory_layer_stats` `native_cdclt.rs:698`; the 15 driver fields are a field-for-field port |
| the 7 `Duration` fields when collection is off | `Duration::ZERO` | same |
| engine-side (simplex/Farkas) fields | ✅ `engine.map(...)` → `None`, never `0` | ✅ same, adapter-side |
| **live cross-thread mirror** | ✅ direct `publish_live(THEORY_LAYER, …, InFlight)` every `LIVE_MIRROR_STEPS = 1_024` (`:2369`) | ✅ two mirrors — `NativeLayerStatsMirror` (`proof_sat.rs:1107`, flush every 1,024 theory steps) + `EngineCountersMirror` (`native_cdclt.rs:461`), recombined by `live_theory_layer_stats:490` |

Parity here is **achieved but fragile**, and it was achieved twice by repair
(§4.3, §4.4).

### 2.7 Model construction

| | `CdclT` | native core |
|---|---|---|
| `value(var)` for a never-decided var | `None` (`:988`) | `false` — `assign.unwrap_or(false)` `:3453`; `CnfAssignment` has no unassigned state |
| — reconciled? | — | ✅ `NativeModel::value` (`native_cdclt.rs:219`) re-derives `None` from an `occurring` bitmap so routes see `CdclT`'s contract |
| out-of-range var | **panics** (raw index) | `None` |
| model built by the driver | ✗ — theory left in the satisfying state, caller replays (`:204`, `:2217`) | same |
| `CnfAssignment` length after `register_theory_atoms` | n/a | **longer than `formula.variable_count()`** — `CnfAssignment::satisfies` against the original formula would return `AssignmentLengthMismatch`. Not reached today because routes read through `NativeModel::value`, but it is a live trap for anyone who reaches for the raw assignment. |

### 2.8 Unknowns

Marked honestly:

- **Whether the native core's heuristics are faster than `CdclT`'s on C1–C4's
  workloads: unknown.** No A/B was run by this lane and none is committed for
  these four routes. The only measured migration numbers I found are for QF_IDL
  (`9a6786e84`: 27/50 → 31/50, PAR-2 −12.9%, zero verdict changes).
- **Whether `proof_literal_budget` overflow and `record_proof: false` behave as
  documented: unknown — untested.** Searching `crates/` for `overflowed`,
  `proof_literal_budget` and `record_proof` finds no `axeyum-cnf` test that
  exercises overflow; the two `record_proof: false` uses (`proof_sat.rs:8659`,
  `:8724`) assert counters, not artifact absence. The solver-side
  `an_unrecorded_refutation_publishes_no_artifact`
  (`native_cdclt/tests.rs:458`) covers the `record_proof` half only.
- **Whether C1's dormant-variable use is essential or an optimization: unknown.**
  Establishing it needs a build, which this lane did not do.

---

## 3. What blocks each un-migrated site

### C3 / C4 — `uflia_online` and `uflra_online` (one-shot)

**Nothing structural. Two small things and one risk.**

1. **`theory_propagations` is not returned by `solve_native`.** Both sites do
   `*count = solver.theory_propagations()` (`uflra_online.rs:1357`,
   `uflia_online.rs:1822`) into an `Option<&mut usize>` that surfaces as the
   public `check_qf_uf{lra,lia}_boolean_prop_metrics`. The number exists on the
   native side as `NativeLayerStats.theory_propagations` (`proof_sat.rs:4955`)
   but is only published when `collect_layer_stats` is on, and `solve_native`
   returns no channel for it. Consumers: `tests/uflra_online.rs:917`,
   `tests/uflia_online.rs:1197`. **A few lines on `NativeSolveOutcome`.**
2. **Model shape.** Both read `solver.value(var)` for the atom literals *and*
   for `inject_skeleton_bool_symbols` (`uflra_online.rs:1387`).
   `NativeModel::value` already reproduces `CdclT::value`'s `None`-for-unoccurring
   contract, so this is covered — but only because someone did that work.
3. **The risk, and it is the one that has bitten before.** Both sites are
   **model-based consumers with a replay gate**: a leaf model that does not
   replay becomes `decline("combined CDCL(T) leaf did not rebuild a replaying
   model")` (`uflra_online.rs:1400`). A different-but-correct model is therefore
   a `Sat` → `Unknown` regression, which is exactly the class documented in
   §4.2. `solve_native` pins `initial_phase: true, target_rephase: false`, but
   the clause-DB tiering and reduction schedule still differ, so the decision
   sequence — and hence the model — can still differ.

**C3 and C4 must move together.** `auto.rs:4484` splits one dispatch arm between
them by sort. Moving one leaves QF_UFLIA and QF_UFLRA on different engines with
different give-up reasons, which is the failure mode `ea85c9813` already
recorded once (§4.2).

### C2 — `qinst_egraph` (incremental, root-only)

**Blocked by one named missing feature: a theory-carrying persistent `Cdcl`
(warm CDCL(T)).** Specifically:

- No public constructor pairs a `NativeTheory` with a persistent `Cdcl`
  (`incremental.rs:125` + `proof_sat.rs:2290`) — the blocker is type-level.
- `NativeTheory` has no reset hook (`theory.rs:137-199`), which
  `proof_sat.rs:2572-2579` names as the open design question.

**Everything else about C2 already fits.** Its `add_checked_batch`
(`qinst_egraph.rs:3651`) is literally `backtrack_to_root` → insert → `solve`,
which is `NativeIncrementalCdcl`'s `between_solves()` → `add_clause()` →
`solve()`. Its `add_theory_variable` use (`:3743`) is a bounded-growth atom
registration that `take_new_atoms` can express. It never adds a clause at a
non-root level.

C2 is also the site with the **most to gain**: it is a refutation-only
accelerator ("never produces product SAT", `:3547`), so every verdict it
produces is an `unsat` that currently reaches the front door with no trusted
step.

### C1 — `ufbv_online` (incremental, mid-search)

**Blocked by three missing features, one of which has no native counterpart at
all.**

1. Warm CDCL(T) — same blocker as C2.
2. **Mid-search clause insertion.** C1 adds permanent clauses at `:1453`,
   `:2364`, `:2393` with a full trail; the native precondition is an empty one
   (`proof_sat.rs:2486`). Either C1 must be restructured to backtrack first —
   changing its refinement loop, not just its engine — or the core must gain
   assignment-aware mid-search attachment, which `CdclT` has (`cdclt.rs:781`)
   and the native core does not.
3. **Dormant variables.** `with_inactive_variables` (`:705`) +
   `activate_variables` (`:752`) have **no equivalent anywhere in
   `axeyum-cnf`** — established by grepping the whole crate for
   `inactive|dormant|activate_variables`, zero hits. C1 uses them for reserved
   row variables (`inactive_reserved_row_variables:1292`).

C1 is a **redesign, not a swap.**

---

## 4. The behavioural deltas that bit people

These are the risk list. All are from committed comments, commit bodies and test
names — none was reproduced by this lane.

### 4.1 Two real defects, found by the differential, before any route moved (`24cb85901`)

- **A panic in `CdclT`.** `theory_propagate` wrote a lazily-propagated literal's
  handle *after* assigning it; `assign` tells the theory, which may answer with a
  conflict, leaving the literal on the trail at the current level with no reason
  and no handle — tripping 1-UIP's own assertion. Reachable by any theory that
  both defers explanations and refuses an assertion it caused; `euf_egraph` does.
  Fixed by recording the handle first (`cdclt.rs:1424`, comment `:1409-1423`).
  Pinned by `a_lazy_propagation_that_conflicts_on_its_own_assert_still_decides`
  (`cdclt.rs:4171`).
- **A wrong-`unsat` *shape* in `proof_sat.rs`.** `explain` answers for two
  different objects — a conflict core, and a propagation reason, which
  additionally contains the implied literal — and the propagate-onto-a-false-literal
  path asked for a CORE where the handle stood for a REASON. An adapter over an
  asserted-literal channel then installs `¬antecedents` as an ADR-1704 **input**
  clause that the theory does not entail. 39 engine disagreements, no wrong
  verdict, but a soundness shape. Fixed by giving `explain` the `implied`
  argument. Pinned by
  `a_propagation_onto_a_false_literal_asks_for_the_reason_not_a_core`
  (`proof_sat.rs:8869`) and `a_final_check_conflict_handle_is_asked_for_as_a_core`
  (`:8901`).

**Both were found by running the two engines against each other.** Neither was
found by inspection.

### 4.2 A different-but-correct model lost a verdict (`f429b3b8a`)

The native core decides a variable **false** first and rephases to the best
assignment on restart; `CdclT` decides **true** first and does no rephasing. Both
find correct models; they find *different* ones.
`auto::tests::mbqi_one_level_fixed_retry_is_guarded_and_replays_unfixed_seed_111_shape`
went `Sat` → `Unknown` on that alone, because MBQI picks its instantiation terms
out of the model it is handed. **Not a wrong answer — a decided query becoming
undecided.** Mitigated by pinning `initial_phase: true, target_rephase: false`
in `solve_native` (`native_cdclt.rs:621-622`), with the reasoning at `:606-612`:
*"moving a route onto this core is a swap of ENGINES and not also a swap of
decision heuristics."*

**Directly relevant to C3/C4**, which are model-based consumers behind a replay
gate.

### 4.3 The engine swap cost a give-up REASON (`ea85c9813`)

`CdclT::solve_inner` tests the deadline at the top of its main loop; the native
core checks less eagerly. Measured on `x > 0 & x < 1` at a zero budget: the core
propagated both units, ran a `final_check` the theory had no budget to answer,
returned `Sat`, and `lia_theory` reported `Unknown{kind: Incomplete}` where
`CdclT` reported `Unknown{kind: Timeout}`. **No verdict moved** — the replay gate
turned the vacuous `Sat` into `Unknown` — **but `dpll_lia::check_with_arith_dpll`
branches on that kind**, so which fallback ran had changed. Fixed by the eager
check at the adapter boundary (`native_cdclt.rs:554-566`). Pinned by
`an_exhausted_deadline_is_unknown_before_any_propagation`
(`native_cdclt/tests.rs:514`), which the commit notes is discriminating: the
fixture is Boolean-satisfiable and theory-refuted, so without the check the same
call returns `Unsat`.

### 4.4 The engine swap silently cost `--trace`, twice

- **First (`fdfd3a04d`).** `CdclT` reads `COLLECT_LAYER_STATS` at construction;
  the native core takes collection as a `TheorySolveOptions` field; nothing
  bridged them. Every migrated route stopped answering `--trace` — reporting no
  `TheoryLayerStats` at all. Caught by
  `lra_theory::tests::theory_layer_stats_are_populated_on_a_theory_conflict`
  **only on the full `--lib --features full` sweep**, not on any targeted run.
  The commit is explicit that this is *"precisely the reason `uflra_online` and
  `uflia_online` were left alone in this lane"* — i.e. **C3/C4 were deferred
  because of this, and the reason is now fixed.**
- **Second (`cb5cd9090`).** The lifting constructor left seven counters at
  `Default` with a comment claiming it "does not measure" them — but every one
  was already in the `engine` argument in hand. From `ea85c9813` onward `--trace`
  printed `final_check_core_widenings=n/a` on *every* QF_LRA file. `n/a` is
  honest, but that counter is the pre-registered decision input for whether the
  Farkas decline paths are the cheap large win, **and an absent number reads as a
  settled one to anyone who measured it on the old route.** Reasoning preserved
  at `native_cdclt.rs:726-741`.

**Pattern:** both were losses of *observability*, not verdicts, and both were
caught by a full sweep rather than a targeted run. A retirement plan should
require the full `--lib --features full` sweep per migrated route, not the
route's own suite.

### 4.5 The retirement's own trap: `CdclT` **is** the differential oracle

`native_cdclt/tests.rs:312`,
`the_two_engines_and_a_brute_force_agree_on_random_instances`: 4,000 random
CDCL(T) instances × both explanation channels = 8,000 runs, each decided by
`CdclT`, by `solve_native`, **and** by an independent brute force over the
Boolean skeleton and the theory's semantics — so "the engines agree" cannot mean
"both are wrong". It asserts zero disagreements and requires >100 sat and >100
unsat in the population, so it cannot pass vacuously.

Its own docstring: *"The gate. … A single disagreement is a hard failure: this is
the check that decides whether a shipping route may be moved."*

**Deleting `CdclT` deletes the gate that authorizes the migration.** ADR-1703's
precedent is exact and should be reused: BatSat was **demoted to a differential
oracle, not deleted.**

### 4.6 Not a blocker, despite appearances

`lib.rs:272` re-exports `CdclT`, `Lit`, `Outcome`. It is inside
`#[cfg(feature = "bench-internals")] #[doc(hidden)] pub mod bench_internals`
(`lib.rs:269-271`), a feature outside both `default` and `full`, documented at
`:264-268` as *"Not part of the public API: do not depend on this from production
code, only from a `[[bench]]` target."* Sole consumer:
`benches/cdclt_propagate.rs:31`. **One bench to port or drop, not an API break.**

---

## 5. The dependency order

### 5.1 What can move independently

```
  C3 uflia_online ─┐
                   ├── must move TOGETHER (one dispatch arm, auto.rs:4484
  C4 uflra_online ─┘    splits them by sort)
        │
        └── blocked by: theory_propagations plumbing (small)
            risk:       model-shape / replay-gate regression (§4.2)
            independent of everything below


  C2 qinst_egraph ──┐
                    ├── both blocked by ONE feature: warm CDCL(T)
  C1 ufbv_online  ──┘   (a theory-carrying persistent Cdcl +
        │               a NativeTheory reset hook)
        │
        └── C1 additionally blocked by TWO features with no native
            counterpart: mid-search clause insertion, dormant variables
```

**Order:**

1. **C3 + C4 first, as one change.** They are one-shot, they are the same
   function duplicated, and their only concrete blocker is a few lines of
   `theory_propagations` plumbing. The deferral reason recorded in `fdfd3a04d`
   (the `--trace` gap) **no longer applies** — it was fixed in that same commit.
   They gain proof output on the QF_UFLIA/QF_UFLRA combination arm.
2. **Warm CDCL(T) as a standalone slice**, gated on the design question the core
   already poses (`proof_sat.rs:2572-2579`): a new `NativeTheory` trait method,
   or a fresh theory instance per solve. Nothing migrates in this step.
3. **C2 next.** Its protocol is already the native between-solves discipline;
   once warm CDCL(T) exists, C2 is close to a swap. It has the highest evidence
   payoff per unit of work — refutation-only, so every verdict it produces
   currently lacks a trusted step.
4. **C1 last, or not at all.** Three missing features, one of which
   (dormant variables) does not exist in `axeyum-cnf` in any form, and one of
   which (mid-search insertion) contradicts a `debug_assert` the core relies on.

### 5.2 The single missing feature that unblocks the most sites

**Warm CDCL(T): a public constructor pairing a `NativeTheory` with a persistent
`Cdcl`, plus a theory-side reset hook on the `NativeTheory` trait.** It unblocks
C1 and C2 — 2 of the 4 remaining sites, and both of the hard ones.

But the honest framing is a two-part answer, because the other two sites are
unblocked by something far cheaper:

| feature | unblocks | size |
|---|---|---|
| return `theory_propagations` from `solve_native` | C3, C4 | a few lines |
| **warm CDCL(T)** | C2, and C1 partially | a real slice, with an open design question |
| mid-search clause insertion + dormant variables | C1 only | new core capability |

**A plan that leads with warm CDCL(T) has the order backwards.** Half the
remaining migration is cheap and is waiting on a stale deferral reason.

### 5.3 The exceptions — what should not move

**`CdclT` itself should not be deleted, even after all four routes migrate.** It
is the differential oracle for the native core (§4.5), and that oracle found both
defects of `24cb85901`, including a wrong-`unsat` shape. Deleting it would leave
the native CDCL(T) core with no independent cross-check at all — the native core
would be checked only against itself and against brute force on instances small
enough to enumerate. The right disposition is ADR-1703's own: **demote `CdclT` to
a test-only differential oracle**, `#[cfg(test)]` or feature-gated, its 30 unit
tests kept as the oracle's own correctness suite. That is a retirement from
*shipping paths*, which is what ADR-1703 actually did to BatSat.

**C1 (`ufbv_online`) is the site where "never move" is defensible on cost.** It
needs three absent features; its refinement loop is built around dormant reserved
row variables and mid-search insertion at a non-root level; and unlike C2 it is
not refutation-only, so the evidence payoff is smaller. If warm CDCL(T) lands and
C2 migrates cleanly, C1 should be re-argued on measured benefit rather than
assumed into the plan.

**A caution the plan should carry regardless.** Retiring `CdclT` leaves `Dpll`
with 7 shipping sites (§0.2), two of them (`uflra_online.rs:1500`,
`uflia_online.rs:1981`) inside the very modules C3/C4 live in. "One CDCL(T)
driver" is not the state this plan reaches.

---

## 6. Method, and what did not run

The counts in §0 were produced by classifying every `CdclT::new(` and
`solve_native` occurrence in `git ls-files crates/` by brace-depth tracking of
`#[cfg(test)] mod` regions, then hand-verifying the boundary cases.

- **Positive control, test side:** `string_theory.rs:1966` confirmed inside
  `#[cfg(test)] mod tests` opened at `:1887`, with a test-only
  `use crate::cdclt::{CdclT, Outcome};` at `:1890`.
- **Positive control, shipping side:** `qinst_egraph.rs:3628` confirmed shipping
  because the *first* `#[cfg(test)]` in that file is at `:6629`, ~3,000 lines
  below.
- **Constructor coverage:** `CdclT`'s only constructor is `pub fn new`
  (`cdclt.rs:574`); every other `Self`-returning item in `impl CdclT` (`:561`)
  is a `with_*` builder taking `self`. Verified by listing every `fn` in the
  block. So counting `CdclT::new` cannot miss a construction route.
- **Multi-line call sites** are counted: `ufbv_online.rs:1386` is a four-line
  call and was found, as were the wrapping `solve_native` calls.
- **A known limitation of the classifier, and it fired once.** It tracks
  `#[cfg(test)] mod`, **not `#[cfg(test)]` on a bare item.** It therefore
  reported `euf_egraph.rs:2695` as a shipping `Dpll::new` when the `Dpll` struct
  itself is `#[cfg(test)]` (`:2182`). All four shipping `CdclT` sites were
  re-checked by hand against this gap: `OnlineQuantifierClauseSession`
  (`qinst_egraph.rs:3524`), `solve_cdclt_round` (`ufbv_online.rs:1338`, carries
  only `#[allow(clippy::too_many_lines)]`) and both `cdclt_combined`
  (`uflia_online.rs:1747`, `uflra_online.rs:1294`) carry no `cfg`. §0.2's `Dpll`
  table is corrected for it.
- **A path-prefix false negative, caught.** An initial reachability grep for
  `uflra_online::` found no `auto.rs` caller and would have recorded C4 as
  unreachable from dispatch. It is reachable: `auto.rs:4486` calls it as
  `crate::check_qf_uflra_online`, through the `lib.rs` re-export. Every
  reachability claim in §1 was re-run against the bare function name with no path
  prefix.
- **`grep -c` control on ADR-1703:** the "never mentions `CdclT`" claim is
  backed by a positive control — the same grep finds `BatSat` 30 times in that
  file, and `cdcl` in five other casings.

**Did not run:** nothing was built, compiled or executed. No `cargo` invocation,
no test run, no benchmark, no profiling. Every claim is from source and commit
reading. In particular:

- The behavioural deltas in §4 are read from committed comments, commit bodies
  and test names — **none was reproduced.**
- No A/B of `CdclT` vs the native core on C1–C4's workloads was performed; §2.8
  records that as unknown.
- The claim that `proof_literal_budget` overflow is untested is from a source
  search, not from running a mutation on it.
