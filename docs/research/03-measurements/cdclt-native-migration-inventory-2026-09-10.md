# `CdclT` → native core: the site inventory and parity matrix

Measured 2026-09-10 against `f91570117` (local `main`, merged into this lane's
worktree). Lane `R-A-cdclt-inventory`. **Research only — no behaviour was
changed and nothing was migrated.**

Two CDCL(T) drivers coexist in `crates/axeyum-solver`:

- `crates/axeyum-solver/src/cdclt.rs` — `CdclT`, 4,176 lines. The older driver.
  Emits no proof.
- `crates/axeyum-solver/src/native_cdclt.rs` — `solve_native`, 764 lines. A thin
  adapter onto `axeyum-cnf`'s proof-producing core
  (`crates/axeyum-cnf/src/proof_sat.rs`, 8,945 lines).

[ADR-1703](../09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
made the native core the SAT engine and retired BatSat. It did not retire
`CdclT`. This document measures how far the CDCL(T) half of that migration got.

---

## 0. The headline correction

The count this lane was briefed with was produced by `grep -c` and is wrong in
the one direction that matters: **it counts `#[cfg(test)]` construction sites as
shipping routes.** The corrected count is below; the method is in §5.

| module | brief said `CdclT::new` | **shipping `CdclT::new`** | `#[cfg(test)]` `CdclT::new` | **shipping `solve_native`** |
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

Three consequences the brief's table hides:

1. **No module has both a shipping `CdclT` site and a shipping `solve_native`
   site.** The two sets are disjoint. The migration is not "half-done per
   module"; it is done or not-done per module, cleanly. Where a module appeared
   to have both, the `CdclT` half was always a unit test.
2. **The migration is 5 routes done, 4 routes remaining** — not the roughly
   even split the brief implies.
3. **`CdclT` is nonetheless pinned by 29 `#[cfg(test)]` construction sites**
   (24 in `cdclt.rs`, 5 in already-migrated modules) plus one bench. Retiring
   the type is a test-rewrite problem as much as a route-migration problem, and
   the test count is six times the route count.

The brief's table also omits every module that mentions `CdclT` without
constructing one: `combined_theory` (9 references), `combined_theory_lia` (8),
`layers` (7), `lib.rs` (4, including a **public re-export**), `lra_online` (3),
`dpll_t`, `smtlib`, `auto`. Those are doc comments and one public API surface,
not call sites — but the public re-export is a retirement obstacle in its own
right (§4.6).

---

## 1. Site-by-site inventory

### 1.1 Shipping sites still on `CdclT` (4)

| # | site | enclosing fn | reached by | protocol |
|---|---|---|---|---|
| C1 | `crates/axeyum-solver/src/ufbv_online.rs:1386` | `solve_cdclt_round` (`:1338`) | `check_qf_ufbv_online_cdclt` (`:931`) / `check_qf_aufbv_online_cdclt` (`:963`) ← `auto.rs:4144`, `auto.rs:4146`, `auto.rs:5329` | **incremental** |
| C2 | `crates/axeyum-solver/src/qinst_egraph.rs:3628` | `OnlineQuantifierClauseSession::new_with_limits` (`:3553`) | `OnlineQuantifierClauseSession::new` (`:3549`) ← `qinst_egraph.rs:2194` | **incremental, long-lived field** |
| C3 | `crates/axeyum-solver/src/uflia_online.rs:1819` | `cdclt_combined` (`:1747`) | `check_qf_uflia_online` (`:226`) ← `auto.rs:4488`, `abv.rs:2240` | one-shot |
| C4 | `crates/axeyum-solver/src/uflra_online.rs:1354` | `cdclt_combined` (`:1294`) | `check_qf_uflra_online` (`:143`) ← `auto.rs:4486` | one-shot |

Routing conditions, for the record:

- C1 is the QF_UFBV / QF_AUFBV arm; `auto.rs:4137` picks `aufbv-online-cdclt`
  when `features.has_array`, else `ufbv-online-cdclt`.
- C3/C4 are one dispatch arm split by sort: `auto.rs:4484` — "a real-sorted term
  anywhere routes to the `QF_UFLRA` decider, otherwise the integer one".
  **C3 and C4 are the same function, duplicated per sort** (both named
  `cdclt_combined`, both one-shot, both over a `CombinedIncremental*`).
- C2 is the ADR-0119 retained equality-abstraction accelerator inside the
  quantifier-instantiation loop. `qinst_egraph.rs:3547` states its contract:
  "It can prove refutations early but never produces product SAT."

### 1.2 Shipping sites already on the native core (5)

| # | site | enclosing fn | reached by |
|---|---|---|---|
| N1 | `crates/axeyum-solver/src/euf_egraph.rs:1330` | `check_qf_uf_online_cdclt` (`:1248`) | `auto.rs:3985`, `euf_egraph.rs:912` |
| N2 | `crates/axeyum-solver/src/lia_theory.rs:219` | `check_qf_lia_online_cdclt` (`:162`) | `dpll_lia.rs:568`, `dpll_lia.rs:1453` |
| N3 | `crates/axeyum-solver/src/lra_theory.rs:363` | `check_qf_lra_online_cdclt` (`:242`) | `dpll_t.rs:384` |
| N4 | `crates/axeyum-solver/src/string_theory.rs:1069` | `check_qf_s_online_cdclt_with_memberships` (`:1040`) | `smtlib.rs:806`, `string_theory.rs:887` |
| N5 | `crates/axeyum-solver/src/dl_online.rs:2279` | `try_check_qf_dl` (`:2189`) | `evidence.rs:2616` |

Each of N1–N5 carries the same four-line migration comment immediately above the
call (`euf_egraph.rs:1322`, `lia_theory.rs:212`, `lra_theory.rs:356`,
`string_theory.rs:1063`, `dl_online.rs:2271`): *"The NATIVE proof-producing core,
not `CdclT` … S1b ported all three into `CdclT` verbatim so this is a swap and
not a reconciliation."* The "all three" is the watch scheme, the order heap and
the clause minimizer.

### 1.3 `CdclT` sites that are tests, not routes (29 + 1 bench)

These are what "migration half-done per module" was actually measuring.

| site | test | what it pins |
|---|---|---|
| `lia_theory.rs:514` | `terminates_within_a_tight_step_budget` | `CdclT::with_step_budget` + `step_budget_hit` |
| `lia_theory.rs:585` | `cdclt_driver_counts_forwarded_lia_propagation` | `CdclT::theory_propagations` |
| `lra_theory.rs:850` | `terminates_within_a_tight_step_budget` | `CdclT::with_step_budget` + `step_budget_hit` |
| `lra_theory.rs:923` | `cdclt_driver_counts_forwarded_lra_propagation` | `CdclT::theory_propagations` |
| `string_theory.rs:1966` | `cdclt_driver_counts_string_theory_propagation` | `CdclT::theory_propagations`, `CdclT::value` |
| `ufbv_online.rs:3330` | `raw_solve_stats` (helper, `:3292`) | driver-level stats for the UFBV suite |
| `cdclt.rs:2720 … :4173` (24 sites) | the driver's own unit suite | every heuristic below |
| `benches/cdclt_propagate.rs:83` | `cdclt_propagate` bench | `CdclT::new` propagation throughput |

**The five tests outside `cdclt.rs` are the load-bearing ones**, because they sit
in modules whose shipping route has *already* moved. They test a driver their own
module no longer uses. Two of them (`lia_theory.rs:514`, `lra_theory.rs:850`) are
the only remaining callers of `CdclT::with_step_budget` / `step_budget_hit`
anywhere in the crate — verified by grepping both identifiers across
`crates/axeyum-solver/src/` and finding only these two pairs plus an unrelated
same-named pair on `lra_online.rs`'s `Dpll` type (`lra_online.rs:2802`, `:2810`).

### 1.4 What distinguishes the two entry points, where a module has both

The brief asked for this column as the most important one. The measured answer:

**In every module that has both, the `CdclT` entry point is a unit test and the
`solve_native` entry point is the shipping route.** There is no module where two
shipping entry points differ in capability. So for `lia_theory`, `lra_theory` and
`string_theory` the "two entry points" question dissolves — the distinction is
test-vs-production, not a capability split, and those modules need no migration
decision at all, only a test rewrite.

The real capability split is between the four remaining sites, and it is
**protocol shape, not logic**:

- **One-shot** (C3, C4): build a skeleton, construct, call `solve` once, read
  the model. This is exactly the shape `solve_native` already implements.
- **Incremental** (C1, C2): construct, then repeatedly `solve` while adding
  variables and clauses between rounds and retaining the learned database.
  `solve_native` does not implement this shape at all.

Measured protocol surface per site (methods called on the `CdclT` value):

| method | C1 `ufbv_online` | C2 `qinst_egraph` | C3/C4 `uf{lia,lra}_online` |
|---|:-:|:-:|:-:|
| `solve` (repeated, resumed) | ✅ | ✅ | ✗ (once) |
| `with_inactive_variables` | ✅ | ✗ | ✗ |
| `activate_variables` | ✅ | ✗ | ✗ |
| `add_theory_variable` | ✅ | ✅ | ✗ |
| `add_permanent_clause` | ✅ | ✅ | ✗ |
| `theory_variable` | ✅ | ✅ | ✗ |
| `backtrack_to_root` | ✗ | ✅ | ✗ |
| `variable_count` / `clause_count` | ✅ | ✅ | ✗ |
| `value` | ✗ | ✅ | ✅ |
| `theory_propagations` | ✅ | ✗ | ✅ |

**`native_cdclt.rs`'s own route table is stale.** Its module doc
(`native_cdclt.rs:15-18`) lists `ufbv_online` as the *sole* client of the
incremental protocol and puts `uflra_online`/`uflia_online` in the one-shot row.
The one-shot classification of C3/C4 is correct, but **`qinst_egraph` is absent
from the table entirely**, and it is a second incremental client — using
everything `ufbv_online` uses except `with_inactive_variables`/`activate_variables`,
*plus* `backtrack_to_root`, which `ufbv_online` does not use. The comment's
"exactly one client" is wrong: there are two, and between them they need a
strictly larger protocol than either alone.

---

## 2. Feature-parity matrix

*(§2, §3 and §4 are pending the two source surveys still in flight; this section
is filled in the second commit.)*

---

## 5. Method, and what did not run

The count in §0 was produced by classifying every `CdclT::new` and
`solve_native` occurrence in `git ls-files crates/` by brace-depth tracking of
`#[cfg(test)] mod` regions, then hand-verifying the boundary cases:

- **Positive control (test side):** `string_theory.rs:1966` was confirmed inside
  `#[cfg(test)] mod tests` opened at `string_theory.rs:1887`, with
  `use crate::cdclt::{CdclT, Outcome};` at `:1890` — a test-only import.
- **Positive control (shipping side):** `qinst_egraph.rs:3628` was confirmed
  shipping by checking that the *first* `#[cfg(test)]` in that file is at
  `:6629`, ~3,000 lines below the site.
- **Constructor coverage:** `CdclT`'s only constructor is `pub fn new`
  (`cdclt.rs:574`); the `impl CdclT` block at `:561` contains no other
  `Self`-returning associated function except the `with_*` builders, which take
  `self`. So counting `CdclT::new` cannot miss a construction route. Verified by
  listing every `fn` in the impl block.
- **Multi-line call sites** are counted correctly: `ufbv_online.rs:1386` is a
  four-line call and was found, as were the four `solve_native` sites whose
  arguments wrap.
- **Path-prefix trap, and it fired.** An initial reachability grep for
  `uflra_online::` found no `auto.rs` caller and would have recorded C4 as
  unreachable from dispatch. It is reachable — `auto.rs:4486` calls it as
  `crate::check_qf_uflra_online`, through the `lib.rs` re-export. Every
  reachability claim in §1 was re-run against the bare function name with no
  path prefix. This is the brief's "search for the string an author would write"
  hazard, and it produced a false negative on the first attempt.

**Did not run:** nothing was built or executed. Every claim here is from source
reading. No `cargo` invocation, no test run, no benchmark. In particular the
behavioural deltas in §4 are read from committed comments and test names, not
reproduced.
