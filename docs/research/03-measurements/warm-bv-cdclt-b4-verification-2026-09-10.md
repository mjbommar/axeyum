# Phase B4 — verifying the three obstacles under the warm BV client

**Lane:** E7 (`E7-warm-bv-decision`), 2026-09-10.
**Phase:** B4 of
[the CDCL consolidation plan](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md),
under [ADR-1908](../09-decisions/adr-1908-the-native-core-is-the-one-cdclt-driver-cdclt-is-demoted-to-an-oracle.md),
which places this client "last **or not at all**".
**Decision recorded as:**
[ADR-1913](../09-decisions/adr-1913-the-warm-bv-clients-dormancy-blocker-is-refuted.md).

**Nothing is migrated here and no shipping code is changed.** This is the
verification the plan asks for before B4 is argued either way. Status words are
used strictly: **confirmed**, **refuted**, **could not establish**, **did not
run**.

---

## 0. The subject is not the file the phase names — and that changes the reading

B4's prose calls its subject "the warm BV client", and this lane's brief resolved
that to `crates/axeyum-solver/src/incremental.rs`, `IncrementalBvSolver`. That is
the wrong file.

```
$ grep -o 'CdclT' crates/axeyum-solver/src/incremental.rs | wc -l
0
$ grep -oi 'cdclt' crates/axeyum-solver/src/incremental.rs | wc -l
0
$ grep -o 'CdclT' crates/axeyum-solver/src/ufbv_online.rs | wc -l          # positive control
18
$ grep -o 'IncrementalCnf' crates/axeyum-solver/src/incremental.rs | wc -l # control: the file is read
9
```

`IncrementalBvSolver` (`incremental.rs:795`) is the warm **bit-blasting** BV
solver: its first two fields are `IncrementalLowering` and `IncrementalCnf`
(`incremental.rs:796-797`). It is already entirely on `axeyum-cnf`'s native stack
and has **nothing to migrate**. Its suite is
`crates/axeyum-solver/tests/incremental_bv.rs`, a different surface entirely.

The actual B4 subject is **`ufbv_online.rs`** — R-A's row **C1** — which ADR-1908
names correctly in its own decision text. Re-derived in this tree, because R-A's
`auto.rs` line numbers no longer hold on `main`:

| what | where |
|---|---|
| the one shipping `CdclT` construction | `ufbv_online.rs:1386`, inside `solve_cdclt_round` (`:1338`) |
| the one `#[cfg(test)]` construction | `ufbv_online.rs:3330` |
| public entry points | `check_qf_ufbv_online_cdclt` (`:931`), `check_qf_aufbv_online_cdclt` (`:963`) |
| dispatch | `auto.rs:4196` / `:4198`, routes `aufbv-online-cdclt` / `ufbv-online-cdclt` (named at `:4190` / `:4192`); second caller `auto.rs:5381` |

Two construction sites, one of them a route — matching R-A's table row
(`ufbv_online | 2 | 1 | 1 | 0`). The count was right; the file the phase pointed
at was not.

---

## 1. Obstacle 1 — "it never backtracks": **confirmed**

```
$ grep -o 'backtrack' crates/axeyum-solver/src/ufbv_online.rs | wc -l
8
$ grep -n 'backtrack_to_root' crates/axeyum-solver/src/qinst_egraph.rs   # positive control
3652:        self.solver.backtrack_to_root(&mut self.theory);
```

All eight occurrences in `ufbv_online.rs` are module prose (`:32`, `:34`, `:886`)
or test names and test-local variable names (`:3403`, `:3994`, `:3996`, `:3997`,
`:3998`). There is **no** `backtrack_to_root` call. The sibling client
`qinst_egraph` has exactly one, first thing, which is already the native
between-solves discipline.

## 2. Obstacle 2 — `add_permanent_clause` runs with a full trail: **confirmed**

Three shipping calls, all inside the refinement loop (`ufbv_online.rs:1400`) that
runs *after* `solve` has returned `Outcome::Sat`:

```
crates/axeyum-solver/src/ufbv_online.rs:1453   ROW axiom clauses
crates/axeyum-solver/src/ufbv_online.rs:2364   array ROW axiom
crates/axeyum-solver/src/ufbv_online.rs:2393   array-equality axiom
```

The trail is genuinely non-empty at those points, on three independent
authorities:

1. `CdclT::solve_inner` (`cdclt.rs:2361`) resets nothing on entry — it re-enters
   the search loop.
2. `add_permanent_clause`'s own doc (`cdclt.rs:774-777`): *"Unlike `Self::new`'s
   clauses, this one is registered **under a partial or total assignment** (the
   caller has just seen an `Outcome::Sat` it means to exclude), so its watches
   cannot simply be the first two literals"*.
3. There is no backtrack call anywhere that could make it empty (§1).

The native precondition is the opposite, also confirmed:

```
crates/axeyum-cnf/src/proof_sat.rs:2560   fn add_input_clause(&mut self, lits: &[CnfLit]) -> Option<CRef> {
crates/axeyum-cnf/src/proof_sat.rs:2561       debug_assert!(
crates/axeyum-cnf/src/proof_sat.rs:2562           self.trail.is_empty(),
crates/axeyum-cnf/src/proof_sat.rs:2563           "add_input_clause between solves only"
```

and `NativeIncrementalCdcl::add_clause` (`proof_sat/incremental.rs:478`) calls
`between_solves()` before it, deliberately.

### 2.1 New finding — the warmth this obstacle protects is only one round deep

`solve_cdclt_round` constructs a **fresh `CdclT`** at `:1386` on every call, and
it is called from a bare `loop {` in `build_and_solve_with_stats_impl`
(`ufbv_online.rs:1048`). So the route **already discards the entire search** —
learned clauses, VSIDS activities, saved phases, the lot — at every *outer*
refinement round; `stats.rounds` counts those rebuilds.

The mid-search insertion therefore buys warmth *within* one round only. The cost
of restructuring to backtrack-to-root-then-insert is bounded above by a loss the
route already absorbs routinely at a coarser grain. This is the fact that moves
B4 from "redesign" to "measure it".

## 3. Obstacle 3 — dormant variables "do not exist in `axeyum-cnf` in any form": **refuted**

R-A established this by grepping the crate for `inactive|dormant|activate_variables`
and finding zero hits. Re-run in this tree, the zero reproduces:

```
$ grep -rn 'inactive\|dormant\|activate_variables' crates/axeyum-cnf/src/ | wc -l
0
$ grep -rln 'fn ' crates/axeyum-cnf/src/ | wc -l        # control: the crate is greppable
34
```

The zero is real. The **conclusion drawn from it is not**: the concept is present
under a different name, `branchable`.

```
$ grep -ro 'branchable' crates/axeyum-cnf/src/ | wc -l
21
```

This is the repository's own standing hazard — *search for the STEP, not the
NAME* — landing on a migration blocker.

### 3.1 The correspondence, mechanism by mechanism

| mechanism | `CdclT` (`cdclt.rs`) | `axeyum-cnf` native core |
|---|---|---|
| the flag | `active: Vec<bool>` | `branchable: Vec<bool>` (`proof_sat.rs:2021`) |
| initial dormant set | caller computes it and passes `with_inactive_variables` (`:705`) | **derived by the constructor**: `vec![false; n]`, then `true` for every literal occurrence (`proof_sat.rs:2416-2418`) |
| seeding the order heap | all active, minus the passed set | only branchable (`proof_sat.rs:2511-2521`) |
| activate on clause insertion | `add_permanent_clause` → `activate_variables` (`:752`, called at `:780`) | inline in `add_input_clause` (`proof_sat.rs:2602-2609`) |
| append a dormant variable | `add_theory_variable` → `self.active.push(false)` (`:726`) | `ensure_vars` → `self.branchable.resize(count, false)` (`proof_sat.rs:2540`) |
| public dormant reservation | — | `NativeIncrementalCdcl::reserve` (`proof_sat/incremental.rs:470`), whose doc says *"Reserved-but-unused variables are not branchable: they never delay a decision and default to `false` in a returned model, exactly as in the one-shot core."* |
| decision filter | `pick_unassigned` skips inactive (`:1942`) | the heap holds only branchable, asserted both ways at `proof_sat.rs:6335-6341` |
| re-insert on backjump | gated on `active` (`:1780`) | gated on `branchable` (`proof_sat.rs:4893-4897`) |

And the decisive detail: `ufbv_online.rs:2973-2975` builds
`skeleton.active_variables` as

```rust
let mut active_variables = vec![false; encoder.var_count];
for literal in clauses.iter().flatten() {
    active_variables[literal.var] = true;
}
```

which is the **same computation, line for line**, as `proof_sat.rs:2416-2418`.
`inactive_reserved_row_variables` (`ufbv_online.rs:1292`) plus
`with_inactive_variables` is a hand-rolled re-implementation of something the
native constructor does for free. On this axis the native core is *more*
automatic than `CdclT`, not less.

### 3.2 Empirical anchor

`scripts/cargo-serialized.sh test -p axeyum-cnf --lib -- --test-threads=4`:

```
test result: ok. 634 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 52.88s
```

Named, each with a nonzero count confirmed rather than an exit status:

| filter | result |
|---|---|
| `unused_low_variables_do_not_delay_sparse_high_projection` | **1 passed** — 200,000 variables, `branchable.iter().filter(..).count() == 2`, heap `[199_998, 199_999]` (`proof_sat.rs:6348`) |
| `proof_sat::incremental::warm_theory` | **11 passed** — includes `a_warm_refutation_carries_a_checkable_two_stream_artifact` and `the_warm_path_records_no_proof_by_default` |
| `proof_sat::incremental::tests` | **10 passed** — includes `an_assumption_on_an_unconstrained_variable_is_satisfiable` |

### 3.3 Is the dormant-variable use *essential*? **No** — refuted on two independent grounds

**Ground A: the capability exists natively** (§3.1), so the question of building
it does not arise.

**Ground B: even the capability is not verdict-load-bearing here.** `active` is
read in exactly five places in `cdclt.rs` — `:1382`, `:1780`, `:1942`, and two
under `#[cfg(test)]` (`:1957`, `:1988`). Two of the three shipping reads are
order-heap bookkeeping. The one semantic read is `pick_unassigned` (`:1942`): a
dormant variable is never decided, so `Sat` is reached on an assignment that does
not mention it. That cannot change Boolean satisfaction, because the dormant set
is by construction "occurs in no clause" — `ufbv_online.rs:1303` filters on
`!active_variables[index]`, and `cdclt.rs:713` `debug_assert`s that no
constructor clause names an inactive variable. And the refinement scan never
reads the Boolean value at all: the round's `Sat` branch takes its model from
`theory.bv.candidate_assignment()` (`ufbv_online.rs:1416`), not from the trail.

**One asymmetry, stated precisely rather than waved past.** `CdclT` *also* drops
theory propagations naming an inactive variable:

```
crates/axeyum-solver/src/cdclt.rs:1382            if !self.active[var] {
crates/axeyum-solver/src/cdclt.rs:1383                continue;
```

The native core has **no** such guard: `theory_round_body`
(`proof_sat.rs:5052-5100`) enqueues every propagated literal whatever its
`branchable` state. Dropping a theory propagation is sound (propagation is an
accelerator; `final_check` carries the obligation), and so is applying one, so
this is a **search-trajectory difference, not a blocker** — but it is a real
behavioural delta of exactly the kind ADR-1908 says is caught only by the full
`--lib --features full` sweep, and it must not be discovered after the swap.

## 4. A fourth obstacle, which R-A folded into the third and which is separate

`ufbv_online.rs:872` calls `solver.add_theory_variable()` **during refinement**.
That is not dormancy; it is mid-search **variable-count growth** with a stable
`(variable, atom)` mapping. It deserves its own row, and its status is **present
with one behavioural difference**, not absent:

| | `CdclT` | native |
|---|---|---|
| grow | `add_theory_variable` (`cdclt.rs:718`) | `Cdcl::register_theory_atoms` (`proof_sat.rs:3921`), driven by `NativeTheory::take_new_atoms` |
| adapter mirror | none needed — the map lives in the core | `NativeTheoryAdapter::take_new_atoms` (`native_cdclt.rs:435-448`) |
| a new variable arrives | **dormant** (`self.active.push(false)`, `cdclt.rs:726`); the caller must `activate_variables` | **branchable immediately** (`proof_sat.rs:3923-3925`), with the doc's reason: *"without that a registered atom would never be decided and the search would report `sat` on an assignment that does not mention it"* |

So a migration gets a slightly larger decision space than it has today, not a
missing feature.

## 5. E3's desync question, answered for this client

E3 found `NativeTheoryAdapter` mirroring the core's variable count and desyncing
between solves, silently in release. **`ufbv_online` does not have that shape
today, and would acquire it on migration.**

- Today the map is the core's own: `add_theory_variable` *returns* the real
  `(variable, atom)`, and the client's alignment check is **release-active** —
  `ufbv_online.rs:873-878` returns
  `SolverError::Backend("online UFBV dynamic theory components lost atom-index alignment")`
  when `euf_atom != bv_atom || bv_atom != solver_atom`. Not a `debug_assert`.
- The adapter's equivalent is
  `debug_assert_eq!(self.atom_for_var.len(), var, "variable indices are dense")`
  (`native_cdclt.rs:445`) over a **mirrored** `next_var` field (`:262`), seeded
  once in `new` (`:300`).

`ufbv_online` is the only un-migrated route that *both* grows variables
mid-search *and* inserts clauses, so it is the route most exposed to that mirror
drifting. A migration must carry the release-active check forward rather than
inherit the `debug_assert`.

## 6. What is at stake

**The evidence gap is real and measured.**

```
$ grep -c 'Evidence\|trusted_step\|TrustedStep' crates/axeyum-solver/src/ufbv_online.rs
0
```

`auto.rs:4205-4211` returns a bare `Ok(Some(CheckResult::Unsat))`. Every
QF_UFBV / QF_AUFBV refutation from this route reaches the front door with no
trusted step — the same condition ADR-1908 gives as its reason for the whole
consolidation.

**But the gain is neither free nor automatic, and must not be overstated:**

- `NativeIncrementalCdcl::warm_theory` sets `record_proof: false`
  (`proof_sat/incremental.rs:276-281`), with the doc pricing the alternative as
  *"on a long CDCL(T) search the stream is gigabytes, and warm means many such
  searches accumulating into one sink."* The test
  `the_warm_path_records_no_proof_by_default` pins it. Migrating produces an
  artifact only if that knob is turned on, and the cost of turning it on for
  this route is **did not run**.
- The artifact is the ADR-1704 two-stream shape: a DRAT refutation of
  (skeleton ∧ installed theory lemmas). The BV and EUF lemmas are trusted by
  assertion — this route's BV conflicts are re-solved UNSAT conjunctions
  (`ufbv_online.rs:60-61`), not certificates. The gain is "a checkable Boolean
  refutation modulo named theory lemmas", not a full proof.

**Not at stake:** "one driver". ADR-1908 keeps `CdclT` in the tree as the
differential oracle regardless, so consolidation for its own sake is not a reason
here.

**Speed: did not run.** No A/B exists for this route. No corpus route census for
`ufbv-online-cdclt` exists in the tree either — three tracked files mention the
route name (`docs/solver-inventory-2026-09/03-dispatch-routing-and-backends.md`,
R-A's inventory, `adr-0071-replay-guided-array-interfaces.md`), and none counts
benchmarks through it.

## 7. Summary

| obstacle, as stated by R-A or the plan | status | where |
|---|---|---|
| the subject is `incremental.rs` / `IncrementalBvSolver` | **refuted** | 0 `CdclT` there vs 18 in `ufbv_online.rs` |
| 1. never backtracks | **confirmed** | `ufbv_online.rs`, 8 `backtrack` occurrences, all prose or tests |
| 2. `add_permanent_clause` with a full trail | **confirmed** | `:1453`, `:2364`, `:2393` vs `proof_sat.rs:2561` |
| 2a. …and the warmth it protects is one round deep | **new finding** | fresh `CdclT` at `:1386` under the outer `loop` at `:1048` |
| 3. dormant variables absent from `axeyum-cnf` | **refuted** | `branchable`, 21 occurrences |
| 3a. is the dormancy essential? | **refuted as a blocker** | present natively, and not verdict-load-bearing |
| 3b. theory-propagation skip on dormant vars | **confirmed as an asymmetry**, not a blocker | `cdclt.rs:1382` has it; `proof_sat.rs:5052-5100` does not |
| 4. mid-search variable growth, separate from 3 | **present**, one behavioural difference | `register_theory_atoms` vs `add_theory_variable` |
| relative engine performance on this workload | **did not run** | no A/B, no route census |
| cost of `record_proof: true` on this route | **did not run** | — |
