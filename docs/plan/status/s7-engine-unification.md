# Lane: s7-engine-unification — the native core decides under a theory, and says what it assumed

<!-- plan-section: lane-status -->

**S7 is two slices, not one. S7a landed: the native core's three declined
theory paths (an `assert` conflict, a propagation onto a falsified literal, a
`final_check` conflict) and dynamic atom registration are implemented, a
CDCL(T) `unsat` produces the ADR-1704 two-stream artifact, and
`TrustId::SatRefutationModuloTheory` exists in code and grades it. S7b — moving
`CdclT`'s ten adapters onto that core — is a separate lane and is scoped below**
(`WIP`, s7-engine-unification, 2026-09-06).

## What landed (S7a)

Commits `9db9c98d8`, `0ccaac54b`, `f09dbba60`, `1666a0931`.

1. **Theory conflicts are learned, not declined.** A conflict from `assert`,
   from a propagation onto a literal the Boolean side has already falsified, or
   from `final_check` comes back as `TheoryRound::Conflict` carrying the
   conflict clause. `stage_theory_conflict` installs it as an ADR-1704 **input**
   clause (`learned[cid] == false`, so `reduce_db` can never delete it), orders
   the two highest-level literals into slots 0 and 1, and backjumps to the
   deepest level the core names before analysis — a complete check's core is not
   required to name a current-level literal, and without the backjump 1-UIP's
   path counter underflows.
2. **One learning path, not two.** The conflict half of `search_loop` is now
   `handle_conflict`, and a theory conflict is a clause id like any other by the
   time it reaches it.
3. **Dynamic atom registration** appends fresh SAT variables at the one point in
   the loop where the trail is at a propagation fixpoint, marks them branchable
   and heap-inserts them, so a registered atom is actually decided.
4. **The artifact.** `TheoryRefutation` carries `cnf`, the enumerated `lemmas`,
   the `extended` formula, and the Boolean stream.
   `theory_lemma_count()` is `|extended| - |cnf|`, computed on every call.
   `check()` composes the lemma-list contract with `check_drat` — **unchanged**,
   no theory arm, the trusted base does not grow by a line — and grades
   `Verified` only when there are no lemmas at all.
   `solve_with_theory_and_drat_proof` is the public entry point; the theory is
   borrowed through a new blanket `impl NativeTheory for &mut T`.
5. **`TrustId::SatRefutationModuloTheory`** and
   `theory_refutation_trust_step`, which is the single place ADR-1704's
   prohibition 2 is decided.

Two soundness details that are not obvious from the diff:

- Before the empty clause is emitted at level zero, every outstanding lazy
  theory reason on the trail is materialised into an installed input clause.
  `check_drat` replays unit propagation over `cnf ++ lemmas`, and a trail
  literal justified only by a handle the theory still holds is invisible to that
  replay. **This had no test that could fail until `1666a0931`**: every earlier
  fixture either propagated eagerly or had conflict analysis walk the reason. A
  level-zero refutation is the one shape where `analyze` never runs.
- An empty conflict core, and a core naming a literal that is not currently
  false, are both declined with the undecided outcome. Acting on the first would
  be a wrong `unsat` on the theory's say-so with no clause in the artifact
  behind it; `CdclT` declines the same case for the same reason.

`THEORY_STEP_BUDGET` (16M iterations, ported from `CdclT::DEFAULT_STEP_BUDGET`)
and an iteration-cadence deadline read bound a non-monotone theory that
propagates or registers atoms without ever conflicting. Both are behind
`HAS_THEORY`, so `NullTheory` drops them at monomorphization.

## The trusted-base count went 6 -> 7, on purpose

The trusted **code** did not grow: `check_drat` and `check_lrat` are untouched.
What grew is the number of holes with a name. Today a `CdclT` `unsat` reaches
the front door as `Evidence::Unsat(None)` with empty `trusted_steps`, so its
theory reasoning is trusted and *uncounted*. A seventh ledger row that says so
is a ledger that got more honest.

## Not measured, and why

**Neither scoring population can move under S7a and neither was measured.** No
solver route reaches the code this slice changed: every shipping entry point
constructs the search with `NullTheory`, and `crates/axeyum-solver/src/cdclt.rs`
is untouched. Reporting a population number here would be reporting host noise.
The population measurement belongs to S7b, which is the slice that changes what
the arithmetic routes run.

`TheoryLayerStats` is likewise **not** ported into the native core. Porting it
now would add counters nothing reads. It still reports, unchanged, from
`CdclT`; `lra_theory::tests::theory_layer_stats_are_populated_on_a_theory_conflict`
is its liveness check and is green.

## S7b, scoped

`CdclT` is not a Boolean search with a theory bolted on; it is a Boolean search
plus an **incremental refinement protocol** that ten adapters drive. The gap to
the native core is not the search — S1 and S1b already ported the watch scheme,
the order heap and the minimizer verbatim — it is this surface:

| `CdclT` surface | Native core today |
|---|---|
| `with_inactive_variables`, `activate_variables` | no notion of a dormant variable |
| `add_theory_variable` / `theory_variable` (explicit atom↔var map) | atoms **are** variable indices; no map |
| `add_permanent_clause` + resumed search retaining learned DB, phases, activities | `NativeIncrementalCdcl` exists but has a different shape |
| `backtrack_to_root`, `variable_count`, `clause_count`, `step_budget_hit`, `theory_propagations`, `value` | absent |
| `solve<T>(&mut self, theory: &mut T)` — theory passed per solve | `Cdcl` **owns** its `T` |

The last row is the structural one: `CdclT` keeps search state across solves
while the theory arrives per call, and `Cdcl` owns the theory for its lifetime.
The cheap resolution is to thread `theory: &mut T` through `run`/`search_loop`
rather than store it — `HAS_THEORY` still monomorphizes, and `CdclT::new`'s
signature and its ten call sites are then untouched, which is the property worth
protecting. Suggested order:

1. Port `TheoryLayerStats`'s driver-side counters (`boolean_propagate`,
   `conflict_analysis`, `decisions`, `restarts`) into the native core and show
   the same numbers on the same five traced files, before anything moves.
2. Thread the theory instead of owning it; blanket
   `impl NativeTheory for T where T: TheorySolver` on the solver side, with the
   literal-convention negation done once at the boundary (this module carries
   explanations as **clauses**, `euf_egraph` as asserted literals).
3. Dormant variables and the permanent-clause/resume protocol.
4. `CdclT` becomes the adapter; measure on
   `bench-results/adr-1701-slice-1-20260905/qf_idl_population.tsv` (50) and
   `qf_lra_population.tsv` (33), arms interleaved on an idle host, plus the full
   corpus sweep for verdict invariance.

<!-- plan-section: landed-changes -->
