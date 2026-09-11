# Warm CDCL(T) on the native core — what was built, what it costs, and three things a migration must not inherit

**Lane:** E3 (`E3-warm-cdclt`), 2026-09-10.
**Phase:** B2 of
[the CDCL consolidation plan](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md),
under [ADR-1908](../09-decisions/adr-1908-the-native-core-is-the-one-cdclt-driver-cdclt-is-demoted-to-an-oracle.md).
**Decision recorded as:**
[ADR-1909](../09-decisions/adr-1909-warm-cdclt-is-one-theory-push-pop-scope-per-solve.md).
**Commits:** `8b7c4ce3c` (the capability), `7ba794a93` (the option sweep and the
phase fix).

**No route is migrated here.** B3 (`qinst_egraph`) and B4 (the warm BV client)
are separate, and B4 is a redesign.

---

## 1. The gap was type-level, and R-A's reading of it was right

`NativeIncrementalCdcl` was `Cdcl<'static, IncrementalSink>` with `T` defaulting
to `NullTheory`, and the only persistent seed constructor lived in
`impl<S: DratSink> Cdcl<'_, S, NullTheory>`. Confirmed by reading. The generic
`Cdcl::new_with_theory(formula, sink, theory)` already existed — **only the
empty seed was bound to `NullTheory`** — so the mechanical part of B2 is three
lines and the design question above it is the work.

The core named the question itself, in `reset_search_state`:

> a *warm* CDCL(T) across solves needs a theory-side reset the trait does not
> have yet, and slice 2 proper has to decide whether that is a new trait method
> or a fresh theory instance per solve

## 2. The answer is neither of those: one `push`/`pop` scope per solve

A theory carries two kinds of state, and `push`/`pop` already separate them:

| state | must survive a solve boundary? | undone by `pop`? |
|---|---|---|
| registration (var-to-atom map, term database) | **yes** | **no** |
| assertions | **no** | **yes** |

So the reset is one `push` taken *below decision level zero* at the start of a
solve, and one extra `pop` in `reset_search_state` at the end. That extra level
is what reaches the level-zero assertions the per-decision-level pops cannot —
and those are exactly the ones the next solve re-derives when it re-propagates
`initial_units`.

Cost: the level-zero literals are re-asserted into the theory once per solve.
Same trade the Boolean warm path already makes for `initial_units`.

Behind `T::HAS_THEORY`, so the one-shot path and the `NullTheory` warm object do
not compile it. `NativeIncrementalCdcl` was **generalized** to
`NativeIncrementalCdcl<T: NativeTheory = NullTheory>` rather than duplicated, so
the ADR-1703 Boolean warm object is the `NullTheory` instantiation of the same
code. Full reasoning and the rejected alternatives are in ADR-1909.

## 3. Equivalence with the one-shot path, measured

`axeyum-cnf --lib warm_theory`: **11 tests**. Crate suite went **618 → 629**.

### 3.1 Single solve, fresh warm object vs `solve_with_theory_and_drat_proof_with_options`

Five queries × three option sets = **15 comparisons**, all agreeing on the
verdict **including the give-up reason**:

| query | shape |
|---|---|
| `{[1],[2],[3]}`, mutex {x1,x2} | theory-refuted, Boolean-satisfiable |
| `{[1],[2,3],[-2,-3]}` | satisfiable, theory prunes a branch |
| `{[1],[-1]}` | Boolean-refuted, theory silent |
| `{[1,2],[-1,3],[-3,4]}`, mutex out of range | satisfiable, theory never fires |
| `{[1],[2],[3]}` at **`max_conflicts = 0`** | `ResourceOut` on both — the give-up-reason arm |

Option sets: shipped defaults; the **`CdclT`-shaped** one a migrating route
actually asks for (`initial_phase: true`, `target_rephase: false`,
`ModeSwitching`); and `ScheduledPhase`.

### 3.2 Multi-solve, warm vs a fresh one-shot after every batch

Four clause batches over five variables, three option sets. After each batch the
warm object — running since batch one, with retained learned clauses,
activities and theory — is compared against a **fresh** one-shot over everything
accumulated. Verdicts agree at every batch under every option set. The sequence
is asserted to contain both a `Sat` and an `Unsat`, so it is not one answer
repeated.

## 4. The guard that dies

Whole-crate sweep (629 tests) per mutant, not the warm suite alone:

| mutation | tests killed |
|---|---:|
| delete the `theory_epoch` arm of `Cdcl::reset_search_state` | **2** |
| delete the `open_theory_epoch` call in `NativeIncrementalCdcl::solve` | **1** |
| delete the initial-phase fill in `NativeIncrementalCdcl::grow_to` | **1** |

Two of the three kill exactly one test. The first kills two, and they are the
two **distinct observable consequences** rather than one guard counted twice:

- `a_solve_boundary_must_not_re_assert_into_a_theory_that_never_forgot` fails
  with *"SECOND solve of an UNCHANGED satisfiable database returned Unsat"* — a
  **wrong verdict**, not a slowdown;
- `into_theory_returns_a_balanced_theory` fails with a theory push depth of 1
  where 0 is required.

The second mutation leaves the stack balanced (with no epoch opened there is
nothing extra to pop) and so kills only the verdict guard.

The fixture: database `{[x1], [x2,x3], [-x2,-x3]}`, theory at-most-one over
{x1,x2}, satisfiable, three solves running. Without the epoch the second solve
re-propagates `[x1]` into a theory still holding the first solve's `x1`.

**The test theory keeps its asserted atoms in a LIST, not a set, deliberately.**
`NativeTheory` promises the driver asserts a variable at most once per scope, so
a duplicate is a driver-side contract violation, and a list is what turns that
violation into an observable verdict instead of a silent no-op.

---

## 5. Three things a migration must NOT inherit

### 5.1 `initial_phase` reached no warm variable, and the sweep is what found it

The first version of the equivalence suite ran only the **shipped defaults**.
Under those, every line of `with_theory` that copies an option into the `Cdcl`
writes the value the constructor already installed — so the option plumbing was
measured by nothing, and deleting it would have changed nothing a test could
see. Adding the two non-default option sets found the bug on the first run:

```
satisfiable, theory never fires under CdclT-shaped:
  warm     Sat([false, true, false, false])
  one-shot Sat([true,  true, true,  true ])
```

Cause: the one-shot path fills `phase`, `best_phase` and `target_phase` in its
constructor, where they are already sized to the formula; a warm solver has no
variables at construction, so the same fill filled nothing. Every variable then
arrived through `ensure_vars`, which grows `target_phase` with `initial_phase`
but `phase` and `best_phase` with `false`.

Fixed by `NativeIncrementalCdcl::grow_to`. **The underlying `ensure_vars`
asymmetry is not repaired**, deliberately: it is reachable on the shipping
one-shot route (`native_cdclt.rs` sets `initial_phase: true`, and its theory
registers atoms mid-search through `Cdcl::register_theory_atoms`), so repairing
it would move the trajectory of the routes that migrated in `853063ebd`. It is
heuristic-only — a decision polarity, never a verdict. `grow_to` reproduces the
one-shot behaviour exactly, asymmetry included, because reproducing it is what
makes the two paths agree.

**The general shape, which is the reusable part:** an equivalence test that runs
only the default configuration measures the configuration plumbing at zero, and
looks exactly like an equivalence test that works.

### 5.2 A warm model is not the one-shot model, and cannot be

With the sweep extended to the multi-solve test, batch 1 under the
`CdclT`-shaped options gave:

```
warm     [F,F,T,F,F]
one-shot [F,T,T,T,T]
```

Both were checked against the clauses **and** the at-most-one constraint. Both
are valid.

This is not a defect and no constructor could arrange it away. A warm solver
enters its second solve holding the previous solve's **saved phases**; a fresh
one-shot starts from `initial_phase`. Phase retention is what warmth *is*.

It matters because it is exactly the hazard `TheorySolveOptions` already
records — a model-based consumer losing a verdict on a different-but-correct
model, measured once at
`auto::tests::mbqi_one_level_fixed_retry_is_guarded_and_replays_unfixed_seed_111_shape`.

**So B3 and B4 must re-measure their own model-based consumers and cannot
inherit any equivalence result from this slice.** The multi-solve test therefore
asserts the claim that holds — verdict equality with a fresh one-shot — and
replaces model equality with model **validity**, replayed against the clauses
and against the theory. (A checker that replayed only the clauses would accept
the one wrong answer a CDCL(T) engine can give: a model that satisfies the CNF
and violates the theory.)

### 5.3 `NativeTheoryAdapter` is not warm-ready — a mirrored counter

No trait change is needed, so **no `NativeTheory` implementor has to grow a
method**. That is a claim about the trait, and it is not the same as "every
implementor is warm-ready". The one shipping implementor is not.

`axeyum_solver::native_cdclt::NativeTheoryAdapter` keeps its own `next_var`,
seeded from a `var_count` fixed at construction, and grows it one per registered
atom in `take_new_atoms`, with the comment:

> The core appends `fresh` variables starting at its current variable count …
> Mirroring the counter here keeps the map aligned without the core having to
> report back.

That is exact **only while the core's variable count moves for no other
reason**. One-shot: it is `formula.variable_count()` at construction and
`register_theory_atoms` is the only thing that moves it. **Warm: false** —
`NativeIncrementalCdcl::add_clause` moves it between solves and the adapter is
never told. `next_var` goes stale and `atom_for_var` / `var_for_atom` misalign.

The adapter's own
`debug_assert_eq!(self.atom_for_var.len(), var, "variable indices are dense")`
is what would fire — so the failure is **loud in debug and silent in release**,
where atoms would map to the wrong SAT variables.

Established by reading the source. The core-side half is pinned by a test,
`atom_registration_survives_a_solve_boundary_and_appends_at_the_current_count`,
which asserts that `add_clause` grows the namespace with no theory involvement
and that the core appends registered atoms at its *current* count. **B3's first
obligation is to make the adapter read `NativeIncrementalCdcl::variable_count()`
rather than mirror its own counter.** Not changed here, because the adapter is
on the shipping one-shot route.

---

## 6. What the object does and does not offer

| | |
|---|---|
| `with_theory(theory, TheorySolveOptions)` | the general constructor; options applied identically to the one-shot path |
| `warm_theory(theory)` | the same with DRAT recording **off** — what a warm route wants (ADR-1703 point 1) |
| `solve(assumptions, deadline, max_conflicts)` | assumptions hold for one solve; deadline and conflict budget as on the one-shot path |
| `add_clause` between solves | closes the previous epoch, then registers into an unassigned solver |
| `theory()` / `theory_mut()` | readable after a solve **with that solve's assertions still in place**, which is what a model builder needs |
| `into_theory()` | closes the epoch first, so a borrowed theory comes back balanced |
| `theory_lemma_count()` | cumulative; available even with recording off |
| `theory_refutation()` | the ADR-1704 two-stream artifact; `None` means **not recorded**, never "no lemma was assumed" |
| `proof_literal_budget` | **not honoured** — the warm sink has no budget counter; recording is all-or-nothing. Recorded rather than fixed, because a budget that silently did nothing is worse than one documented absent |
| mid-search clause insertion | **absent** (B4) |
| dormant variables | **absent** (B4) |

## 7. Gates run, with exit codes

Exit codes read directly, never through a pipe. Everything heavy through
`scripts/cargo-serialized.sh`.

| gate | result | exit |
|---|---|---:|
| `test -p axeyum-cnf --lib` | **629 passed**, 0 failed (618 before) | 0 |
| `test -p axeyum-solver --lib --features full` | **1695 passed**, 0 failed | 0 |
| `test -p axeyum-solver --features full --test corpus_regression` | 2 passed, 0 failed | 0 |
| `clippy --workspace --all-targets -- -D warnings` | clean | 0 |
| `cargo fmt --all --check` | clean (read-only) | 0 |

The workspace clippy caught one real defect in this lane's own code that the
per-crate runs did not reach: `theory_refutation` carried an `expect` with no
`# Panics` section. It is documented rather than softened — a retained clause is
within `variable_count()` by construction, and if that stopped holding the
artifact would be naming a formula it does not have, which must fail loudly
rather than produce a refutation of the wrong CNF.

Not run, and therefore not claimed: `just check`, `./scripts/check.sh`, and the
`--features z3` differential fuzzes (this change touches neither linear
arithmetic nor the string routes).
