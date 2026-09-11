# ADR-1909: Warm CDCL(T) is one theory `push`/`pop` scope per solve — no new `NativeTheory` method, no fresh theory instance

Status: accepted
Index-summary: `axeyum-cnf`'s core posed its own open question in `Cdcl::reset_search_state` — a warm CDCL(T) "needs a theory-side reset the trait does not have yet, and slice 2 proper has to decide whether that is a new trait method or a fresh theory instance per solve" — and the absence blocked Phase B3 and B4 of the CDCL consolidation plan at the TYPE level: `NativeIncrementalCdcl` was `Cdcl<'static, IncrementalSink>` with `T` defaulting to `NullTheory`, and the only persistent seed constructor `Cdcl::new_empty` lived in an impl block bound to `NullTheory`. Decision: **neither of the two options the core named**. A theory carries two kinds of state — REGISTRATION (its var-to-atom map, its term database), which must survive a solve boundary or a warm object is pointless, and ASSERTIONS, which must not — and `push`/`pop` already separate exactly those two, since `pop` undoes assertions back to the matching `push` and unregisters nothing. So one scope opened around the whole solve, BELOW decision level zero, is the reset; that extra level is what reaches the level-zero assertions the per-decision-level pops cannot, which are precisely the ones the next solve re-derives when it re-propagates `initial_units`. Cost: one re-assertion of the level-zero literals per solve, the same trade `initial_units` already makes on the Boolean warm path. Rejected: a `NativeTheory::reset` method (a third lifecycle hook meaning what `push`/`pop` already mean, and every implementor must then get it right twice); a fresh theory instance per solve (destroys the registration, which is the half that must survive, and makes atom indices unstable across solves); and keeping the level-zero assertions (sound, since a monotone clause database keeps its level-zero entailments — but the driver then asserts the same literal twice into one scope, violating the trait's own contract, and a theory that keeps an assertion LIST rather than a set answers `Unsat` on a satisfiable database, measured). `NativeIncrementalCdcl` is GENERALIZED to `NativeIncrementalCdcl<T: NativeTheory = NullTheory>` rather than duplicated, so the ADR-1703 Boolean warm object is the `NullTheory` instantiation of the same code; the epoch is behind `T::HAS_THEORY`, so the one-shot path and the Boolean warm path do not compile it and their trajectories are unchanged. Two consequences a migration must not inherit: `initial_phase` reached no warm variable until `grow_to` was added (`ensure_vars` grows `target_phase` with `initial_phase` but `phase`/`best_phase` with `false`, a PRE-EXISTING asymmetry reachable on the shipping one-shot route and deliberately reproduced here rather than repaired), and a warm model is not the one-shot model and cannot be — a warm solve enters holding the previous solve's SAVED PHASES, so B3 and B4 must re-measure their own model-based consumers. Third: no trait change is needed, but `NativeTheoryAdapter` — the one shipping `NativeTheory` implementor — is NOT warm-ready, because it mirrors the core's variable counter in its own `next_var` and that mirroring is exact only while the count moves for no reason other than atom registration; `add_clause` moves it between solves with the adapter never told, so `atom_for_var`/`var_for_atom` misalign, loudly in debug (its own dense-indices `debug_assert`) and SILENTLY IN RELEASE. B3's first obligation is to make it read `variable_count()` instead of mirroring.
Index-status: accepted
Date: 2026-09-10

## Context

Phase B2 of
[`docs/solver-comparison-2026-09/12-cdcl-consolidation-plan.md`](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md),
under [ADR-1908](adr-1908-the-native-core-is-the-one-cdclt-driver-cdclt-is-demoted-to-an-oracle.md),
resting on
[the `CdclT` → native core site inventory](../03-measurements/cdclt-native-migration-inventory-2026-09-10.md)
(lane R-A). Measurements for this record are in
[the warm CDCL(T) note](../03-measurements/warm-cdclt-native-2026-09-10.md).

### The gap, and that it was a type-level one

`NativeIncrementalCdcl` was declared

```rust
cdcl: Cdcl<'static, IncrementalSink>,     // T defaults to NullTheory
```

and the core's only persistent seed constructor lived in

```rust
impl<S: DratSink> Cdcl<'_, S, NullTheory> {
    fn new_empty(sink: S) -> Self { ... }
}
```

So **no public constructor paired a theory with a `Cdcl` that outlived one
solve.** This is worth stating precisely because it changes what kind of work
B2 was: not "the adapter takes a shortcut", but "the core cannot express the
object". `native_cdclt.rs`'s own framing — that it implements "deliberately only
the one-shot half … porting it is a separate slice" — is accurate and
understates it.

The generic constructor `Cdcl::new_with_theory(formula, sink, theory)` already
existed. Only the *empty* seed was bound to `NullTheory`, which is why the fix
at the `Cdcl` level is three lines and the design question above it is the whole
of the work.

### The question the core asked itself

`Cdcl::reset_search_state` unwinds a finished search. It pops the theory once
per decision level the search pushed, and then said:

> Level-zero assertions made before the first `push` are NOT undone — the theory
> has no backtrack point below level zero, exactly as `TheorySolver` defines it.
> That is the right shape for a one-shot solve; a *warm* CDCL(T) across solves
> needs a theory-side reset the trait does not have yet, and slice 2 proper has
> to decide whether that is a new trait method or a fresh theory instance per
> solve.

`NativeTheory` has no `reset`. The two options named are the two this record
rejects.

### Why the level-zero assertions are the whole problem

They are not an edge case; they are the common case. `reset_search_state`
promotes every level-zero trail literal into `Cdcl::initial_units` so the next
solve re-derives it by propagation rather than by search. That is deliberate and
it is what makes `add_clause` simple. But it means **the next solve asserts those
same literals into the theory again** — and without a scope below level zero the
theory never forgot them.

## Decision

### 1. One theory `push`/`pop` scope per solve, opened below decision level zero

`Cdcl` gains a `theory_epoch` flag and `Cdcl::open_theory_epoch`, which takes
one `NativeTheory::push` before the search begins.
`Cdcl::reset_search_state` closes it with one extra `pop`, after the
per-decision-level pops and **before** the trail is cleared — a theory that walks
the driver's trail during `pop` must still see the assignments it is undoing,
which is an invariant `backtrack_to` already documents and relies on.

The reasoning is that a theory carries two kinds of state and the trait already
separates them:

| state | example | must survive a solve boundary? | undone by `pop`? |
|---|---|---|---|
| **registration** | the var-to-atom map, the term database, `take_new_atoms` bookkeeping | **yes** — otherwise a warm object is pointless and atom indices are unstable | **no** |
| **assertions** | what is currently asserted true or false | **no** | **yes** |

`pop` means "undo every assertion back to the most recent `push`" and
unregisters nothing. That is exactly the split a solve boundary needs, so the
boundary needs no new vocabulary — only one more level of the vocabulary that
exists.

The invariant `backtrack_to`'s pop count relies on is preserved: the epoch sits
*below* `trail_lim[0]`, so `backtrack_to(level)` — which pops
`trail_lim.len() - level` times — never touches it.

**Cost.** The level-zero literals are re-asserted into the theory once per
solve. This is the same trade the Boolean warm path already accepts for
`initial_units` ("one level-zero propagation per solve, and it buys the property
that makes `add_clause` simple"), and it buys the same kind of property here: a
solve always begins against a theory in a known state, with no
assignment-aware special case anywhere.

**Scope.** `open_theory_epoch` is called by the warm entry point and nowhere
else, and its body is behind `T::HAS_THEORY`. So the one-shot CDCL(T) path takes
no epoch and its theory push/pop counts are unchanged, and the `NullTheory`
warm object does not compile the code at all.

### 2. `NativeIncrementalCdcl` is generalized, not duplicated

`NativeIncrementalCdcl<T: NativeTheory = NullTheory>`. The default type
parameter means `NativeIncrementalCdcl` still names what it named — no caller
changed, `IncrementalSat` still holds it by value — while the warm CDCL(T)
object is the same code at a different `T`.

This is a deliberate choice against a second type. The whole of
[the consolidation plan](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md)
exists because duplicated Boolean search machinery diverged, and a
`NativeIncrementalCdclT` beside `NativeIncrementalCdcl` would be the same
mistake at a smaller scale. It also buys an argument that a duplicate could not:
the `NullTheory` instantiation of this code is the object ADR-1703 already
shipped and already tested, so the warm CDCL(T) path inherits that assurance
instead of restating it.

### 3. DRAT recording is OFF on the warm path by default

`NativeIncrementalCdcl::warm_theory(theory)` is `with_theory` with
`record_proof: false`. `TheorySolveOptions::default()` has it **on**, which is
right for a one-shot evidence-producing call and wrong here: ADR-1703 point 1
made exactly this call for the `NullTheory` warm object, and the reason is
stronger for a theory, not weaker. The stream is every learned clause of the
search held in memory, `TheorySolveOptions::record_proof`'s own doc prices a
single long CDCL(T) search at gigabytes, and *warm* means many such searches
accumulating into one sink.

With recording on, `NativeIncrementalCdcl::theory_refutation()` returns the
ADR-1704 two-stream artifact. `None` there means **not recorded** and never "no
theory lemma was assumed" — that is `Some(artifact)` with
`theory_lemma_count() == 0`. The lemma COUNT stays available with recording off,
so the distinction survives even when the artifact does not.

### 4. `proof_literal_budget` is not honoured on the warm path, and says so

The warm sink carries no budget counter. Recording here is all-or-nothing. A
caller needing a bounded stream keeps recording off and re-runs the decided
query through the one-shot path, which does honour it. This is recorded rather
than fixed because a budget that silently did nothing is worse than one that is
documented absent.

## Alternatives rejected

**A `NativeTheory::reset` trait method** — the first option the core named. It
adds a third lifecycle hook whose meaning is "`pop` everything", i.e. what
`push`/`pop` already mean, so every implementor now has two ways to say the same
thing and must get both right. Worse, `reset` has no natural definition for a
theory reached through `&mut T`: the blanket `impl NativeTheory for &mut T`
would forward it, so a borrowed theory could be reset out from under its owner.
The `push`/`pop` framing has neither problem and needs no trait change at all,
so **no `NativeTheory` implementor has to grow a method**. That is a claim about
the trait and is not the same as "every implementor is warm-ready" — see
consequence (c).

**A fresh theory instance per solve** — the second option the core named. It
destroys the registration, which is the half of the state that must survive:
atom indices would be re-issued per solve while the Boolean variable namespace
persisted, so the two would drift apart. It also forfeits the point of warmth on
the theory side (a rebuilt congruence closure or simplex tableau per solve), and
it requires `T: Default` or a factory, neither of which the trait has.

**Keep the level-zero assertions** — tempting, because it is *sound*: a
level-zero literal is entailed by the clause database alone, the warm database
only grows, so the entailment persists. But the driver then asserts the same
variable twice inside one scope, which the trait's own convention forbids
(`assert` is called once per variable per scope; `theory_qhead` guarantees it
within a solve and only the boundary breaks it). Whether that is harmless
depends entirely on the theory: idempotent for a union-find merge, **not**
idempotent for any theory that keeps an assertion list, a trail for
explanations, or a counter. Measured against a theory that keeps a list, the
second solve of an unchanged, satisfiable database returns `Unsat`. A
correctness property that holds only for some implementors of a public trait is
not a property.

**Leave `ensure_vars`'s `initial_phase` asymmetry repaired in this change** —
see below. Rejected as out of scope, not as wrong.

## Consequences

### Two findings a migration must NOT inherit

**(a) `initial_phase` reached no warm variable, and the underlying asymmetry is
live on the shipping one-shot route.** `Cdcl::ensure_vars` grows `target_phase`
with `initial_phase` but `phase` and `best_phase` with `false`. The one-shot path
hides this for the formula's own variables because its constructor fills all
three; a warm solver has no variables at construction, so the same fill filled
nothing. `NativeIncrementalCdcl::grow_to` now gives every newly created variable
the phase the one-shot constructor would have given it.

The asymmetry itself is **not** repaired here. It is reachable on the shipping
one-shot route — `native_cdclt.rs` sets `initial_phase: true` and its theory
registers atoms mid-search through `Cdcl::register_theory_atoms` — so repairing
it would move the trajectory of the routes that migrated in `853063ebd`. It is
heuristic-only (a decision polarity, never a verdict). `grow_to` therefore
*reproduces* the one-shot behaviour exactly, including the asymmetry, because
reproducing it is what makes the two paths agree. Repairing it is a separate
change with its own measurement.

**(b) A warm model is not the one-shot model, and cannot be.** A warm solve
enters holding the previous solve's saved phases; a fresh one-shot starts from
`initial_phase`. Phase retention is what warmth *is*. Measured: under the
`CdclT`-shaped options, warm `[F,F,T,F,F]` against one-shot `[F,T,T,T,T]`, both
valid against the clauses and the theory.

This is the hazard `TheorySolveOptions` already records — a model-based consumer
losing a verdict on a different-but-correct model, measured once at
`auto::tests::mbqi_one_level_fixed_retry_is_guarded_and_replays_unfixed_seed_111_shape`.
**B3 and B4 must re-measure their own consumers on the model and cannot inherit
any equivalence result from this slice.** Verdict equivalence with a fresh
one-shot is established here; model equivalence across a warm boundary is not
available to be established, because it is false.

**(c) `NativeTheoryAdapter` is not warm-ready, and the reason is a mirrored
counter.** No trait change is needed, but the one shipping `NativeTheory`
implementor still needs work before B3 can use this object, and it is better to
name it now than to discover it inside the migration.

`axeyum_solver::native_cdclt::NativeTheoryAdapter` maintains its own `next_var`,
seeded from a `var_count` fixed at construction, and grows it one per registered
atom in `take_new_atoms`, with the comment *"The core appends `fresh` variables
starting at its current variable count … Mirroring the counter here keeps the
map aligned without the core having to report back."*

That mirroring is exact **only while the core's variable count moves for no
other reason**. On the one-shot path that holds: the count is
`formula.variable_count()` at construction and `Cdcl::register_theory_atoms` is
the only thing that moves it afterwards. On a warm path it is false —
`NativeIncrementalCdcl::add_clause` moves it between solves and the adapter is
never told — so `next_var` goes stale and `atom_for_var` / `var_for_atom`
misalign. The adapter's own
`debug_assert_eq!(self.atom_for_var.len(), var, "variable indices are dense")`
is what would fire, which means the failure is loud in debug and **silent in
release**, where atoms would map to the wrong SAT variables.

Established by reading the source, and the core-side half of it is pinned by a
test:
`atom_registration_survives_a_solve_boundary_and_appends_at_the_current_count`
asserts that `add_clause` grows the namespace with no theory involvement and
that the core appends registered atoms at its *current* count. So B3's first
obligation is to make the adapter read the core's count —
`NativeIncrementalCdcl::variable_count()` is the observable — rather than mirror
its own. This slice does not change the adapter, because the adapter is on the
shipping one-shot route and changing it there is a behaviour change this lane
was explicitly scoped out of.

### What B3 gets

`qinst_egraph`'s `add_checked_batch` is `backtrack_to_root` → insert → `solve`,
which is `between_solves()` → `add_clause()` → `solve()`. That mapping was the
inventory's reason for calling B3 "close to a swap once B2 exists", and B2 now
exists. It is refutation-only, so the artifact route (decision 3) is the part it
will actually exercise. Its model-based consumers — if any — fall under
consequence (b).

### What B4 does not get

`ufbv_online` still needs mid-search clause insertion (which contradicts
`add_input_clause`'s empty-trail `debug_assert`) and dormant variables (which do
not exist in `axeyum-cnf` in any form). Neither is delivered here. ADR-1908's
"last, **or not at all**, re-argued on measured benefit" is unchanged by this
record.

### No route migrates

This slice delivers the capability and its tests only. A migration on top of an
unproven constructor is how an engine swap becomes a silent behaviour change,
which this repository has measured four times (`ea85c9813`, `f429b3b8a`,
`fdfd3a04d`, `cb5cd9090`).
