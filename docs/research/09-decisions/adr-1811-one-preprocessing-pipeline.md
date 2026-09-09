# ADR-1811: One word-level preprocessing pipeline — `preprocess.rs` is the home, and the witness asymmetry runs the other way

Status: proposed
Date: 2026-09-09
Index-summary: Closes roadmap item 1.4. Two word-level preprocessing pipelines run the same five reductions: `preprocess.rs` (`check_with_preprocessing`, up to 8 rounds, `MAX_PREPROCESS_ROUNDS` at `:32`) and `auto::preprocess_reduce` (`auto.rs:2158`, one straight-line round, the front door). **The inventory's crux claim is false.** It says the front door does not carry the `real_div_zeros` model witness whose loss `preprocess.rs:221-224` calls "a wrong `sat` through the preprocessed path"; `auto.rs:2339-2346` carries it, added in the same commit `124e18aa0` (2026-07-02) with the same comment. The asymmetry runs the OTHER way: `auto.rs` carries symbols + function interpretations + `/0` and is a strict superset of `preprocess.rs`, which carries symbols + `/0` and drops function interpretations at `:215-227`. Whether that drop is reachable is genuinely open and needs a run, not a read — its one non-test caller is the QF_ABV scalar-abstraction probe (`abv.rs:3242`), and `abv::complete_assignment` (`:3444`) refills a MISSING interpretation with a default rather than raising `UnboundFunction`, so the failure would be quiet. Decision: `preprocess.rs` is the surviving home for the reduction and the replay, parameterized over the solve call; `auto::preprocess_reduce` and `dispatch_reduced`'s model-building block are deleted. Warning attached: `reduction_shrinks_encoding`'s measured AIG-inflation numbers were taken against a ONE-round reduction and do not transfer to the fixpoint.
Index-status: proposed

## Context

Roadmap item 1.4
([`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md))
says the two word-level preprocessing pipelines should merge into one that
"carries both witness kinds and loops to fixpoint under the existing cap." The
inventory
([`docs/solver-inventory-2026-09/00-README.md`](../../solver-inventory-2026-09/00-README.md)
§1) states the crux as:

> Neither preprocessing pipeline is a superset of the other. `preprocess.rs:221-224`
> states that dropping the `real_div_zeros` witness "would hand the caller a model
> that no longer replays — a wrong `sat` through the preprocessed path"; the front
> door's path does not carry it. **This is a divergence needing an owner, not a
> demonstrated bug** — whether `auto.rs`'s path can ever see a real `/0` witness
> was not determined here, and settling it needs a run, not a read.

The last sentence is right about method and wrong about which question is open.
Read in source on 2026-09-09 at `ea8515407`:

### The `/0` question is settled by reading, and the inventory has it backwards

`auto::dispatch_reduced` carries the witness, with the same reasoning in the same
words:

```
crates/axeyum-solver/src/auto.rs:2339-2346
    // Same for the free-division `/0` witness (P2.5): the replay above succeeded
    // *under* this interpretation (the evaluator consults it on a zero divisor),
    // so dropping it would hand back a model that no longer replays — a wrong
    // `sat` through the preprocessed path.
    for (numerator, quotient) in reconstructed.real_div_zeros() {
        out.set_real_div_zero(numerator, quotient);
    }
```

`git blame` puts lines 2340-2346 at commit `124e18aa0`, 2026-07-02, *"feat(nra):
first-class /0 division witnesses — forced-div-by-zero promotes unknown→sat"* —
the same commit that put the paired lines in `preprocess.rs:221-227`. So the
hazard `preprocess.rs:221-224` names has not applied to the front door for two
months. No run is needed; the inventory was reading one of the two sites.

### The real asymmetry, which points at the pipeline the inventory called safer

Model witnesses actually carried, per pipeline:

| witness kind | `auto::dispatch_reduced` | `preprocess::replay_preprocessed_model` |
|---|---|---|
| symbol values | `:2324-2330` | `:215-220` |
| uninterpreted-function interpretations | `:2331-2338` | **absent** |
| free-division `/0` (`real_div_zeros`) | `:2339-2346` | `:221-227` |

`auto.rs` is a strict superset. `preprocess.rs` drops function interpretations,
and `auto.rs:2331-2337` states exactly why that matters:

> an inner QF_UFLIA/QF_UFLRA `sat` reconstructs an `Op::Apply` interpretation,
> and dropping it would leave the returned model unable to replay a UF query (the
> original assertions reference `f` — `eval` would raise `UnboundFunction`).

`preprocess.rs`'s *own* replay (`:191-213`) is safe, because it evaluates under
`reconstructed`, which does hold the interpretation. The loss is in the `Model`
it hands back at `:215-227`, i.e. to its caller.

### Whether that drop can fire is open, and the failure mode would be quiet

`check_with_preprocessing` is public API (exported through `full_exports!`,
`lib.rs:1268`), so an external caller can hit it directly. Its one non-test caller
in tree is `abv::check_scalar_abstraction` (`abv.rs:3232`), which calls
`check_with_preprocessing_and_local_search` at `:3242` on the QF_ABV
scalar-abstraction path and then, by its own doc (`:3229-3231`), subjects the
result to "the normal ROW/extensionality projection and original-formula replay."

That downstream replay is the gate, and it is not obviously a loud one.
`abv::complete_assignment` (`:3444-3460`) fills in any function the assignment
does not bind:

```
    for (func, _name, params, result) in arena.functions() {
        if out.function(func).is_none()
            && let Some(value) = default_func_value(arena, params, result)
        {
            out.set_function(func, value);
        }
    }
```

So a genuine interpretation dropped at `preprocess.rs:215` does not surface as
`UnboundFunction`; it is silently replaced by a **default**, and whatever the
array replay then concludes it concludes under the wrong function. Whether the
final original-formula replay catches that, and whether an AUFBV query with a
non-degenerate uninterpreted function actually reaches `:3242` in the shipping
dispatch, are two questions this ADR does **not** settle. They need a run. The
experiment is named under *Migration*.

**This is stated as an exposure, not a bug.** No wrong `sat` is demonstrated
here, and none should be claimed from this document.

### What else differs

| | `preprocess.rs` | `auto.rs` |
|---|---|---|
| rounds | up to 8, stops at a fixpoint (`:32`, `:89-136`) | exactly 1 (`:2166-2198`) |
| deadline polling between passes | none | six `past_deadline` checks (`:2163`, `:2169`, `:2175`, `:2181`, `:2187`, `:2193`) |
| encoding-size guard before using the reduction | none | `reduction_shrinks_encoding` (`:2233`), called at `:1768` |
| replay diagnostics | three distinct failures — evaluated false / non-Boolean / eval error (`:194-212`) | one collapsed message (`:2314-2322`) |
| local-search probe before the backend | `:138-159` | none |
| "a definite verdict survives an expired deadline" | none | `:2281-2296`, `:2304-2312`, measured on `nia-bounded-blast` |
| what it dispatches to | a caller-supplied `SolverBackend` (`:161`) | the whole router, `check_auto_inner` (`:2280`) |

The reductions themselves are identical in both — `canonicalize_terms` →
`propagate_values` → `solve_eqs_bounded(DEFAULT_SOLVE_EQS_FUEL)` →
`elim_unconstrained` → `canonicalize_terms`, composing one
`ModelReconstructionTrail`. As with ADR-1810, the duplication is orchestration,
not algorithm.

The last row is the one that stops this being a straight deletion. `preprocess.rs`
wraps *a backend*; `auto.rs` re-enters *the router* with `preprocess` cleared.
`abv.rs:3242` deliberately wants the backend form — routing it through
`check_auto_inner` would re-enter dispatch from inside the array CEGAR. So one of
the two differences is legitimate and must survive the merge as a parameter.

## Decision

**`crates/axeyum-solver/src/preprocess.rs` is the one home for word-level
preprocessing: one reduction function and one replay function, parameterized over
the solve call. `auto::preprocess_reduce` (`auto.rs:2158-2198`) and
`dispatch_reduced`'s reconstruct/replay/model-build block (`auto.rs:2299-2346`)
are deleted and replaced by calls into it.**

The split of what moves and what stays:

| moves into `preprocess.rs` | stays at the call site |
|---|---|
| the reduction, as a fixpoint loop with `MAX_PREPROCESS_ROUNDS` **and** `auto.rs`'s per-pass deadline polling | `auto`: `reduction_shrinks_encoding`, the definite-verdict-survives-the-deadline policy, the fall-back-to-unreduced arm |
| the replay + model build, carrying **all three** witness kinds with `preprocess.rs`'s three distinct failure messages | `preprocess`: the local-search probe |

`preprocess.rs` is the home rather than `auto.rs` for three reasons, in order of
weight: a reduction pipeline is not dispatch, and `auto.rs` is the dispatcher;
`preprocess.rs` is already the named, documented, publicly exported module; and
`auto.rs`'s own doc comments already point at it as the definition of the
discipline they implement (`auto.rs:2156`, `:2204` — "the same checkable-`sat`
discipline as [`crate::check_with_preprocessing`]").

**The merged replay carries symbols, function interpretations, and
`real_div_zeros` — the union, which is today's `auto.rs` behaviour.** No public
signature changes: `check_with_preprocessing` keeps its `&mut B: SolverBackend`
shape.

**This ADR does not decide that the front door starts running 8 rounds.** The
merged reduction takes the round cap as a parameter; whether the front door's cap
goes from 1 to `MAX_PREPROCESS_ROUNDS` is a measured decision gated on the
re-measurement named below, because the guard that protects the front door from a
bad reduction was calibrated against one round.

## Evidence

- Source read at `ea8515407`, 2026-09-09; every line number above verified
  individually rather than taken from the inventory.
- `git blame -L 2338,2346 crates/axeyum-solver/src/auto.rs` → `124e18aa00`,
  2026-07-02, which is what settles the `/0` question against the inventory.
- `preprocess.rs:72-80` argues the fixpoint is not cosmetic: "One pass is not
  enough: `elim_unconstrained` can expose a fresh constant that
  `propagate_values`/`solve_eqs` then eliminate, and the re-canonicalization
  AC-normalizes substituted product trees that reveal further folds." That is an
  argument, not a measurement, and it has never been measured against the front
  door's corpus.
- `auto.rs:2209-2232` is a measurement, and it points the opposite way about
  reduction in general: on `062-bench_2195` the term DAG **shrank** 1,375 → 1,215
  while the AIG grew 35,329 → 51,724 (+46%), and on `058-bench_165` the AIG grew
  +54%. That is why `reduction_shrinks_encoding` exists, and why more rounds is
  not obviously better.
- [ADR-1721](adr-1721-a-preprocessing-step-owes-one-of-three-obligations-chosen-by-the-direction-it-can-break.md)
  — what a preprocessing step owes, chosen by the direction it can break. Both
  pipelines here discharge it the same way, by replaying the reconstructed model
  against the original assertions; the merge must not weaken that.

## Alternatives

**Keep `auto::preprocess_reduce` as the home and delete `preprocess.rs`.**
Rejected. It deletes a public API item (`full_exports!`, `lib.rs:1268`), it
deletes the local-search probe `abv.rs:3242` uses, and it puts a term-rewriting
pipeline permanently inside an 8,000-line dispatcher, which is the condition that
produced the divergence in the first place.

**Keep both and give the inventory's divergence an owner without merging.**
Rejected. The divergence is not a documentation gap: `auto.rs` gained the
function-interpretation carry and `preprocess.rs` did not, and nothing announced
it. A second copy is what makes that possible; an owner does not remove it.

**Merge the dispatch too — one entry point that takes a router.** Rejected.
`abv.rs:3242` calls this from *inside* the array CEGAR and must reach a specific
backend, not re-enter `check_auto_inner`. Collapsing the two dispatch shapes into
one is how a recursion gets built.

**Do nothing; the item is cosmetic.** Not rejected outright — it becomes the
right answer if the experiment below shows the dropped function interpretation is
unreachable *and* the fixpoint buys nothing on the corpus. That is stated under
*What would falsify this decision* rather than hidden.

## Consequences

**What is lost if the migration is careless** — each of these lives in exactly
one of the two copies, so a "take the superset" merge can drop any of them
silently:

1. **The six `past_deadline` checks** in `auto::preprocess_reduce`. `preprocess.rs`
   has none, so if the merged reduce takes its shape, an 8-round loop can run
   well past the caller's budget with no poll. The merged function must poll, and
   the poll must be inside the round loop, not only before it.
2. **`reduction_shrinks_encoding`** (`auto.rs:2233`), and more importantly its
   calibration. Its three measured rows were taken against a **one-round**
   reduction. A fixpoint substitutes more, and substitution duplicates structure
   the term DAG was sharing — which is the exact mechanism those rows measure. So
   raising the front door's round cap without re-measuring this guard can inflate
   encodings on files it currently rescues. It must also stay at the `auto` call
   site: `preprocess.rs`'s caller is a backend that may not bit-blast at all, and
   `lower_terms` **panics** rather than erroring on a non-BV query
   (`auto.rs:2243-2251`).
3. **`preprocess.rs`'s three replay failure messages** (`:194-212`) — evaluated
   false, evaluated non-Boolean, failed to evaluate. `auto.rs` collapses all three
   into one string. These are soundness-alarm diagnostics; the granular form is
   the one to keep.
4. **The local-search probe** (`preprocess.rs:138-159`), which returns an
   already-replayed `sat` before the backend runs. It is `abv.rs`'s reason for
   calling this module rather than the backend directly.
5. **`auto.rs`'s definite-verdict-survives-the-deadline policy** (`:2281-2296`,
   `:2304-2312`). Measured: `nia-bounded-blast` decides `nia-pythagorean` a hair
   past the budget, and an unconditional `past_deadline` gate turned that decided
   `sat` into `unknown`. A merge that re-adds a bail there loses a real answer.
6. **The function-interpretation carry itself** — the thing this whole ADR is
   about. The merged replay must build the model from all three loops, and a test
   must die if any one of them is removed.

**What becomes easier.** One place for the reduction, so a pass added for roadmap
2.x reaches both callers. One place where the model-witness set is decided, so
"which witnesses does a preprocessed model carry" has a single answer with a
single test — instead of two answers that drifted apart for two months without
anything noticing.

**What becomes harder.** `preprocess.rs` gains a parameterized solve call and a
round cap, so its currently very readable 229 lines get an indirection. The
`auto` call site gets slightly longer, because the policy that stays there is now
visibly separate from the reduction that left.

**Revisit when** roadmap 1.1 lands the warm solver on the front door. That change
touches `dispatch_reduced`'s neighbourhood and the CEGAR loops the reduction
feeds; the two should not be in flight at once in the same functions.

## Migration

Roadmap item 1.4. This is the DECISION half; the code is a later lane's.

1. In `preprocess.rs`, extract `reduce_to_fixpoint(arena, assertions, deadline,
   max_rounds) -> Result<Option<(Vec<TermId>, ModelReconstructionTrail)>, SolverError>`
   — the existing `:85-136` loop with a `past_deadline` poll before each of the
   five passes, returning `Ok(None)` on expiry exactly as `auto.rs:2163` does.
2. In `preprocess.rs`, extend `replay_preprocessed_model` (`:177`) with the
   function-interpretation loop from `auto.rs:2331-2338`, keeping its own three
   failure messages. Make it `pub(crate)`.
3. Repoint `check_with_preprocessing_impl` at both, passing
   `MAX_PREPROCESS_ROUNDS`. No behaviour change except the added witness kind —
   which is the point.
4. Delete `auto::preprocess_reduce` (`:2158-2198`); call
   `preprocess::reduce_to_fixpoint(.., 1)` from `auto.rs:1766`. Delete
   `dispatch_reduced`'s block at `:2299-2346`; call
   `preprocess::replay_preprocessed_model`. Keep `reduction_shrinks_encoding`,
   the fall-back-to-unreduced arm, and the definite-verdict deadline policy where
   they are. **The round cap stays 1 in this step**, so the merge is a pure
   refactor with one witness-carry addition and nothing else moves.
5. Separately, and gated on measurement: raise the front door's cap from 1 toward
   `MAX_PREPROCESS_ROUNDS`, re-measuring `reduction_shrinks_encoding`'s three rows
   at the new cap first, and gating on the `QF_BV` parity slice and the `:status`
   sweep.

**Exit criterion.** The roadmap's own wording is good and is kept, with one
sharpening — since the front door already carries `/0`, a fixture that only
exercises `/0` cannot distinguish the merged path from today's:

> A fixture carrying a real `/0` witness **and** an uninterpreted-function
> interpretation replays through the merged path from **both** entry points
> (`check_with_preprocessing` and the front door), and `preprocess.rs:221`'s
> "wrong `sat`" comment describes a case that is now tested rather than one the
> front door can hit.

**Negative controls — three, because the fixture has three carries and a fixture
that passes with a carry deleted is measuring nothing.** Delete each of the three
loops in the merged `replay_preprocessed_model` in turn (symbols, functions,
`real_div_zeros`) and require that **exactly one** test dies each time, and a
different one. The function-interpretation control is the load-bearing one: it is
the carry `preprocess.rs` does not have today.

**The separate experiment this ADR does not settle**, to be run before or with
step 2, because its answer decides whether item 1.4 is a latent-defect fix or a
tidy-up:

> Construct an AUFBV query whose uninterpreted function has an interpretation not
> forced by the scalar abstraction, drive it through the shipping dispatch so it
> reaches `abv.rs:3242`, and inspect the `Model` that
> `check_with_preprocessing_and_local_search` returns. Record (a) whether a
> `function` entry is present, (b) if absent, whether `complete_assignment`
> (`abv.rs:3444`) substitutes a default, and (c) whether the array path's final
> original-formula replay rejects the result or accepts it. Report the finding
> either way; "could not construct a reaching query" is a finding too, and is the
> one that makes 1.4 cosmetic.

## What would falsify this decision

- **The exposure is unreachable and the fixpoint is worthless.** If the
  experiment above cannot construct a query that reaches `abv.rs:3242` with a
  live function interpretation, *and* raising the round cap moves no verdict and
  no PAR-2 on the parity slice, then item 1.4 is a tidy-up with no measured value
  and belongs below the Phase 1 items that have one. Say so and reorder rather
  than executing it out of tidiness.
- **The fixpoint inflates encodings.** If re-measuring
  `reduction_shrinks_encoding`'s rows at a raised cap shows the guard declining
  materially more often, the fixpoint is not the improvement `preprocess.rs:72-80`
  argues it is on this corpus, and step 5 does not happen — the merge still does,
  at cap 1.
- **The backend/router split cannot be parameterized.** If `abv.rs:3242`'s
  backend-shaped call and the front door's router-shaped call cannot share one
  reduce + replay without a type gymnastic that obscures either, the two dispatch
  shapes are a real boundary and the right answer is to share only
  `replay_preprocessed_model` — the witness set, which is the part that actually
  drifted — and leave the reduction duplicated with a test pinning the two pass
  sequences equal.
- **A verdict moves at step 4.** Step 4 is asserted to be a pure refactor plus one
  added witness carry. Any `:status` or parity verdict change there means it was
  not, and the merge must be re-derived rather than accepted.
