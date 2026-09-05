# ADR-1661: the replay census covers every carrier, and `Type`-valued theorems are a named class

Status: accepted
Date: 2026-09-05
Lane: `lean-replay-census-all`

Index-summary: ADR-0760's per-declaration independent-replay census is
extended from the constructed reals to every carrier the kernel builds, with
the carrier list derived from `src/lib.rs`'s re-export block rather than
recalled; the three grades (`representable`, `theorem_type_not_prop`,
`blocked_by_dependency`) become the shared vocabulary, the `Type`-valued
theorems become a NAMED class of 50 rather than a count, and a `everything`
carrier builds all of them into one kernel so the headline is a union rather
than a sum of nesting rows. Measured on the cross-check pin (Lean
4.34.0-rc1): of 4,478 proved declarations Lean's kernel accepts 4,394, 50 are
`Type`-valued theorems it refuses as theorems, and 34 are blocked behind one
of those.

## Context

[ADR-0760](adr-0760-independent-replay-is-graded-per-declaration-by-name.md)
settled *how* an independent replay grade is earned: read back the constant
names Lean's own kernel ended holding (`replay-lean4export.lean
--emit-names`, which dumps `env.constants`), and grade each subject by
membership of *its own name*. No family, no module, no prefix, no sibling —
because each of those is a route by which an unchecked theorem inherits a
grade from a checked one. That discipline is right and this ADR does not
change it.

What ADR-0760 did not do is apply it to more than one carrier. Its suite,
`real_lean_replay_census`, builds `build_creal_prelude` and nothing else. The
kernel builds sixteen other carriers — `logic`, `nat`, `axreal`, `int`,
`characterization`, `ipc`, `ipc_eval`, `list`, `rat`, `string`,
`arith_models`, `complex`, `cpoint`, `metric`, `intspace`, `rn` — and no
external checker had ever been pointed at any of them by name.

Three consequences, all recorded in
`docs/math-department/14-lean-lang.md`:

1. **The chair's headline could not be completed.** "N axiom-free results"
   had no companion "and Lean's kernel accepts M of them", because M existed
   for one carrier out of seventeen.
2. **Reviewer 02's objection had a count and no names.** "48 theorems are
   `Type`-valued and Lean's kernel refuses them as theorems" — which 48? The
   suite printed them to stdout on each run and nothing captured them, so the
   figure could only be re-derived by re-running a four-minute census.
3. **The `creal` floor had stopped ratcheting.** It was set at 1,900 on
   2026-08-30 against a measured 1,972. The carrier held 3,542 replayable
   declarations six days later, so the floor could have absorbed the silent
   loss of nearly half the carrier without a word.

## Decision

### 1. The census covers every carrier, and the carrier list is derived

A new suite, `crates/axeyum-lean-kernel/tests/real_lean_replay_census_all.rs`,
runs ADR-0760's census over every carrier the kernel builds, one `#[test]`
per carrier. The classifier, the exporter call, the Lean invocation and
`grade` move into `tests/support/replay_census.rs` and are included by
`#[path]` into **both** suites, so the two cannot drift.

The carrier list is not a literal anyone maintains from memory.
`every_public_prelude_builder_is_accounted_for` reads `src/lib.rs`'s `pub use`
re-export block — the authority for what this crate offers to build — pulls
every `build_*` name out of it, and requires each to appear in a `BUILDERS`
table under one of three dispositions:

- `Carrier(name)` — a census carrier runs this builder directly;
- `CoveredBy(name)` — a census carrier's build runs it transitively;
- `NotACarrier(reason)` — excluded, with a reason of substance.

It checks both directions (a builder the crate exports and the table omits is
a gap; a table row the crate no longer exports is stale), checks that every
`Carrier`/`CoveredBy` target is a carrier that actually exists, checks that
every carrier is produced by some public builder, and carries a positive
control so that a broken `pub use` scan fails as a parse error rather than
passing as "the crate exports no builders". Adding a prelude to the crate
without adding it to the census fails that test.

### 2. Three typed classes, and the non-representable ones are NAMED

Every declaration falls into exactly one class, decided in *this* kernel by
inference and then earned against Lean's:

- **`representable`** — the wire format carries it and Lean's kernel will
  accept its kind. Every one of these **must** be admitted by Lean under its
  own name; `missing == 0` is enforced per carrier and is the check that
  cannot be satisfied by admitting fewer things.
- **`theorem_type_not_prop`** — a `Declaration::Theorem` whose type is not a
  proposition. `Lean.Environment.addDeclCore` refuses a `theorem` whose type
  does not live in `Prop`.
- **`blocked_by_dependency`** — its dependency closure reaches one of those.
  The **blocker is named**, not just the reason, because "why can this not
  go" and "what is it waiting on" are different findings.

Both non-representable classes are printed member by member, every run, and
the full lists are published in
[`artifacts/measurements/lean-replay-census-2026-09-05.md`](../../../artifacts/measurements/lean-replay-census-2026-09-05.md).
A count is not an answer to "which ones".

### 3. What a `Type`-valued theorem means for independent checkability

This kernel admits `Theorem`s whose type is not a `Prop`; Lean's does not.
The affected declarations are deliberate and the reason is written down in
`creal/uniform_convergence.rs`: `CReal.UniformConvergesOn` is `Type`-valued
because `Exists.rec` cannot eliminate into `Type`, so the convergence *rate*
must be data rather than an existential. The same argument shapes
`UniformlyContinuousOn` and `HasDerivativeAt`.

The position this ADR takes is the one the previous lane stated and this one
confirms across every carrier: **it is not a demonstrated soundness hole, but
it is a real gap in independent checkability.** Nothing here exhibits a wrong
statement, and this kernel's own type checker admitted each of them. What is
true is narrower and worth saying plainly: for these 50 declarations, and the
34 that depend on them, **no second kernel has confirmed what we admitted**.
They therefore hold no independent-replay grade, and the census records that
rather than folding it into a percentage.

That Lean refuses them **for this reason** is earned, not asserted:
`lean_really_does_refuse_a_theorem_whose_type_is_not_a_proposition` hands
pinned Lean `CReal.weierstrassMTest` alone and requires the rejection to come
from the kernel (`REAL LEAN KERNEL REJECTED`), to be for the recorded reason
(`is not a proposition`), and to name that declaration. Without it the
classifier could exclude anything it liked and the census would stay green.

### 4. A union carrier, because the per-carrier rows nest

`rn` ⊇ `metric` ⊇ `cpoint` ⊇ `creal` ⊇ `rat` ⊇ `int` ⊇ `nat` ⊇ `logic`, and
six other containments hold besides. Adding the rows up counts most
declarations six or seven times. So a seventeenth carrier, `everything`,
builds every carrier into **one** kernel, and it is the only row a headline
may be read from. The coverage guard names it explicitly as the one carrier
no single builder produces, rather than skipping it by a wildcard.

### 5. Concurrency is a lock, not a documented flag

`scripts/check-lean-gate.sh` runs each registered suite as
`cargo test -q -p <pkg> --test <target>` with the **default** thread count.
Seven of these carriers hold a full `CReal` kernel, so a module-header note
saying "`--test-threads=1` is not optional" would be a rule enforced only on
whoever read it, and the resulting failure in the gate would look like the
host's rather than this suite's. The constraint is therefore a
`static ONE_CARRIER_AT_A_TIME: Mutex<()>` held across each carrier's build and
census. A poisoned lock is taken with `PoisonError::into_inner`, so one
carrier failing lets the other sixteen report their own verdicts instead of
replacing sixteen findings with one message about a mutex. It bounds memory,
not wall time: the Lean replays are separate processes and were never the
parallel part.

### 6. The floors

Each carrier carries a monotone floor set below its measurement with
headroom. `real_lean_replay_census`'s `creal` floor is **raised 1,900 →
3,350**; it is not lowered. `scripts/check-lean-gate.sh` registers the new
suite and raises `CHECK_FLOOR` 261 → 278, which is exactly its seventeen Lean
invocations (the three non-Lean tests contribute none).

## The measurement

Cross-check pin, `leanprover/lean4:v4.34.0-rc1`
([ADR-1660](adr-1660-there-are-two-lean-pins-and-every-claim-names-which-one-it-means.md)
disambiguates it from the Mathlib corpus pin, which does not move with it),
commit `3328d2a80`, 2026-09-05. `20 passed; 0 failed` in 738.79 s for the new
suite and `5 passed; 0 failed` in 104.18 s for the `creal` suite. Every
carrier ran; none was skipped.

| carrier | population | representable | replayed | `Type`-valued | blocked | missing |
|---|---:|---:|---:|---:|---:|---:|
| `logic` | 99 | 99 | 99 | 0 | 0 | 0 |
| `axreal` | 129 | 129 | 129 | 0 | 0 | 0 |
| `nat` | 1,990 | 1,990 | 1,990 | 0 | 0 | 0 |
| `ipc_eval` | 2,003 | 2,003 | 2,003 | 0 | 0 | 0 |
| `list` | 2,021 | 2,021 | 2,021 | 0 | 0 | 0 |
| `ipc` | 2,040 | 2,040 | 2,040 | 0 | 0 | 0 |
| `string` | 2,086 | 2,086 | 2,086 | 0 | 0 | 0 |
| `int` | 2,391 | 2,391 | 2,391 | 0 | 0 | 0 |
| `characterization` | 2,427 | 2,427 | 2,427 | 0 | 0 | 0 |
| `rat` | 2,997 | 2,997 | 2,997 | 0 | 0 | 0 |
| `creal` | 3,617 | 3,542 | 3,542 | 49 | 26 | 0 |
| `arith_models` | 3,713 | 3,638 | 3,638 | 49 | 26 | 0 |
| `cpoint` | 3,766 | 3,691 | 3,691 | 49 | 26 | 0 |
| `complex` | 3,767 | 3,692 | 3,692 | 49 | 26 | 0 |
| `metric` | 3,863 | 3,788 | 3,788 | 49 | 26 | 0 |
| `rn` | 3,921 | 3,846 | 3,846 | 49 | 26 | 0 |
| `intspace` | 3,961 | 3,877 | 3,877 | 50 | 34 | 0 |
| **`everything`** | **4,478** | **4,394** | **4,394** | **50** | **34** | **0** |

**The sentence a chair may quote, and its only source is the `everything`
row:**

> Of 4,478 proved declarations, pinned Lean's kernel accepts 4,394; 50 are
> `Type`-valued theorems it refuses as theorems, and 34 are blocked behind
> one of those.

Every `Prop`-valued theorem this kernel has proved, in every carrier it
builds, is now independently admitted by an external Lean kernel under its
own name. The 84 that are not are named individually, with a reason each.

## Alternatives

- **One test over all carriers.** Rejected: the constructive carriers cost
  tens of seconds of Lean each on top of minutes of prelude build, so a
  single test would make "the census is green" mean "whichever carriers fit
  in the budget", and a carrier that timed out would be indistinguishable
  from one that passed. One `#[test]` per carrier makes "did not run" a
  reportable state.
- **Run only the maximal carriers** (`rn`, `intspace`, `complex`, …) and
  infer the rest by containment. Rejected for the same reason ADR-0760
  refused to grade a theorem from its family's aggregate: `nat ⊂ rn` is a
  claim about the build, and a census that leans on it stops measuring the
  moment the containment stops holding. Every carrier is built and replayed
  on its own; the containments are stated in the artifact as an argument
  against ADDING the rows up, never as a substitute for measuring one.
- **Only the union carrier.** Rejected: it hides where a regression is. The
  per-carrier rows are what turn "the census dropped by 20" into "`int`
  dropped by 20", which is how the post-merge movement in this lane's own run
  was attributed to `int_prelude/two_squares.rs` in one line.
- **Fold `theorem_type_not_prop` into "not exported" and report a
  percentage.** Rejected: it is the finding. A percentage would let the class
  grow without anyone noticing which theorems entered it.
- **Restate the 50 in `Prop`-valued form so the census reaches 100%.**
  Rejected here as out of scope, not as wrong. It would change the
  constructive content (the rate would stop being data), it is real
  mathematical work, and the census's job is to say precisely where that work
  would pay — the 34 blocked declarations hang off just five of the 50.

## Consequences

- `docs/math-department/14-lean-lang.md`'s row "our theorems replayed in
  pinned Lean" is no longer `creal`-only, and Next Ten item 2 is done.
- Reviewer 02's "48 theorems are `Type`-valued" now has 50 names and a
  published list, and the five that block the other 34 are identified — which
  is what makes item 3 (publish the constructive analysis as a Lean library)
  a scoped job rather than an open-ended one.
- A new prelude that nobody adds to the census fails
  `every_public_prelude_builder_is_accounted_for`, so the coverage cannot
  silently narrow the way it did between 2026-08-30 and today.
- `scripts/check-lean-gate.sh`'s `CHECK_FLOOR` is 278. A host without the
  pinned toolchain still fails by default, as it did before.
- The `creal` floor is a live ratchet again. Raising these floors as the
  carriers grow is the ratchet working; lowering one needs a reason in the
  commit message.
- **Known limitation, recorded rather than fixed:** the export emits the
  dependency *closure* of its roots, so a mutant that drops a non-leaf root
  from the export survives (`missing` stays 0, correctly — Lean still holds
  the name). A mutant that drops a leaf root is killed and names the loss.
  The guard is therefore sensitive to every loss that changes what Lean ends
  up holding, which is the property it claims; it is not a per-root
  transmission audit and does not claim to be.
