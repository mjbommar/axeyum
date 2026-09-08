# Closing the coverage on admission limits, 2026-09-08

Companion to
[admission-limit-basis-2026-09-08.md](admission-limit-basis-2026-09-08.md),
which built the `Basis` gate and re-derived the `dpll_lia` rectangle, and to
[config-registry-2026-09-07.md](config-registry-2026-09-07.md), which built the
registry. That lane's own closing section says what this one is for:

> **The gate works. The population is not covered.**

It ended with 113 entries over 19 governed files, a further **75 admission
limits it had found and not registered**, and one instrumented gate out of
twelve. This lane closes the enumeration, and the enumeration immediately
changed two of the previous lane's headline numbers — not because they were
computed wrong, but because they described the files that had been read.

## Coverage, before and after

| | before | after |
|---|---:|---:|
| registry entries | 114 | **454** |
| distinct modules covered | 19 | **98** |
| dated justifications | 29 | **68** |
| admission class | 71 | **296** |
| …of those, dated | 23 | **39** |
| admission-class bounds crossing with **no signal** | 12 | **128** |
| …of those, attributable (`note_crossed` wired) | 1 | **16** |
| …structurally unattributable from this crate | — | 1 |
| …enumerated backlog | — | 111 |

512 constants outside the governed files were examined and 340 registered;
the rest are classified out of scope with a stated reason rather than omitted.

**The row that matters is the last group.** "12 admission-class entries cross
with no signal" was published as a property of the solver. It was a property of
the 19 files that had been read. The real figure is **128**, and rank 4 of that
lane's loss ranking — *"cannot be ranked: no route-attribution data exists for a
crossing that emits no signal"* — applies to ten times as many bounds as it
said.

The 2026-09-07 measurement that produced the 12 was correct about its sample and
was not labelled as one. That is the general shape worth keeping: **a census
over a subset is a sample, and the honest failure mode of this programme is to
publish the subset's number as the population's.**

## What the sweep found that a name search cannot

Six read-only sweeps over `axeyum-solver`, `axeyum-rewrite`, `axeyum-cnf`,
`axeyum-smtlib`, `axeyum-bv`, `axeyum-aig` and `axeyum-egraph`, each deciding
every field from what the code does at its use sites.

### Divergent twins that no code links

The registry exists to make these visible; before this lane it could see two of
them.

| Twin | Divergence |
|---|---|
| `MEMBERSHIP_MAX_STATES` | **60,000** in `smtlib.rs`, **20,000** in `string_theory.rs`. Same name, same concept, 3x apart. |
| `RANGE_SIZE_CAP` (4096) | `quant_finite_cert.rs` and `quant_guarded_int.rs`. The doc comment *requires* them to match; nothing checks it. |
| `MAX_SPLIT_DEPTH` (64) | `uflia_online.rs` and `uflra_online.rs`, byte-identical doc comments. |
| `MAX_SPLIT_PAIRS` (64) | `combined_theory.rs` and `combined_theory_lia.rs`, each claiming to "mirror the cold core's `MAX_SPLIT_DEPTH`". Four copies of one number, none linked. |
| `STRING_MAX_LEN` / `DEFAULT_STRING_BOUND` (12) | three copies across two crates, one self-documented as a mirror. |
| `INPROCESS_MAX_VARIABLES` / `_CLAUSES` | `sat_bv_backend.rs` mirrors `inprocess.rs`'s defaults **by value only**. |
| `MAX_CODE_POINT` / `SMTLIB_MAX_CODE_POINT` | three copies of the SMT-LIB maximum across two crates; exactly one pair is pinned by a test. |

Each entry's `note` now names its twins. This is the same defect ADR-1751 fixed
for `nra`/`lra_theory`, unfixed in seven more places.

### One constant, two contracts, one file

`dpll_t::MAX_CERTIFIABLE_BOOLS` yields `Ok(Unknown(Incomplete))` at line 512 (a
soft decline) and `Err(Unsupported)` at line 576 (a hard error). The second is
reached by `evidence.rs` **re-checking evidence the first already produced**.
The registry previously governed only the `dpll_lia.rs` twin of that name.

### Code that contradicts its own comment

Three in `abv.rs` alone:

- `MAX_DIFF_SKOLEMS` documents "declining to unknown" and produces
  `SolverError::Unsupported` — a hard `Err` — at its only external call site,
  even though an unused `BuildFailure::Unknown` variant exists beside it.
- `MAX_STRUCTURAL_ARRAY_REALIZATION_STEPS` ends its route with
  `Err(Backend(..))` where every sibling in the file degrades to `unknown`.
- `MAX_BRANCH_SCALAR_CHOICE_DEPTH` is named for a depth and meters a *count*,
  checked once before any search runs.

This is why the registry's contract says a field is decided from the code: on
these three, a reader who trusted the comment would have written the wrong
`on_exceed` and never known.

### Bounds on code no shipping path reaches

`cube::MAX_PRODUCT_CUBE_SELECTORS` and both `inprocess.rs` defaults gate
functions that `axeyum-solver` never calls (reachable only from `axeyum-cnf`
examples and tests). `euf::MAX_ENCODED_DECLARED_SORT_CEGAR_PAIRS`'s only
production caller passes the *other*, terminal-rung bound instead — its note
describes protecting "an enclosing search" that does not exist today.

A bound on unreachable code cannot cost a file. Until now nothing said which
bounds those were, so every one of them sat in the same undifferentiated pile as
a bound carrying fifty.

### Bare integer literals, which no name-keyed registry can ever see

Swept deliberately rather than incidentally, and enumerated in
[bare-literal-guards-2026-09-08.md](bare-literal-guards-2026-09-08.md). The
headline is not the four sites the previous lane named; it is the **clusters**:

- `depth > 32` repeated **verbatim in 11 independent functions** in
  `parse.rs`'s exact-reasoning family. A change to one silently diverges from
  the other ten.
- `parts.len() > 6` in **six** sibling concat-rewrite helpers.
- `exact_ite_count(..) <= 6` at **four** sites, where `2^6 = 64` matches that
  file's separately named `EXACT_ITE_CASE_CAP` and nothing pins them together.
- `maxsat.rs`'s `bits > 127` — a hard `Err` ending the whole MaxSAT route.
- `bv2nat_blast.rs`'s `w >= 128` — an unlinked second copy of that same file's
  own `MAX_BLAST_WIDTH`.
- `qinst_egraph.rs`'s `attempts_since_clock_check >= 8192`, which sets how often
  a shared deadline is polled at all.
- `cas_poly.rs`'s `ideal_limits()` struct literal — four Gröbner-basis budgets
  as anonymous fields, backing the same search as the registered `MAX_IDEAL_*`.

None was registered: they have no key to register under, and inventing one is a
code change with its own review. They are written down so the next lane starts
from an inventory rather than a grep.

## The backlog is a ratchet, not an exemption

128 silent bounds; 16 wired this session; 1 unwireable from this crate
(`axeyum-rewrite::quantifiers::CHAIN_INSTANCE_CAP` — `note_crossed` lives in
`axeyum-solver`, which depends on `axeyum-rewrite` and not the reverse); 111
left.

Writing "111 remain" in a document is what this programme keeps doing and it is
not enough, so the number lives in the source where a test can hold it:

- `SILENT_UNATTRIBUTED` lists all 111 by key, sorted and unique.
- A key in it must **really** be silent, **really** be admission-class, and
  **really** have no `note_crossed` call site. Wiring a gate and leaving its
  line is a failing test, so the backlog cannot overstate the debt either — a
  number nobody can trust downward is as useless as one nobody can trust upward.
- `SILENT_UNATTRIBUTED_MAX` is asserted **equal** to the list length, not
  `>=`. Slack is room to grow.
- A silent bound that is neither wired, nor structurally excused, nor already
  listed fails outright, so a lane adding one inherits the requirement instead
  of being trusted to remember it.
- `uninstrumentable_bounds_are_outside_this_crate` refuses any line in
  `SILENT_UNINSTRUMENTED` naming a bound under `crates/axeyum-solver/`, because
  such a bound is reachable from `note_crossed` by construction. A coverage
  check that can be satisfied by editing its own exemption list is not a check.

## Sixteen gates made attributable

Eleven of the twelve originally enumerated, plus the five reclassified below.
Each records the crossing in the entry's own unit, never normalized; each is one
thread-local `Cell<bool>` read with no guard constructed; no verdict moves.

The ones worth naming are the ones where the *decline* had no body at all:

- `auto::MAX_COERCION_LINK` sat in a `let`-chain, so the refusal was the absence
  of a branch. It is now an `if`/`else` whose `else` is the record.
- `nia_linearize::MAX_CONGRUENCE_GROUPS` is the registry's own worked example of
  a bound with no `else`; it has one now.
- `nia_linearize::MCCORMICK_MAX_ABS_BOUND` was two byte-identical closures
  (`clamp` in `mccormick_lemmas`, `guard` in `derived_product_bounds`); they are
  one `clamp_to_mccormick_bound`, so a *dropped* endpoint and an *absent* one
  stop being the same `None`.
- `nia_linearize::MAX_SMALL_DOMAIN_PRODUCTS` records only when a product that
  **would** have been split is forgone. A spent budget nothing wanted is not a
  loss, and a recorder that cannot tell the difference launders "consulted" into
  "decided".

## Five entries claimed a signal the code does not emit

Each verified at the site rather than taken on report:

| Entry | Claimed | Reality |
|---|---|---|
| `lra_online::DEFAULT_STEP_BUDGET` | `ToCaller` | `solve_with_deadline` returns the same `None` for budget exhaustion and deadline expiry, and the sole converter emits `UnknownKind::Timeout` with detail *"timeout in the online LRA driver"* — a label that is actively **wrong** in the case this budget exists for (no deadline at all: the `wasm32` and default-`SolverConfig` path). `step_budget_hit`, the one accessor that could tell them apart, is read only by tests. |
| `simplex::MAX_PIVOTS` | `ToCaller` | `Tableau::run` breaks to the identical `RunOutcome::Unknown` for pivots and deadline; `Status::Unknown`'s own doc admits it covers "the pivot/deadline budget ran out" as one case. |
| `dl_online::MAX_SCALE` | `ToCaller` | a bare `None` from `scan_dl`, indistinguishable from every other decline there. |
| `nia_linearize::POW2_TABLE_MAX_CASES` | `DeclineRoute` / `NotApplicable` | tested in **one** `\|\|` with the next row, producing one `Ok(None)`; `abstract_pow2` declines no route, it omits the value-table axiom and keeps emitting its other families. That is `Relax`. |
| `nia_linearize::POW2_TABLE_MAX_EXP` | `DeclineRoute` / `ToCaller` | same condition as the row above, and registered with a **different signal**. Two disjuncts of one `if` cannot have different observability. |

All five now carry `Signal::None` with a `guarded_by`, and all five were wired in
the same change — so the reclassification adds five attributable gates rather
than five names to the backlog. The `POW2_TABLE_*` guard is split so each
disjunct records its **own** observed quantity, not the shared condition's.

Two statements in the table were also simply false:
`dpll_lia::MAX_TWO_EDGE_DIFF_EDGES`'s `guarded_by` claimed it "falls through to
the Bellman-Ford gate" — `negative_cycle_core` returns `None` immediately above
512 edges and never reaches that check; and `dl_online::MAX_DL_ATOMS`'s note
said no trace could attribute the route change, which stopped being true when
the gate was wired.

## The next stale limit: rank 1, and it went stale yesterday

`euf::MAX_ACKERMANN_CONGRUENCE_PAIRS = 64` is rank 1 of the previous lane's
ranking — reported to carry **52 of 58 QF_UFLIA losses** through
`try_lazy_arith_for_overbound`.

Its measurement is real and good. `6233a7c98` (2026-06-24) records a 40-pair
decidable frontier, a 117-pair smallest observed hang, a k=60 run unbounded past
200 s and a k=700 stack overflow.

**It is stale.** `eliminate_functions` — the O(k²) expansion the bound exists to
keep bounded — has changed **five times** since, most recently `7da79642f` on
**2026-09-07**. The measurement describes a tree that is gone, so the entry is
deliberately left `undated`, with the evidence in its `note`, rather than dated
to a measurement that no longer applies. Re-deriving it against today's
expansion is owed by the lane that owns the route.

Worth recording *how nearly this was missed*: `git log -G'fn eliminate_functions'`
is **empty** over the same window. The signature never moved; the body did. A
survey that asks about the declaration line gets a clean bill of health.

## Two rules the gates themselves taught

Both came out of gates going red on this lane's own work, which is the only kind
of evidence that a gate is doing something.

**1. A `rests_on` that names the constant itself is stale-tripped by
documentation.** Twice: `drat::CACHE_DROP_INTERVAL_BYTES` reported STALE against
`b405da6ef`, a rustdoc-link fix turning ``[`CACHE_DROP_INTERVAL_BYTES`]`` into a
plain code span; `euf::MAX_ENCODED_DECLARED_SORT_CEGAR_PAIRS` would have done
the same against `8d5ba48f0`. `git log -G` cannot tell such a diff from a code
change, and it should not try. Both now rest on the **function the measurement
was of** (`fn maybe_advise`, `check_qf_ufbv_lazy_with_pair_bound`), which is the
checker's own prescription — *"narrow the entry's `rests_on` if the change cannot
affect it"*.

**2. A negative control read inside the guard that already recorded the key is
vacuous.** `note_crossed` keeps only the **first** crossing per key, so once a
key is present the set cannot grow again, and

```rust
assert_eq!(admitted, crossed, "an admitted skeleton must add no crossing");
```

held no matter what. All four such assertions in the recorder's tests had it,
including the one that shipped with the recorder itself on 2026-09-08.
`scripts/tests/mutation_controls.py` said so out loud — the mutation *"an empty
product set is recorded as a crossing"* came back **SURVIVED**. Each negative now
runs under its own `ConfigTraceGuard` and asserts the set is **empty**, which is
an assertion that can fail.

## What was not done

- **The 111 remaining silent gates are not wired.** They are enumerated and
  ratcheted; wiring is per-gate work with a real test each, not a sweep.
- **Field-level review is per-entry work.** 340 entries were classified by six
  readers from the code. Mechanically verified for all 454: name, module and
  value against the source; `Signal::None` iff `guarded_by`; sorted and unique;
  every dated entry resting on a live path and naming a resolvable `Basis`; both
  Python gates green. **Not** mechanically verifiable: `protects` and
  `on_exceed`. `quant_bool_model_sat.rs` was read independently by two of the
  six, which gives a calibration sample of seven: **five agreed on those two
  fields and two did not** (`Time`/`DeclineRoute` against
  `Soundness`/`RefuseUnknown`), both resolved by hand at the call site in favour
  of the first reading. Treat the judgement fields as ~70 % independently
  agreed, not as a verified table. A wrong entry can only fail this module's own
  checks; nothing in the solver reads the registry.
- **`GOVERNED_FILES` is still 19.** Registering a file's constants and *claiming
  that file is completely covered* are different promises; the second needs an
  `EXEMPT` line per out-of-scope constant, which the sweeps produced as prose and
  not as table rows. The registry now describes 98 modules and claims complete
  coverage of 19 — which is a smaller lie than describing 19 and claiming 19,
  but it is still a gap and it is stated here rather than implied.
- **`MAX_ACKERMANN_CONGRUENCE_PAIRS` was not re-derived**, per the previous
  lane's ownership note. It is now *shown* stale rather than *suspected* stale,
  which is the difference between a hunch and a work item.
- **`canonical.rs::AC_REBUILD_MAX_OPERANDS` was not re-derived.** It has a real
  2026-08-02 measurement and `550b2c1f1` moved the bound out of a post-hoc
  `flat.len() > CAP` check into an early abort inside `flatten_ac_bounded` a week
  later. It stays undated with both facts in its `note`.
