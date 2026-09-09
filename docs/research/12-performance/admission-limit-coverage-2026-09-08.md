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
| registry entries | 114 | **455** |
| distinct modules covered | 19 | **98** |
| dated justifications | 29 | **72** |
| admission class | 71 | **296** |
| …of those, dated | 23 | **42** |
| admission-class bounds crossing with **no signal** | 12 | **129** |
| …of those, attributable (`note_crossed` wired) | 1 | **17** |
| …structurally unattributable from this crate | — | 1 |
| …enumerated backlog | — | 111 |

512 constants outside the governed files were examined and 340 registered;
the rest are classified out of scope with a stated reason rather than omitted.
One more (`sat_bv_backend::MAX_LINKED_PROOF_STEPS`) landed on main while this
lane was in flight and was registered on merge — see below.

**The row that matters is the last group.** "12 admission-class entries cross
with no signal" was published as a property of the solver. It was a property of
the 19 files that had been read. The real figure is **129**, and rank 4 of that
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

129 silent bounds; 17 wired this session; 1 unwireable from this crate
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

## Seventeen gates made attributable

Eleven of the twelve originally enumerated, plus the five reclassified below,
plus `abv::MAX_ROW_SITES` — registered by the QF_ABV lane as `Signal::None`
while this one was in flight, and wired on merge because the ratchet refuses to
backlog a bound that arrives after the backlog was drawn.
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

## Ranking, measured: 15 files of 1,101 cross an instrumented bound

Rank 4 of the previous lane's table read *"cannot be ranked: no route-attribution
data exists for a crossing that emits no signal"*. With sixteen gates wired, part
of it can now be measured instead of reasoned. This is the first ranking in this
programme that came out of a run's own output.

**Method.** `target/release/examples/smtcomp_cli --trace --timeout-ms 4000`,
`taskset -c 0-7`, over 1,101 files (`corpus/regression`,
`corpus/public-curated`, `corpus/qfbv-curated`, `corpus/micro`). 1,094 emitted a
`; config` line; the `crossed=` field was collected per key. Shared dev box,
other lanes active — verdicts and RSS are robust to that, wall times are not and
are only quoted within a back-to-back pair on one file.

Run twice: once before merging `origin/main` and once after. **The crossing
table below is identical across both runs** — same 15 files, same keys, same
counts — which is the only reason to trust it against a tree that moved
underneath it. Only `consulted=` shifted (111 -> 113 files), because main's
QF_ABV work moved two files onto the simplex path.

`abv::MAX_ROW_SITES`, wired on merge, crossed on **zero** of these 1,101 files.
That is not evidence it never bites: the QF_ABV lane measured it firing on
`brummayerbiere/fifo32ia04k08` (4,109 sites) and `wchains140se` (4,484), and
neither is in this corpus — they live in the unextracted
`corpus/public/QF_BV.tar.zst`. A zero here means "not in this population", not
"never".

| | files |
|---|---:|
| traced | 1,094 |
| emitting a `consulted=` field (an instrumented bound was *looked at*) | 113 |
| emitting a `crossed=` field (a bound *bit*) | **15** |
| …of those, still decided | **11** (7 unsat, 4 sat) |
| …of those, ending `unknown` | **4** |

Per key, by files where it bit:

| Bound | files | observed / bound | verdicts |
|---|---:|---|---|
| `dpll_lia::MAX_INITIAL_BOUND_IMPLICATION_ATOMS` | 8 | 514, 515 ×4, 586, 1222, 6504 / **512** | 4 unsat, 4 unknown |
| `nia_linearize::MAX_SMALL_DOMAIN_WIDTH` | 7 | 24, 29, 34, 39, 41, 55, 63 / **4** | 3 unsat, 4 sat |
| `dpll_lia::MAX_TWO_EDGE_DIFF_EDGES` | 1 | 672 / 512 | unknown |
| `dpll_lia::MAX_PRE_SAT_ARITH_ATOMS` / `MAX_PRE_SAT_CNF_VARS` | 1 | 6504 / 1024, 20520 / 4096 | unknown |

And the negative result, which is the more useful half:
`simplex::MAX_TABLEAU_CELLS` is **consulted on 108 files and crossed on zero**.
A bound looked at constantly that never bites is not a candidate for
re-derivation, and before the instrumentation nothing could say that about any
bound in this table.

### `MAX_INITIAL_BOUND_IMPLICATION_ATOMS`: re-derived, and it costs nothing here

Five of its eight crossings are within 15 % of the bound and **three are within
three atoms of it** (514/512, 515/512). A bound refusing work at its own
boundary on real files is exactly the shape the `dpll_lia` rectangle turned out
to have, so it was re-derived rather than assumed.

**Method.** All eight crossing files through the shipped front door at
`--timeout-ms 24000`, release, `taskset -c 0-7`, with the bound at its committed
512 and again at 16,384 — a 32x envelope — the two arms run back to back on each
file so host load drifts across the pair rather than across the arms.

| | 512 (shipped) | 16,384 |
|---|---|---|
| verdicts | 4 unsat, 4 unknown | **identical, file for file** |
| worst-case peak RSS | 492 MiB (`guarded_product_factorial_bound`) | 492 MiB |
| largest RSS increase | — | +42 % on `cli__regress4__bug337` (45.9 → 64.7 MiB) |
| `cli__regress4__bug337` wall | 25.0 s (whole budget) | 5.9 s, still `unknown` |

**No decision rides on this bound on this corpus.** That is a real result and
the honest form of it is narrow: raising the envelope 32x recovers nothing, so
the bound is not carrying losses here — and it also does not measurably protect
anything at 512 rather than 16,384, since the whole process stays under 80 MiB
in both arms. "512 is right" is not what was shown; "512 is not costing us
files, and nothing distinguishes it from 16,384 in either direction" is.

`MAX_SMALL_DOMAIN_WIDTH` needs no A/B: all seven files that cross it are decided
anyway, at 6x to 16x the bound. The relaxation it forgoes was not needed.

**What this ranking cannot say.** It covers the **17 instrumented gates of 129**.
The other 111 emit nothing, so a file lost to one of them looks exactly like a
file lost to search. The measurement is a lower bound over an instrumented
subset, and the subset is 13 % of the population — which is the argument for
closing the backlog rather than a substitute for it.

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

## The rustdoc trap, third and fourth instances — and what was NOT re-based

`79a7c5297` (the memory-limit lane) turned the staleness gate red on
`lra_online::DEFAULT_ONLINE_LRA_BUDGET_BYTES` and
`lra_theory::MAX_ONLINE_LRA_ATOMS`. Its entire touch of that symbol in
`lra_online.rs` is **one added line inside a doc comment**:

```rust
/// [`DEFAULT_ONLINE_LRA_BUDGET_BYTES`] it reproduces `MAX_ONLINE_LRA_ATOMS`
```

The value is untouched at `640 * 1_024 * 1_024`, and `lra_theory.rs` was not in
the commit at all. Same shape as `drat::CACHE_DROP_INTERVAL_BYTES` and
`euf::MAX_ENCODED_DECLARED_SORT_CEGAR_PAIRS`: **four instances now, all from a
`rests_on` that names the constant itself.** Treat that as a rule, not a
coincidence — a dependency should name the mechanism a measurement was *of*.

### Why re-basing is honest here, and what was checked before deciding

Re-basing is the wrong answer when a measurement genuinely needs re-taking, and
`79a7c5297` is not a harmless commit: it established that `memory_limit_mb`
**did not bind at all** until 2026-09-08, and it re-attributed one of ADR-1752's
three cost-model refutations (the 7.8 GB abort on
`_sanfoundry_10_ground.i_6_3_3.bpl_13.smt2`) to the *offline* Fourier–Motzkin
route via a live stack sample. Either could have invalidated the ADR.

Neither does, and the reason is in ADR-1752's own text. The two entries do not
rest on that refuted evidence. They rest on a **calibration identity**: the
budget is chosen so `NormalizationLimits::for_budget`'s derived ceilings sit
right, and so `budget_bytes / BYTES_PER_ADMITTED_ATOM` reproduces `1_024`
*exactly* at the default. That identity is checkable in the tree, not in a
corpus run, and nothing in `79a7c5297` moves it — the same argument the
memory-limit lane itself used when it re-derived `BYTES_PER_ADMITTED_ATOM` on
2026-09-08 and **kept the value**.

So the dates stay at 2026-09-07 and the dependencies move to the mechanisms:

| entry | was | now |
|---|---|---|
| `DEFAULT_ONLINE_LRA_BUDGET_BYTES` | the constant + `MAX_ONLINE_LRA_ATOMS` | `for_budget` (the derivation) + `check_qf_lra_online_cdclt` (the route that takes it) |
| `MAX_ONLINE_LRA_ATOMS` | the constant + `MAX_LRA_CACHED_COEFFICIENTS` + `DEFAULT_ONLINE_LRA_BUDGET_BYTES` | `MAX_LRA_CACHED_COEFFICIENTS` (**kept**) + `check_qf_lra_online_cdclt` + `nra::admission_fits_consumer` |

`MAX_LRA_CACHED_COEFFICIENTS` is kept as a named *constant* deliberately and is
now the only one: it is ADR-1752's founding example, the dependency whose absence
let a 2026-08-03 measurement stand after the 2026-08-06 commit that falsified it.

Each replacement was checked before it was written, in both directions —
`git log -G'<symbol>' --since=2026-09-07` is **empty** for all three (so none is
a real staleness being hidden), and `git log -G'<symbol>'` over all history
**matches** for all three (so none is a dead query that can never fire). A
symbol chosen only to make a gate green would fail the second check, and that is
the check worth running.

### The finding that came out of it

`MAX_ONLINE_LRA_ATOMS` is no longer the LRA route's own gate — ADR-1752 replaced
it with `budget_bytes / BYTES_PER_ADMITTED_ATOM`, which is 1,024 at the default
budget and **13,107 at `--memory-limit-mb 8192`**. But
`nra::admission_fits_consumer` still projects against the **static 1,024** and
calls it the consuming engine's capacity, per ADR-1751.

So above the default budget the two are incommensurable again: the LRA consumer
admits 13,107 atoms while the NRA gate refuses above 1,024. **That is the exact
defect ADR-1751 existed to remove, reintroduced in a new form by ADR-1752**, and
it is the same shape as the `MAX_TABLEAU_CELLS` (4 M cells) against
`simplex_admission` (268 M at 8 GiB) divergence the budget-discipline lane
recorded — 67x apart, in different units, on one allocation. Recorded on the
entry, not resolved: it needs a measurement of what the NRA route can actually
afford at a raised budget, not an edit.

## The undated share is now in the run's own output

459 entries, 77 dated. The sweep took the table from 114 to over 450 by reading
code, and reading code establishes what a bound DOES, never what its value
should BE — so roughly **five undated entries for every dated one** is the
honest headline, and it was visible only in a checker's first line.

- `undated_count()` sits beside `dated_count()`, derived, never written down.
- `config_trace_line` prints `undated=` on every `--trace` run, from the one
  shared formatter, so the watchdog's partial line carries it too.
- The module doc leads with it, where a reader of the table arrives.
- `DATED_FLOOR` + `the_dated_count_only_rises` ratchet the **dated count**, not
  the share. Ratcheting the share would pay a lane to leave a bound
  unregistered, since registering an unmeasured value moves the percentage the
  wrong way. What must never happen quietly is *losing* a date — most temptingly
  by downgrading an entry to `undated` when its `rests_on` goes red instead of
  re-deriving it, which turns a finding into a silence. That exact edit is a
  registered mutation and it kills exactly one test.

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
  `on_exceed`. There is a measurement rather than
  an assurance, from two independent samples. `quant_bool_model_sat.rs` was read
  by two of the six readers: on seven constants they agreed on those two fields
  **five times and disagreed twice** (`Time`/`DeclineRoute` against
  `Soundness`/`RefuseUnknown`). Separately, the QF_ABV lane registered
  `abv::MAX_ROW_ROUNDS`, `abv::MAX_ROW_SITES` and
  `ufbv_online::MAX_INPUT_DAG_NODES` the same day this lane did, and on merge
  **one agreed on both fields and two did not**. Ten constants, seven
  agreements — roughly **70 % independent agreement** on a small sample.

  Every disagreement was settled by reading the call site, and in every case the
  wrong reading was the one that had **not been measured firing**:
  `MAX_ROW_SITES` produces an `Ok(None)` reported as an array *shape* message
  for a *capacity* event, so `Signal::None` is right and this lane's `ToCaller`
  was wrong; `MAX_INPUT_DAG_NODES` gates the first route every array query
  tries and raising it abstracts a bigger DAG, so `Memory`, not `Time`. Treat
  the judgement fields as informed opinion about the code, not as a verified
  property of it — the calibration now also lives in `config_registry`'s module
  doc, where a reader of the table will meet it. A wrong entry can only fail this module's own
  checks; nothing in the solver reads the registry.
- **One more entry was registered on merge.**
  `sat_bv_backend::MAX_LINKED_PROOF_STEPS` (8,000,000) landed on main while this
  lane was in flight, and it is exactly the class this lane exists for: it is
  *dated*, and its own doc says the cap clears the worst observed instance by
  **4.06x**, not the orders of magnitude its size suggests. Crossing it does not
  refuse — `ReductionLink::check_unsat` falls back to checking the `unsat`
  against the REDUCED formula and tells the caller so
  (`ProofCoverage::Reduced(ReducedReason::OverBudget { steps, budget })`), so it
  is `Truncate`/`ToCaller`: the bound weakens what the certificate is *about*,
  and says which. Registered rather than left as a fresh gap in a file this lane
  claims to have swept.

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
