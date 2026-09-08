# Admission limits whose justification has outlived its basis, 2026-09-08

Companion to
[config-registry-2026-09-07.md](config-registry-2026-09-07.md), which built the
registry, and to [ADR-1762](../09-decisions/adr-1762-the-configuration-surface-is-enumerable-recordable-and-dated.md),
which fixed the contract. That lane asked *what values govern the solver*. This
one asks the narrower and sharper question that three separate incidents this
month all turned out to be instances of:

> **A numeric admission limit silently refuses work. Its stated justification
> names a mechanism that no longer exists. Nothing notices.**

Each of the three was found by accident, while looking for something else. The
point of this lane is to stop finding them by accident.

## The class, stated precisely

Not every limit is in it. A limit that makes the solver **slower** is ordinary
engineering. The class here is limits that make the solver **answer worse**:
return `unknown`, decline a route it could have taken, or silently take a
weaker path. In registry terms that is

    on_exceed ∈ { RefuseUnknown, DeclineRoute }   ∪   { Relax with signal = None }

— the last disjunct because a relaxation nobody can observe is a route change
with the evidence removed.

**70 of the registry's 113 entries are in this class.**

## The three known instances

| # | Limit | Stated basis | Why the basis is gone |
|---|---|---|---|
| 1 | `dpll_lia::MAX_PRE_SAT_ARITH_ATOMS` / `MAX_PRE_SAT_CNF_VARS` (1,024 × 4,096) | "`BatSat` allocate\[d\] past an 8 GiB process ceiling … before its cooperative deadline poll", measured on `sal/pursuit-safety-16.smt2`, landed `d599b682f` 2026-08-08 | [ADR-1703](../09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md) (`317be80fe`, **2026-09-05**) took BatSat off every shipping path. `IncrementalSat` — the exact object `BoolSkeletonSolver.sat` holds — is now `NativeIncrementalCdcl`. The allocator named in the justification is reachable only behind the non-default `batsat-reference` feature, as a measurement oracle. |
| 2 | `lra_theory::MAX_ONLINE_LRA_ATOMS` (1,024) | an 8 GiB abort measured 2026-08-03 at `e62086742` | `MAX_LRA_CACHED_COEFFICIENTS`, the bound that caps exactly that cost, landed `96ff85930` on 2026-08-06 — **three days later**. Already fixed and re-dated by ADR-1752; it is listed here as the founding example, and it is the one the existing staleness checker's positive control fires on. |
| 3 | `euf::try_lazy_arith_for_overbound` at `ackermann_congruence_pairs > 64` | doc comment, undated | **Not this lane's** — owned elsewhere. Counted, not touched. |

Instances 1 and 3 are structurally identical to instance 2 and were each found
by a different lane looking at a different problem.

## Enumeration: what the class actually contains

Source of record: `crates/axeyum-solver/src/config_registry.rs` (113 entries,
19 `GOVERNED_FILES`). Extraction is mechanical, from the registry's own text.

### Headline

| | count |
|---|---:|
| registry entries | 113 |
| in the admission class (`RefuseUnknown` / `DeclineRoute` / silent `Relax`) | **70** |
| …of those, carrying a measurement **date** | **18** |
| …of those, **undated** — unclassifiable, not "valid" | **52** |
| admission-class entries that cross with **no signal to the caller** | 12 |

**52 of 70 cannot be classified stale-or-valid at all**, because there is no
date to compare anything against. That is the honest headline, and it is not the
same as "52 are fine". A staleness checker can only speak about the 18.

### The verdicts

`STALE` requires positive evidence that the cited basis is gone. `VALID`
requires a date plus a `rests_on` dependency plus nothing having changed since.
`UNDATED` is neither.

| Verdict | Entries |
|---|---|
| **STALE — basis retired** | `dpll_lia::MAX_PRE_SAT_ARITH_ATOMS`, `dpll_lia::MAX_PRE_SAT_CNF_VARS`, `dpll_lia::MAX_MODERATE_PRE_SAT_ARITH_ATOMS`, `dpll_lia::MAX_MODERATE_PRE_SAT_CNF_VARS`, `dpll_lia::MAX_DYNAMIC_LARGE_CORE_LITERALS` |
| **VALID — dated, dependencies unchanged** | the 18 dated entries, all of which `scripts/check-config-registry-staleness.py` currently passes (ADR-0360 ×3, ADR-0364 ×2, ADR-0543 ×2, ADR-1730, ADR-1751 ×3, ADR-1752 ×9, plus `euf::DECLARED_SORT_CEGAR_PAIRS_TERMINAL_RUNG` and `memory_budget::ENCODING_BYTES_PER_CLAUSE`) — **but see the caveat below** |
| **UNDATED — cannot be classified** | the remaining 52 admission-class entries |

The five STALE entries are exactly the entries whose doc comment names
`BatSat`. They were found by scanning every registered constant's
definition-site doc comment for identifiers, then asking whether each identifier
still names a live part of the default build. Nothing else in the registry cites
a retired mechanism by name.

**Caveat on VALID.** A `VALID` here means *the check that exists cannot fault
it*. The existing staleness check compares a date against `git log -G<symbol>`
over the entry's declared `rests_on`. It cannot see a basis that was never
written down as a dependency, and it cannot see a basis that is prose ("BatSat's
allocator") rather than a symbol. Both instances 1 and 2 above were invisible to
it for that reason — instance 2 only became visible once ADR-1752 wrote the
dependency down. This is the gap the new check closes.

### The 12 that cross with no signal

These are the ones where "which route declined, and why" cannot be recovered
from any trace, because the crossing produces no branch a caller can observe:

| Entry | `on_exceed` | What is supposed to make it safe |
|---|---|---|
| `dl_online::MAX_DL_ATOMS` | DeclineRoute | routed to another engine — but the size refusal and the structural "not difference-shaped" decline share one `None` return, so no trace can tell them apart (already recorded by ADR-1762) |
| `dpll_lia::MAX_BELLMAN_FORD_DIFF_EDGES` | DeclineRoute | search continues without that core |
| `dpll_lia::MAX_TWO_EDGE_DIFF_EDGES` | DeclineRoute | falls through to the Bellman-Ford gate |
| `dpll_lia::MAX_INITIAL_BOUND_IMPLICATION_ATOMS` | Relax | the skipped pass only adds valid lemmas |
| `auto::MAX_COERCION_LINK` | Relax | `sat` accepted only after model replay |
| `nia_linearize::MAX_CONGRUENCE_GROUPS` | Relax | `check_with_nia` replays every `sat` |
| `nia_linearize::MAX_MCCORMICK_PRODUCTS`, `MAX_SMALL_DOMAIN_PRODUCTS`, `MAX_SMALL_DOMAIN_WIDTH`, `MAX_TANGENT_ABS_VALUE`, `MCCORMICK_MAX_ABS_BOUND` | Relax | an unemitted valid lemma cannot make a verdict wrong |
| `quantifiers::CHAIN_INSTANCE_CAP` | Relax | an uninstantiated chain can only leave the query undecided |

Every one of these has a `guarded_by` reason that is plausible for
**soundness**. None of them has anything that makes the crossing
**attributable**: a run that lost a decision here cannot say so. That is what
`note_crossed` (below) is for.

## The registry is not the haystack: 75 more, outside `GOVERNED_FILES`

The registry claims 19 files. A separate read-only sweep of every other
non-test source file in `axeyum-solver`, `axeyum-rewrite`, `axeyum-cnf`,
`axeyum-smtlib`, `axeyum-bv` and `axeyum-aig` — looking for the *step* (a
numeric comparison guarding a route), not for a naming convention — found **75
further admission limits**: 19 that change mode with no signal, 20 that return a
first-class `Unknown`, 29 that decline a route, 7 that hard-error out of one.

**Not one of the 75 names a date or a commit.** Two name an ADR (`ADR-0029`
twice); one names a `REPORT.md` line. Dated justifications exist essentially
only inside the 19 governed files — which means the enumeration above, dispiriting
as its 52-undated figure is, describes the **best**-documented corner of the
surface.

Four structural findings from that sweep, each of a kind the registry is blind
to by construction:

- **Bare integer literals in guards.** `strings.rs`'s `rmax > 16` (three sites,
  hard `Err`), `smtlib/parse.rs`'s `conjuncts.len() > 2_048` and
  `assertions.len() > 2_048`, `depth > 256`, `depth > 16`, `maxsat.rs`'s
  `bits > 127`, and `qinst_egraph.rs`'s `attempts_since_clock_check >= 8192`
  (which sets how often a shared deadline is polled at all). No registry keyed
  on `const` names can see any of these, and no rename or grep will find them.
- **Undocumented wall-clock budgets outside any category the registry has.**
  `array_bv_abs::BV_ABSTRACTION_TIMEOUT` (1 s) and
  `abv::SCALAR_LOCAL_SEARCH_PROBE_MS` (100 ms) each end a search inconclusively,
  and neither has a doc comment.
- **Divergent twins.** `MAX_SPLIT_DEPTH = 64` appears verbatim, with
  byte-identical doc comments, in `uflia_online.rs` and `uflra_online.rs`;
  `MAX_SPLIT_PAIRS = 64` likewise in `combined_theory.rs` and
  `combined_theory_lia.rs`, whose doc claims it "mirrors the cold core's
  `MAX_SPLIT_DEPTH`". Four copies of one number, none linked to another. This is
  the same defect ADR-1751 fixed for `nra`/`lra_theory`, unfixed in three more
  places.
- **One constant, two contracts, one file.** `dpll_t::MAX_CERTIFIABLE_BOOLS`
  yields `Unknown(Incomplete)` at line 512 and `Err(Unsupported)` at line 576.
  The registry governs only the `dpll_lia.rs` twin of that name.

The largest wholly undocumented cluster is `incremental.rs`:
`MAX_WARM_STRUCTURAL_ARRAY_NODES`, `…_DEPTH`, `MAX_WARM_ARRAY_UF_APPS_PER_ROOT`,
`MAX_REPLAY_SHARED_MEMO_ENTRIES` and `MAX_WARM_STRUCTURAL_REFINEMENT_ROUNDS` —
five caps, no doc comments, one of them returning `Unknown(ResourceLimit)`.

None of the 75 was fixed or registered by this lane. Registering them is real
per-value work (each needs `protects`/`on_exceed`/`signal` decided from the code,
not from its comment), and a registry entry written carelessly is worse than an
honest absence — which is exactly why `GOVERNED_FILES` is a claim and not a
default.

## Ranking by losses actually carried

Only the first row is a **measurement**; the rest are reasoned and are marked as
such. The measured population is the 2026-09-05 parity loss census
(`bench-results/parity-losses-20260905/`), whose per-file populations, wall
times and verdicts are good — its `class` column is **not**, and QF_LIA is
explicitly on that census's *not-confirmed* list, so the row below was
re-derived rather than quoted.

| Rank | Limit | Losses | Basis of the number |
|---:|---|---:|---|
| 1 | `euf` Ackermann pairs `> 64` | 52 of 58 QF_UFLIA | measured by the lane that owns it; **not re-measured here** |
| 2 | `dpll_lia` pre-SAT rectangle | 15 of 27 QF_LIA | census `class` column, **re-derived through the front door by this lane** — see the measurement section |
| 3 | `dl_online::MAX_DL_ATOMS` and the QF_IDL/QF_RDL admission declines | 46 of 54 QF_IDL, 24 of 47 QF_RDL | census `class`, **reasoned**: those divisions were confirmed by the slices that acted on them, but not attributed to a single constant |
| 4 | the 52 undated admission-class entries | unknown | **cannot be ranked**: no route-attribution data exists for a crossing that emits no signal |

Rank 4 is the reason `note_crossed` matters more than any single constant. Until
a crossing is attributable, the population riding on it is unmeasurable by
construction, and "a stale limit nobody hits" is indistinguishable from "a stale
limit carrying fifty files".

## Making a decline attributable: `note_crossed`

The registry already had `note_consulted(key)` — "this bound was looked at". It
does not say the bound *bit*, and it carries no numbers, so a run's own output
cannot answer "which route declined, on what condition, with what budget
remaining". For the 12 silent entries above, that question is unanswerable by
construction, and rank 4 of the table below is a direct consequence: a stale
bound nobody hits is indistinguishable from a stale bound carrying fifty files.

`note_crossed(key, observed, bound)` records the crossing with its numbers, in
the entry's own `unit`, never normalized — two gates metering one resource in
different units is a defect this registry exists to make visible, not to
launder. Same discipline as every other recorder here: opt-in behind
`ConfigTraceGuard`, clock-free, and with no guard constructed it is one
thread-local `Cell<bool>` read and a return. Only the **first** crossing of a
key is kept, so a bound crossed in a loop cannot make the trace line grow
without limit, and the numbers reported are the ones from the crossing that
first changed the route. `config_trace_line()` emits
`crossed=N <key>=<observed>/<bound> …` after the `consulted=` field, so a
`--trace` run distinguishes "consulted" from "decided".

It is wired at the `dpll_lia` rectangle first, where it does something the
existing `UnknownReason` cannot: the reason is only produced on the path that
*returns* it, so a query that crosses the rectangle and is then rescued by
`oversized_admission_probe` previously left **no record at all**. That is the
population whose size nobody could state.

Two tests guard it, and the second is the one that matters:
`consulted_keys_are_registered` now scans call sites of **both** recorders
against the registry (a crossing under an unregistered key is a trace line
nobody can resolve back to a bound), and
`crossing_the_pre_sat_rectangle_is_recorded_with_its_numbers` drives the real
decision function — not `note_crossed` directly — so it dies if the wiring is
removed and not only if the mechanism breaks. It also asserts the two negatives:
an admitted skeleton records nothing, and a crossing outside a guard records
nothing.

## The gate: a justification whose basis cannot expire unnoticed

Two questions, deliberately separated, because the existing checker could only
ask the first:

| | question | needs | catches |
|---|---|---|---|
| `rests_on` (existing) | did the code this was measured against **change**? | history + a date | `MAX_ONLINE_LRA_ATOMS` |
| `basis` (new) | does the thing this reasoning **names** still exist? | the tree as it is now | `MAX_PRE_SAT_ARITH_ATOMS` |

`Basis` is a **required** argument of `dated(...)`, not an optional field, for
the reason the registry exists at all: a field that can be omitted is omitted.
All 24 dated entries carry one; `dated_justifications_declare_a_basis` fails if
any does not, and fails equally if an *undated* entry carries one (a basis with
no measurement to support has nothing to be the basis of).

Four variants, each checkable with no host-specific data:

- `LiveSymbol { ident, in_path }` — an identifier the reasoning names must still
  occur at the site it points at. `in_path` is a specific file, never the
  workspace: *"BatSat exists somewhere in the tree"* stays true forever behind an
  optional dev-dependency, while *"BatSat is what
  `crates/axeyum-cnf/src/lib.rs`'s warm solver uses"* is the claim that became
  false.
- `CommitSubject { sha, subject_contains }` — a cited commit must still exist and
  still say what it was cited for saying.
- `AdrLive(id)` — the ADR a bound implements must not be superseded, rejected or
  withdrawn. A bound whose deciding ADR was overturned is not automatically
  wrong, but it is automatically unjustified.
- `DocPath(p)` — the write-up must still exist.

`scripts/check-admission-limit-basis.py` resolves them: **exit 1** when any is
gone, **exit 2** on a self-check failure, exit 0 otherwise. Two self-checks, both
modelled on the sibling script's own history of near-misses: the entry count must
match the raw `ConfigEntry {` literal count, and the number of basis
declarations *attributed to an entry* must match the number *written in the
file* — a basis written down and checked by nothing is precisely a gate that
cannot fire.

### The control, and what it demonstrated

`scripts/tests/test-admission-limit-basis-control.sh` runs seven steps against
throwaway copies. Two of them are worth stating on their own:

**Step 2 reproduces the real failure, and refines it.** The first draft of the
control asserted that a basis naming the string `batsat` inside
`crates/axeyum-cnf/src/lib.rs` would fire. **It did not** — that file still says
"batsat" in prose about the retired adapter and in a
`#[cfg(feature = "batsat-reference")]` re-export. The claim that actually became
false is narrower: until ADR-1703, `IncrementalSat` was
`{ solver: IncrementalBatSat, .. }`, and **`IncrementalBatSat` occurs nowhere in
`crates/` today**. So the control names that type, and the lesson is in the
control's own comment: a basis must name the thing whose disappearance *is* the
claim becoming false, not a word that happens to appear near it.

**Step 6 is the deletion test.** Each of the four `check_basis` branches is
removed in turn from a scratch copy of the checker, and **exactly one** of the
four registry mutants must stop being caught — the diagonal, not merely "some
test went red". Building it found a real defect in the checker: `REPO` was
derived from `Path(__file__).parent.parent`, so a scratch copy resolved every
path and every commit against the scratch directory. A defanged checker then
reported **nine** findings instead of the one its mutation should have removed —
not a weaker control, a control measuring the wrong thing while looking busy.
`--repo` now makes the subject explicit.

### `--audit`, and its honest negative result

The script also has a discovery mode: read every registered constant's
definition-site doc comment, extract every identifier-shaped token, and report
any that occurs nowhere in `crates/`. Run today it examined **95 of 113** doc
comments and found **nothing dangling**.

That negative is the point. `batsat` *does* still occur in `crates/`, so this
coarse net would never have caught the founding case. It rules out the easy
half of the problem — a name that is simply gone — and leaves the hard half,
which is why the declared `Basis` has to be precise and why it is required
rather than inferred.

## What was not done

- **The 52 undated entries were not dated.** Dating a value means re-taking its
  measurement, which is a per-value piece of work, not a sweep. They are
  enumerated and marked `UNDATED`, which is the honest state.
- **Rank 1 and rank 3 were not re-measured.** Rank 1 belongs to another lane;
  rank 3 has no single constant to attribute to.
- **Coverage is still the registry's 19 governed files.** A limit outside them
  is outside this enumeration too.
