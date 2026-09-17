# ADR-2144: the canonical constraint cache is a library feature of the warm engine

Status: proposed
Index-summary: Glaurung's explorer re-checks assertion SETS that repeat — 62 % of 12,902 checks are exact canonical reuse per four-driver pass (ADR-0304's v2 analyzer) — and today the cache that exploits it lives in Glaurung's adapter, so no other consumer of `IncrementalBvSolver` gets it and the engine's own ordered replay-checked cache (ADR-0190) misses on a reordered, re-scoped or duplicated assertion. `CanonicalConstraintCache` now lives in the engine: keyed by the sorted, duplicate-elided set of live assertion identities (ADR-0303's key — inside one hash-consed arena a `TermId` IS a structural identity, so the key needs no hashing), it serves an exact `sat` only after the cached model REPLAYS against the live set, an exact `unsat` directly, `unsat` for any live SUPERSET of a cached unsat set, and a cached model of a SUBSET when it replays; `unknown` is never cached; deterministic 4,096-entry LRU (ADR-0303's bounds). Two invariants are pinned with mutation controls that each kill exactly one test: a stale model is a counted rejection and a fresh solve, never a wrong `sat`; and a subset query is never answered `unsat` (the soundness-negative dies alone when the subset test is deleted). Measured: replaying the DptfDevGen owner-1 session (1,206 checks) the cache answers **589 (48.8 %)** — 418 exact `sat`, 171 model reuse — with the verdict digest byte-identical on and off, 0 disagreements, 0 replay failures, and wall 1.19–1.31 s → 0.77–0.83 s; on the `QF_BV` pinned list (200 one-shot files) it changes no verdict and costs nothing, which is the regression control. Ships OFF behind `SolverConfig::canonical_constraint_cache` / `AXEYUM_CANONICAL_CACHE`; the counters ride `stats()` and the Python `Incremental`. Glaurung's next step is to replace its text-keyed process cache with the engine's (item 5 on its list). No default moves.
Index-status: proposed
Date: 2026-09-17

## Context

Item 8 of the [2026-09-16 improvement list](../../plan/improvement-list-2026-09-16.md):
make ADR-0303's canonical constraint cache a library feature of the
incremental engine instead of each consumer's adapter. The sizing is in
[`2026-09-17-constraint-cache-sizing.md`](../11-design-review/2026-09-17-constraint-cache-sizing.md);
what it found:

- The engine already had an opt-in cache, ADR-0190's `ReplayCheckedSatCache`,
  keyed on the ORDERED assertion vector plus every frame's cumulative end
  plus the ordered assumption vector, storing `sat` models only. An
  assertion re-asserted in a different order, in a different frame
  partition, twice, or moved between the stack and the assumptions is a
  miss, and an `unsat` is never reused.
- Glaurung's cache (`constraint_cache.rs`) is process-wide and keys on the
  SHA-256 of each assertion's SMT text, sorted and deduplicated — ADR-0303's
  identity, after ADR-0304 rejected ordered-text keying. Its warm route
  drives `IncrementalSolver::check_assuming` on a path-owned
  `IncrementalBvSolver` with the path prefix on the scope stack and the
  branch condition as a one-shot assumption.
- ADR-0304's v2 opportunity artifact: 8,001 of 12,902 checks (62.01 %) are
  exact canonical reuse per four-driver pass; implication-only reuse (both
  ADR-0303 directions together) adds 562 (4.36 %). On the extracted
  DptfDevGen owner-1 stream, counted from the ops file alone, 418 of 1,206
  checks (34.7 %) are exact reuse within one owner session, all `sat`, and
  neither implication direction adds one.

## Decision

`IncrementalBvSolver` owns a `CanonicalConstraintCache`
(`crates/axeyum-solver/src/incremental.rs`), enabled by
`SolverConfig::canonical_constraint_cache` — `DEFAULT_CANONICAL_CACHE = false`,
the one-binary lever `AXEYUM_CANONICAL_CACHE=on|off` read once per process,
registered in `config_registry.rs` — or explicitly by
`enable_canonical_constraint_cache(policy)`. Both `check` and
`check_assuming` (and so the `IncrementalSolver` trait) go through it; the
core-returning and memory-simplifying routes do not.

**Key.** The sorted, duplicate-elided `Vec<TermId>` of every open frame's
assertions plus the check's assumptions. Frame boundaries and order are not
part of it (conjunction is commutative and idempotent), and because the arena
hash-conses, a `TermId` is a structural identity inside one solver — the
same assertion rebuilt after a pop keys the same. Deferred-theory (array/UF)
assertions or assumptions bypass the cache entirely, so the warm path's
refusal of them does not depend on it.

**What a hit returns.**

| cached entry | live set `Q` vs cached `C` | answer | guard |
| --- | --- | --- | --- |
| `sat(C, m)` | `Q == C` | `Sat(m)` | `m` replays against every live original and assumption |
| `sat(C, m)` | `C ⊆ Q` | `Sat(m)` | the same replay (model reuse, at most one candidate: the entry under `Q`'s largest member) |
| `unsat(C)` | `Q == C` | `Unsat` | — |
| `unsat(C)` | `C ⊆ Q` | `Unsat` | the subset test (monotonicity) |

`unknown` is never stored. The `Q ⊆ C` SAT direction of ADR-0303 is not
implemented: the v2 artifact bounds all implication reuse at 4.4 % and the
replayed stream shows none.

**The two invariants**, each pinned by a test and a mutation control
(`scripts/tests/mutation_controls.py canonical-constraint-cache-2144`):

1. A cached `sat` is served only after its model replays against the live
   set. A replay that is `false`, non-Boolean or fails to evaluate is a
   *rejection* (`cache_replay_rejections`): an exact entry that fails is
   dropped (its set has not changed, so the model was never one), a reuse
   candidate is kept (it is still a model of its own set), and the check is
   solved fresh. Never a wrong `sat`, never an error.
   `a_cached_model_that_no_longer_replays_is_rejected_never_served` extends
   the path with an assertion the cached model violates;
   `corrupted_canonical_exact_entry_is_rejected_and_resolved_fresh` plants a
   false model under the exact key.
2. A cached `unsat` is served only for a superset of the cached set.
   `unsat_is_never_served_for_a_subset` caches `{a, c}` unsat and asks
   `{b, c}` (satisfiable, and `c` is the largest member of both, so a lookup
   without the subset test finds the entry); deleting the subset test kills
   exactly this test.

**Structure.** Slots in a free-listed `Vec`, an exact `HashMap` over keys,
and a `by_max` index from each entry's largest `TermId` to its slots
(`C ⊆ Q` implies `max(C) ∈ Q`, so a subset probe walks `|Q|` buckets and runs
a sorted-merge subset test per candidate). Deterministic LRU: least logical
stamp, then lowest slot, is evicted; bounds are ADR-0303's 4,096 entries and
262,144 model values plus a bit bound. A superset hit and a model-reuse hit
each insert the live set as its own exact entry, so its repeat is an exact
hit. `stats()` carries `cache_hits`, `cache_misses`,
`cache_replay_rejections`, `cache_superset_hits`;
`canonical_constraint_cache_stats()` the per-class detail. The Python
`Config(canonical_constraint_cache=)`, `Incremental.enable_/disable_canonical_constraint_cache`,
`canonical_constraint_cache_enabled`, `canonical_constraint_cache_stats()`
and the four `IncrementalStats` getters ship with regenerated stubs.

## Evidence

**The replayed session.** `examples/warm_session_age.rs --replay
/data0/axeyum/scratch/ax-cache/dptf-r1-owner1 [--canonical-cache]` (the
DptfDevGen r1 owner-1 stream AX-WARM extracted for ADR-2142; 1,206 checks,
599 distinct assertions), release, cores 0–7 on s4 at load ~7, arms
interleaved, three rounds:

| arm | verdicts | disagreements / replay failures | verdict digest | wall (3 rounds) |
| --- | --- | ---: | --- | --- |
| off | sat 725 / unsat 481 / unknown 0 | 0 / 0 | `9c7712cf37340c0e` | 1.305, 1.246, 1.194 s |
| on | sat 725 / unsat 481 / unknown 0 | 0 / 0 | `9c7712cf37340c0e` | 0.832, 0.770, 0.771 s |

Cache on: hits **589 of 1,206 (48.8 %)** — exact `sat` 418 (exactly the
ops-file count), exact `unsat` 0, superset 0, model reuse 171 — misses 617,
replay rejections 614, insertions 788, evictions 0. The verdict+model digest
moves (`9fe6d1e14afe9c19` → `19ea21d943068024`) because a served model is the
cached one, which is the point; the verdict digest does not. With four reuse
candidates per miss instead of one, reuse hits were 174 for 2,432 failed
replays, so the bound is one. Session-age growth (ADR-2142's ratio) is
unchanged at 28–32× either way: the hits are the cheap checks.

**The `QF_BV` pinned-list A/B** (`bench-results/canonical-cache-20260917/`):
`bench-results/parity-lists/QF_BV.txt` (200 files), s7, one binary
(`smtcomp_cli` at this lane's tree, hash in `half*.log`), arm A the variable
unset and arm B `AXEYUM_CANONICAL_CACHE=on`, interleaved per file and
alternating in order, 24 s / 8 GiB, two halves of 100 files concurrently on
core pairs `1,9` and `3,11`, `$EPOCHREALTIME` with the 200 ms sleep
self-check (`ab-env.sh`, `summarize.py`):

| measure | A = cache off | B = `AXEYUM_CANONICAL_CACHE=on` |
| --- | ---: | ---: |
| decided (of 200) | 187 | 187 |
| sat / unsat | 58 / 129 | 58 / 129 |
| PAR-2 (ms, 24 s) | 3852 | 3851 |
| wall, 187 both-decided files (ms) | 146 317 | 146 201 |
| other arm >10 % + 50 ms slower | B slower on 1 | A slower on 1 |

Gains 0, losses 0, **flips 0, `:status` disagreements 0**, nonzero exit
rows 0, timing-unit failures 0 (binary `840e29c9…`, clock self-check 205 /
203 ms). The one-shot front door never reaches the warm engine on these
files, so the lever is inert here by construction; the table is the evidence
that it is inert, not a speed claim.

**The corpus identity** (`cache_on_and_off_agree_on_every_flat_qf_bv_fixture`):
every committed flat `QF_BV` fixture (43 compared, 9 `sat`, 10 skipped by
the parser or the warm path) is driven assert-all / check / push / check /
pop / check with the cache off and on; every verdict agrees at every step,
the fresh first models are identical, every served model replays, and the on
arm records 86 hits (two per fixture).

## Alternatives

- **Extend ADR-0190's cache with a set key.** Rejected: its identity
  (ordered vector plus frame ends) is what ADR-0190 deliberately chose for an
  exact-query cache, and its false-replay rule is a soundness error, which is
  right for an exact key and wrong for model reuse. The two coexist; the
  canonical cache sits in front.
- **A process-wide cache keyed by structural hash, as Glaurung's is.**
  Deferred: `axeyum-ir` has no structural term hash today, a cross-solver
  model must be keyed by symbol name rather than `SymbolId`, and a per-solver
  cache needs neither while giving every retained-session consumer the
  feature. The cross-owner share of ADR-0304's 62 % is what this slice
  forgoes.
- **ADR-0303's `Q ⊆ C` SAT direction.** Not implemented; bounded at 4.4 %
  by the v2 artifact and zero on the replayed stream.
- **Shipping ON.** Not yet: a served `sat` returns the cached model rather
  than the model a fresh solve would, which is a visible change for every
  warm consumer, and the pinned-list A/B is a regression control, not a
  measurement of the consumer that wants it. Glaurung turns it on and
  measures under ADR-0303's protocol.

## Consequences

- Every consumer of `IncrementalBvSolver` — Glaurung's warm path, `bmc`,
  `dpll_t`, the warm array route — can turn the cache on per solver or per
  process; nothing changes until they do.
- **What Glaurung would do** (item 5 on its list): keep its process-wide
  cache only for the cross-path share, and for the path-owned warm solver
  set `SolverConfig::canonical_constraint_cache` (or call
  `enable_canonical_constraint_cache`) and read `stats().cache_hits` beside
  `replay_sat_cache_stats()`; ADR-0303's mode matrix then runs with the
  library cache as the `exact` and `structural` arms.
- A cross-solver variant needs a structural term hash in `axeyum-ir` and a
  name-keyed model; that is the next slice if Glaurung's cross-owner share
  measures as worth it.
