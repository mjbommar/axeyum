# Sizing: the canonical constraint cache as a library feature (item 8, 2026-09-16 list)

Lane AX-CACHE, 2026-09-17. Read before the code; the decision is ADR-2144.

## What exists

**In the engine** (`crates/axeyum-solver/src/incremental.rs`). `IncrementalBvSolver`
is bound to one `TermArena`; its `frames: Vec<Frame>` each hold `assertions`
(the ORIGINAL terms, which is what `replay` evaluates) and a CNF selector.
`check` / `check_assuming` both go through `check_with_replay_cache`, then
`solve_with_extra` → `solve_with_encoded_extra` (encode the one-shot
assumptions under fresh selectors, solve the retained CNF under the frame
selectors, lift, replay). `check_assuming_core`, the `*_simplifying_memory`
and `*_with_memory` routes bypass the cache today and keep doing so.

The existing `ReplayCheckedSatCache` (ADR-0189/0190, opt-in via
`enable_replay_checked_sat_cache`):

| | existing replay-checked cache |
|---|---|
| key | the ORDERED assertion vector + every frame's cumulative end + the ordered assumption vector; compared as vectors, linear scan |
| stores | `sat` models only (scalar Bool/BV); `unsat` and `unknown` are counted (`declined_*`) and never stored |
| hit | exact vector identity; the model is replayed against every live original and served only if replay is `true` |
| replay `false` | the entry is evicted and the check returns a `SolverError` (fail closed, ADR-0190) |
| bounds | entries, total model values, total model bits; deterministic LRU |
| stats | `replay_checked_sat_cache_stats()` — not in `stats()` |

So today an assertion ORDER change, a different frame partition of the same
assertions, a duplicate assertion, or an assumption moved onto the stack is a
miss, and an `unsat` is never reused.

**In the consumer** (Glaurung, `src/symbolic/solver/constraint_cache.rs`,
read-only). The brief calls it "keyed on ordered query text"; the code
is already one step further: `query_key` is the SHA-256 of each assertion's
SMT text (`pipe::assertion_line`), sorted and deduplicated — the ADR-0303
identity — because ADR-0304 rejected the ordered-text keying. It is a
process-wide thread-local (cross-path, cross-arena), with an exact `BTreeMap`,
an inverted index for SAT-superset (`Q ⊆ C`) and a trie for UNSAT-subset
(`C ⊆ Q`), ADR-0303's bounds (4,096 entries / 524,288 assertion refs /
262,144 model values / 256 per entry), and a strict evaluator for model
replay. It wants back: the verdict; for `sat`, the model by symbol id
(consumed by concretization); it does not consume unsat cores from the cache.
Glaurung's warm route (`warm_paths.rs::transition_and_check`) drives
`IncrementalSolver::check_assuming` on a path-owned `IncrementalBvSolver`,
with the path prefix on the scope stack and the branch condition as a one-shot
assumption. That is exactly the surface a library cache sits under.

## What the canonical key needs

A stable identity per assertion **across pushes**. Inside one arena a
`TermId` is already that: the arena hash-conses, so structurally equal terms
built at different times intern to the same id, and the id never moves. The
key is therefore

    sorted, duplicate-elided Vec<TermId> of (every live frame's assertions ++ the check's assumptions)

Frame boundaries are NOT part of the key (they do not change the conjunction);
neither is order (conjunction is commutative) nor multiplicity (idempotent).
Deferred-theory (array/UF) assertions are outside the warm path and the cache
bypasses whenever any is active, as the existing cache does.

Across arenas — what Glaurung's process-wide cache does — the id is not
stable and a structural hash of the term (which `axeyum-ir` does not currently
expose; Glaurung hashes SMT text) is required. That is a second slice: a
per-solver cache lands first because it needs no new IR surface and every
consumer with a retained solver gets it for free; the cross-solver variant
needs the hash plus a symbol-name-keyed model (see "What Glaurung would do" in
ADR-2144).

## What a hit returns

| entry | live set `Q` vs cached set `C` | answer | guard |
|---|---|---|---|
| `sat(C, model)` | `Q == C` (exact) | `Sat(model)` | model replays against every live original AND assumption |
| `sat(C, model)` | `C ⊆ Q` (the explorer extended the path) | `Sat(model)` | same replay — this is model REUSE, sound only by replay |
| `unsat(C)` | `Q == C` | `Unsat` | none needed |
| `unsat(C)` | `C ⊆ Q` | `Unsat` | the subset test itself (monotonicity) |

`unknown` is never stored. The `Q ⊆ C` SAT direction of ADR-0303 (a cached
model of a LARGER set answers a smaller query) is not implemented in this
slice: on the v2 opportunity artifact all implication-only reuse together is
562 of 12,902 checks (4.4 %), and on the extracted DptfDevGen owner-1 stream
(below) it is zero.

## The soundness rules the tests pin

1. **A cached `sat` is served with its model only after the model REPLAYS
   against the current live assertion set** (every frame's originals plus
   this check's assumptions). A replay that is `false` or non-Boolean is a
   *rejection*: the entry is dropped, `cache_replay_rejections` counts it,
   and the check is solved fresh — never a wrong `sat`, never an error from
   a stale reuse (that is where it differs from ADR-0190's exact cache, whose
   false replay is a soundness error because an exact key cannot legitimately
   stop replaying; a model-reuse candidate can).
2. **A cached `unsat` is served only for a live set that is a SUPERSET of the
   cached set.** A subset query is never answered `unsat` from the cache. The
   soundness-negative test asserts a sat subset after an unsat superset and
   must get `sat`; deleting the subset test in the lookup must kill exactly
   that test (mutation control).

Both are invariants of the lookup, not of the consumer: a consumer cannot
get a wrong verdict by calling in any order.

## Expected reuse (measured on the stream this lane replays)

`/data0/axeyum/scratch/ax-cache/dptf-r1-owner1.{smt2,ops}` (copied from
AX-WARM's scratchpad; DptfDevGen r1 owner 1, 1,206 checks, 599 distinct
assertions, verdicts sat 725 / unsat 481). Counting canonical sets over the
ops file alone:

    checks=1206 exact=418 (sat 418, unsat 0) distinct=788 unsat_subset_extra=0 sat_superset_extra=0

So 34.7 % exact canonical reuse within ONE owner session, all of it `sat`;
the per-process 42 % (255/603) that ADR-0304 reports for this driver
includes cross-owner reuse a per-solver cache cannot see. Every exact hit
here needs a replay of the cached model, so the hit's cost is the evaluator
over the live set — the same replay a fresh `sat` already pays.

## Cost and bounds

Storage: one `Vec<TermId>` per entry plus a scalar model. ADR-0303's bounds
carried over: 4,096 entries, 262,144 model values, and a bit bound in place of
the per-entry value cap. Eviction: deterministic LRU by logical check stamp,
ties by lowest entry id (the existing cache's rule). Lookup: exact via a
`HashMap<Vec<TermId>, entry>`; the `C ⊆ Q` probes via an index from each
entry's LARGEST term id to the entries with that maximum (`C ⊆ Q` implies
`max(C) ∈ Q`), so a probe walks `|Q|` buckets and runs a sorted-merge subset
test on each candidate rather than scanning every entry. The lever ships OFF;
`stats()` gains `cache_hits`, `cache_misses`, `cache_replay_rejections`,
`cache_superset_hits` so the counters ride the snapshot every consumer already
reads.
