# ADR-2145: the warm core keeps the surviving scopes' trail across `pop` and `check`

Status: accepted
Index-summary: ADR-2142 removed the quadratic term from the retained `IncrementalBvSolver`'s per-check cost; what remained was linear in the retained database because the warm core re-derived the whole assignment on every solve by design. Sized at head on the replayed DptfDevGen session (1,206 checks): `propagate` 40.6 %, the order-heap drain after that propagation 29.3 %, the `assignment_is_model` self-check 8.3 %, `reset_search_state` 2.8 % — re-derivation is ~76 % of the session, and the per-check trail grows to 40k entries over a 63k-variable / 148k-clause database. The change: the core backtracks to the longest common prefix of the previous and next assumption sequences (CaDiCaL `ilb=1`) instead of unwinding, registers clauses added between solves against the live assignment through a re-init list (z3's `m_clauses_to_reinit`: unit → enqueue at the current level, re-examine when that level unwinds), and takes the shipped reset when less than half the trail would survive. The invariant kept is that the assignment at every surviving level equals a fresh propagation of the surviving clauses, and every retained learned clause is entailed by the database alone (1-UIP never resolves an assumption away, so the brief's "drop learned clauses derived under assumptions" rule has no code to delete; the equivalent guard is the surviving-scope IDENTITY check, killed by two mutation suites). Measured: the replayed session 1.21 → 0.45 s at three interleaved rounds per arm with the same verdict+model digest, last-band p50 1.34 → 0.07 ms and p90 5.36 → 2.08 ms, propagations per check 20,976 → 2,107; July's BatSat engine was 0.87 s on the same stream. Pinned lists (200 `QF_BV` + 200 `QF_ABV`, s7, 24 s, interleaved): 0 verdict movers, 0 flips, 0 `:status` disagreements; of the time movers rerun 3×/arm, `QF_ABV` has 9 stably faster and 1 stably slower. A new session fuzz for the incremental path (push/assert/check/pop against a fresh one-shot, a replay, and z3 driven through the same stream) found the first cut's wrong-`unsat` before any gate did and is registered in the pre-push hook. `DEFAULT_WARM_KEEP_TRAIL` moves to `true`; `AXEYUM_WARM_KEEP_TRAIL=off` is the previous schedule.
Index-status: accepted
Date: 2026-09-17

## Context

[ADR-2142](adr-2142-the-warm-session-slowed-with-age-because-the-target-phase-snapshot-re-walked-the-trail-per-decision.md)
found and removed the quadratic term in a retained `IncrementalBvSolver`'s
per-check cost (the target-phase snapshot re-walking the trail at every
decision). Its own closing measurement said what was left: the last band of
the replayed DptfDevGen session was still 30–37× its first, the July BatSat
engine on the same stream was 16–18×, and the profile after the fix was
`propagate` 63 %, `heap_percolate_down` 13 %, the `assignment_is_model`
self-check 9 % — "the cost of re-deriving the whole retained assignment every
solve, which `proof_sat/incremental.rs` chooses on purpose". Glaurung's re-pin
(`solver-035`) measured the same shape in production: warm p90 per check
growing 0.09 → 6.1 ms across a 1,229-check session.

The reset was a design choice with a stated reason: "Between solves the
solver holds no assignment at all … That costs one level-zero propagation per
solve and buys the property that makes `add_clause` simple: a clause is
always registered into an unassigned solver". This ADR pays for that property
another way.

## The sizing at head

`e7d132705`, the replayed DptfDevGen r1 owner 1 session (`examples/
warm_session_age.rs --replay`, 1,206 checks, cores 0–7), `perf record`:

| frame | share |
|---|---:|
| `Cdcl::propagate` | 40.6 % |
| `Cdcl::heap_percolate_down` (the order heap drained by `pick_branch` after a from-scratch propagation assigns every retained variable) | 29.3 % |
| `IncrementalSat::solve_inner` (`assignment_is_model` over all 148k clauses) | 8.3 % |
| `Cdcl::run` / `search_loop` (assumption installation) | 3.8 % |
| `Cdcl::reset_search_state` | 2.8 % |
| `IncrementalCnf::assert_root` | 2.0 % |

Assignment re-derivation — propagate, the heap drain it causes, the reset and
the re-installation of assumptions — is about 76 % of the session; everything
else about 24 %. The retained database and the trail, by band (the new
`clauses` / `vars` / `trail` columns of the reproducer):

| check | clauses | variables | trail after the check |
|---:|---:|---:|---:|
| 50 | 10,745 | 5,427 | 1,495 |
| 500 | 72,506 | 31,945 | 16,497 |
| 1,000 | 130,420 | 56,239 | 29,730 |
| 1,206 | 147,661 | 63,154 | 39,614 |

Baseline p90 per band at head: 0.31 ms → 8.5 ms (load 11), 0.19 → 5.3 ms
(load 5); total 1.97 s / 1.21 s.

## What each side does today, at `file:line`

**Ours.** `IncrementalBvSolver` (`crates/axeyum-solver/src/incremental.rs`)
compiles scopes to selector variables: `push` allocates a fresh selector
(`:1821`), every assertion in that frame is encoded guarded by it
(`assert_root` in `axeyum-cnf/src/lib.rs:2048` emits `¬s ∨ root`), `pop`
drops the frame (`:1841`) and nothing at the SAT level moves, and `check`
passes the live frames' selectors — plus one ephemeral selector per
`check_assuming` temporary — as the assumption list, in frame order
(`:3889`). So the CNF core never sees `push`/`pop`; it sees a sequence of
`solve(assumptions)` calls whose assumption lists share prefixes.
`NativeIncrementalCdcl::solve` (`crates/axeyum-cnf/src/proof_sat/
incremental.rs`) called `between_solves` → `Cdcl::reset_search_state`
(`proof_sat.rs:2707`) before every solve and before every `add_clause`:
promote the level-zero trail to `initial_units`, unassign everything, clear
the trail, and re-insert every branchable variable into the order heap; the
next `run` (`proof_sat.rs:3691`) re-propagates `initial_units` and
`search_loop` re-installs the assumptions one decision level each
(`:3910`). Learned clauses, activities and phases survive.

**z3.** `sat::solver::check` (`references/z3/src/sat/sat_solver.cpp:1250`)
begins with `pop_to_base_level()`; `init_assumptions` (`:1882`) then installs
every assumption in ONE scope (`m_search_lvl == 1`). Between checks z3 keeps
only the base level. Its internal `pop(num_scopes)` (`:3650`) is the one the
brief cites: `unassign_vars` (`:3674`) unassigns only the trail above the
popped scope's limit and re-pushes literals whose level survived
(`m_replay_assign`), and `reinit_clauses` (`:3707`) re-attaches clauses that
were added at a non-base level (`m_clauses_to_reinit`, pushed by
`push_reinit_stack` from `mk_bin_clause` / `mk_nary_clause` when
`!at_base_lvl()`, `:464`–`:552`). SMT-level `push`/`pop`
reach the SAT solver as `user_push`/`user_pop` (`:3741`, `:3754`), both of
which `pop_to_base_level()` first. So z3's warm object does re-propagate
every assumption level per check; what it never re-propagates is level zero,
and the machinery this ADR borrows is the re-init list, not the check
schedule.

**CaDiCaL.** `Internal::sort_and_reuse_assumptions` (`references/cadical/src/
assume.cpp:550`) under `opts.ilb` (`options.hpp:139`, default 0: off) sorts
the new assumptions by their position on the trail and backtracks to the
first level whose decision differs from the assumption sequence — which is
exactly the longest-common-prefix rule below; `ilb=1` reuses assumption
levels only, `ilb=2` also decisions when there are no assumptions.
`add_new_original_clause` (`clause.cpp:382`) backtracks to level zero unless
`opts.ilb`; with it, `handle_external_clause`
(`external_propagate.cpp:948`) assigns the unit and, under `elevate == -1`,
backtracks to the level the clause is unit at.

**The invariant a change must preserve.** After a `pop` (here: after the
resume that precedes a solve) the assignment at every kept level must equal
what a fresh propagation of the surviving clauses produces — as a set of
literals; level labels may be higher than the minimal ones, which is what
MiniSat records for every propagation and is sound — and every learned
clause retained across the boundary must be entailed by the clause database
alone. The second half holds here by construction: 1-UIP resolves reasons,
and an assumption is a decision, so it appears in a learned clause as a
literal and is never resolved away (`incremental.rs` module header). The
brief's named control — "dropping the rule that learned clauses derived
under assumptions are dropped must make the fuzz find a disagreement" —
therefore has no code to delete; the guard with that consequence is the
surviving-scope count comparing assumption LITERALS rather than positions,
and both mutation suites below kill its mutant.

## The change

Behind `SolverConfig::warm_keep_trail` (`AXEYUM_WARM_KEEP_TRAIL`, read once
per process, `on`/`off`, malformed refuses), installed into the retained
core by both `IncrementalBvSolver` constructors and reaching
`NativeIncrementalCdcl::set_keep_trail`:

1. **Resume instead of reset.** `solve` computes the longest common prefix of
   the retained assumption sequence and the new one, bounded by the level the
   core is actually at, and calls `Cdcl::resume_search_state(level)`:
   `backtrack_to(level)` plus the per-solve counters and schedules zeroed —
   nothing else. Level `i + 1` of the held trail was opened for assumption
   `i`, so `search_loop`'s assumption installation resumes at
   `decision_level()` and finds the kept levels in place. The order heap is
   not rebuilt: `backtrack_to` re-inserts what it unwinds, and every
   unassigned branchable variable is already in it (the invariant lazy
   deletion maintains; a debug assertion checks it).
2. **Clauses against a live trail** (`Cdcl::add_input_clause_live`): two or
   more non-false literals → watch two (a true one first); exactly one
   non-false, unassigned → enqueue it at the CURRENT level with the clause as
   reason and push `(clause, level)` onto `Cdcl::reinit`; already true above
   its false watch's level → the list too; conflicting with highest false
   level `L > 0` → backtrack to `L − 1` and classify again; conflicting at
   level 0 → `has_empty_clause`; a unit CLAUSE → level zero, unwinding what is
   above it (rare on the warm routes, which assert scoped facts through
   selectors, and what `reset_search_state`'s promotion and the DRAT
   checker's unit propagation both rely on).
3. **Re-examination** (`Cdcl::reinit_replay`, called from `backtrack_to`
   whenever the list is non-empty): every entry tagged above the level just
   unwound to is re-read — false watch unassigned → drop; implied literal
   true → keep; unassigned → enqueue at the new level and keep; false → keep,
   the pending propagation of the literal that falsified it reports the
   conflict. At level 0 everything examined is dropped (z3's `at_base_lvl`).
   Tags are non-decreasing along the list, so the entries to examine are a
   suffix.
4. Two consequences inside the search: `backtrack_to` clamps `qhead` instead
   of resetting it (identical on the search's own calls, where every level
   below the bound was at fixpoint; needed so a pending literal at the kept
   level is not skipped), and the backjump's asserting-literal enqueue checks
   the value first, because the replay can assign that variable at the
   backjump level (`enqueue` now carries a debug assertion against a double
   assignment). After an outright `Unsat` the empty clause is pinned, because
   the level-zero conflict that produced it was consumed by `propagate` and a
   resumed search would not rediscover it.
5. **A reuse-share floor.** When the surviving prefix is under
   `KEEP_TRAIL_MIN_REUSE_SHARE` (one half) of the held trail, the resume takes
   the shipped reset: one sequential pass over the variables beats a
   scattered pop-and-reinsert of the same size.
6. `backtrack_to` re-inserts unwound variables bottom-up (trail order) rather
   than popping top-down: the heap's order is a strict total order, so the
   extraction sequence — the trajectory — is unchanged (both streams'
   digests are identical), and `heap_percolate_up` fell from 9.2 % of the
   synthetic session to 4.5 %.

Items 2, 5 and 6 are the second cut. The first backtracked to the level a
new clause was unit at, which keeps the invariant with minimal labels — and
on the synthetic explorer stream unwound almost everything on every check (a
fresh node's definition clause is unit as soon as one input is assigned, and
inputs sit at low levels): 94 of 19k trail entries reused, 1.74 → 2.09 s
UNDER the lever. Recording the literal at the current level and re-examining
on unwind is what z3 does for clauses added at a non-base level; the
reuse-share floor is what makes the no-reuse shape cost nothing.

## The controls

- `axeyum-cnf` `keep_trail_*` (7 tests): the surviving-prefix gauge with a
  shipped-schedule negative control; a popped scope not surviving; a clause
  unit at a retained level re-propagated when that level unwinds (reused 5
  where a dropped clause gives 4); a unit clause landing at level zero; an
  outright unsat staying unsat; a DRAT proof recorded across sat /
  unsat-under-assumptions / unsat solves checking against the final formula
  and refusing without the unit; and a 1,000-session random differential
  (SplitMix64-finalised draws, ADR-2141) against a fresh solver that replays
  every model, re-solves every failed-assumption core, and requires the
  population to analyse conflicts. **It caught the first cut of the re-init
  commit**: the unit-clause arm read `assign[var]` (the variable) where the
  literal's value was meant and reported a wrong outright `unsat` on 122 of
  400 sessions.
- `tests/incremental_bv_session_fuzz.rs` (`#![cfg(feature = "full")]`, z3
  half under `z3`): random push / assert / check / check-sat-assuming / pop
  sessions over one `IncrementalBvSolver`, each verdict against a fresh
  one-shot solve of the live set and against a z3 `Solver` driven through the
  SAME stream, every `sat` replayed through the ground evaluator, both arms
  from one binary (the field set explicitly), plus the shipped-default pin.
  150 sessions per arm: 1,655 checks, 994 sat / 661 unsat, z3 adjudicated all
  1,655 in both arms, 0 disagreements; the keep-trail arm reused a trail on
  1,491 checks, the shipped arm on 0. Registered in `hooks/pre-push`
  (dispatch/reason, 60 sessions per arm) — until it, no gate compared the
  warm engine's verdicts on a sequence against anything.
- Mutation suites: `warm-keep-trail-2145` (7 guards — surviving-scope
  identity, live registration, the empty-clause pin, the `qhead` clamp, the
  re-init push, the re-init replay, the backjump guard — 7 killed) and
  `warm-keep-trail-2145-session-fuzz` (the identity guard and the default,
  killed from the term level: 2 and 1).

## The measurement

**The replayed session** (`--replay` DptfDevGen r1 owner 1, cores 0–7,
three rounds per arm interleaved, `off` first):

| arm | total | last-band p50 | last-band p90 | propagations / check (last band) | reused trail / check | digest |
|---|---:|---:|---:|---:|---:|---|
| `off` | 1.218 / 1.210 / 1.217 s | 1.34 ms | 5.36 / 5.36 / 5.32 ms | 20,976 | 0 | `9fe6d1e14afe9c19` |
| `on` | 0.454 / 0.450 / 0.447 s | 0.07 ms | 2.10 / 2.09 / 2.06 ms | 2,107 | 31,085 of 39,320 | `9fe6d1e14afe9c19` |

Same 19 conflicts, 2,355 decisions per check either way, 0 disagreements
with the trace, 0 replay failures. The July BatSat engine measured 0.87 s on
this stream (ADR-2142). The p90 that remains is the sibling-branch check
(pop one scope, push its negation): its cone is ~15k of the 47k trail
entries and is genuinely new work.

**The synthetic stream** (`--synthetic 1200`, 54k retained clauses): `off`
1.760 / 1.762 s, `on` 1.773 / 1.761 s, reused 0 — every check re-decides
its path (2,990 decisions, 16,159 propagations per check on both arms), so
the reuse-share floor takes the reset and the lever costs nothing. Digest
`0d31b2edfe790805` on both.

**The pinned lists** (s7, one binary `a9a66260…`, two env values, arms
interleaved per file and alternating in order, 24 s / 8 GiB `ulimit -v`, two
halves of 100 per division on core pairs `1,9` / `3,11` (`QF_BV`) and `5,13`
/ `6,14` (`QF_ABV`), `$EPOCHREALTIME` with the 200 ms sleep self-check;
`bench-results/warm-keep-trail-20260917/`):

| division | decided A / B | sat/unsat A → B | PAR-2 A / B | wall, both-decided | B slower / A slower (>10 % + 50 ms) | gains / losses / flips / `:status` disagreements | nonzero exit |
|---|---:|---:|---:|---:|---:|---:|---:|
| `QF_BV` | 187 / 187 | 58/129 → 58/129 | 3942 / 3934 | 164.5 → 162.9 s (−1 %) | 3 / 3 | 0 / 0 / 0 / 0 | 0 |
| `QF_ABV` | 189 / 189 | 130/59 → 130/59 | 3496 / 3516 | 171.1 → 175.2 s (+2.4 %) | 4 / 10 | 0 / 0 / 0 / 0 | 1 (`wchains140se`, rc 134 on BOTH arms) |

The 20 single-pairing time movers were rerun three times per arm on one core
pair (`recheck-time.sh`): `QF_BV`'s 6 are all equal on recheck (the
`lfsr_002_127_112` 2.7 vs 1.2 s pairing reads 1.41 vs 1.37 s); `QF_ABV`'s 14
split into 9 STABLY FASTER under the lever (the `dwp_formulas` `try4`
disjunction files 0.81 → 0.45 s, `fse-bfs` 0.81 → 0.41 s, `wp_test` 0.81 →
0.41 s, `flanagansaxe_id` 0.41 → 0.31 s, `copy_array11` 1.01 → 0.61 s — the
online array route's refinement loop, which is a warm session), 1 STABLY
SLOWER (`wp_dd.advance_input_offset` 5.01 → 6.38 s: the level labels a
resumed search carries are higher than the minimal ones, so its backjumps
land shallower), and 4 equal (the +2.0 s `mkfifo` and +1.4 s `chroot`
pairings that made the single run's wall +2.4 % read 7.08 vs 7.08 s and 1.71
vs 1.71 s). `QF_BV`'s one-shot route does not use the warm engine, which is
why that list is a null.

**The ship criterion** — 0 stable losses, 0 flips, 0 `:status`
disagreements, the new fuzz green in both arms, the replayed session faster —
is met: 0 / 0 / 0, green (z3 adjudicating all 1,655 checks per arm), 1.21 →
0.45 s. One file is stably slower by 1.4 s against nine stably faster by
0.3–0.4 s each and a warm session 2.7× faster. `DEFAULT_WARM_KEEP_TRAIL`
moves to `true`.

## Gates run

`cargo test -p axeyum-cnf --all-features` (779 passed, 0 failed, all
targets); `-p axeyum-solver --lib --features full -- --test-threads=6`
(1,979 passed); `--features full --test corpus_regression` (2 passed); the 14
`IncrementalBvSolver` suites with the lever off and on (`incremental_bv` 11,
`incremental_stats` 5, `incremental_trait` 3, `model_preference_2140` 17,
`pdr_robustness` 2, `qfbv_profile` 1, `symbolic_execution` 77,
`warm_array_relation_flags` 5, `warm_array_relations` 8, `warm_preprocessing`
4, `warm_structural_array_equality` 8, `warm_structural_array_reads` 9,
`warm_vs_cold` 4, all green in both arms; `warm_array_uf_parents` 16 passed /
1 failed in both arms, the known pre-existing red
`structural_array_parameter_relation_flag_separates_independent_keys`, ungated);
`--features z3 --test bv_differential_fuzz` (3 passed, 1 ignored) and
`--test abv_differential_fuzz` (2 passed) with the lever off and on;
`--features z3 --test incremental_bv_session_fuzz` (3 passed before the
default pin, 4 after); the two mutation suites above.

## Consequences

- Glaurung's warm session pays the delta of a check, not the database. The
  re-pin and six-cell rerun are the follow-up that measures it in production.
- What remains linear: the `assignment_is_model` pass over every clause on
  each `sat` (8.3 % at head, a larger share now), and the sibling check's
  cone. The first is a self-check the term-level replay duplicates and could
  be made incremental; neither is this ADR.
- `NativeIncrementalCdcl` and `IncrementalSat` built directly (the NRA clause
  loop, the CDCL(T) adapters) keep the reset schedule unless they call
  `set_keep_trail(true)`; a theory-carrying object ignores the setting. The
  A/B measured the `SolverConfig` path only.
- `DEFAULT_WARM_KEEP_TRAIL` is registered (dated 2026-09-17, resting on the
  constant, `resume_for_solve` and `reinit_replay`) and pinned by
  `the_shipped_default_keeps_the_trail`, which the mutation suite kills.
