# Phase 0 — Integration & tree hygiene (BLOCKING, serial, one owner)

**Role:** integrator. Works in `~/projects/personal/axeyum` on `main`.
**Blocks:** Lanes A, B, C, F. (Lanes D and E may start in parallel — they touch
disjoint areas.)
**Size:** 1 session.
**Base:** `main` @ `ffc466b4`.

## Why this is first

Two live agent branches carry finished, tested, unmerged capability, and **both
edit `crates/axeyum-smtlib/src/parse.rs` and `crates/axeyum-solver/src/smtlib.rs`**.
If Lanes B and C start from `main` before these land, the parse.rs conflict gets
worse every hour. Land them in dependency order, then fan out.

Audit of all worktrees as of 2026-07-28:

| Worktree | Branch | Ahead of `main` | Disposition |
|---|---|---:|---|
| `axeyum` | `main` @ `ffc466b4` | — | integration checkout |
| `axeyum-uflia-main-next` | `agent/solver/uflia-main-next` | **+7** | **T0.1 — land first** |
| `axeyum-fp-ground-div` | `agent/smtlib/fp-ground-div` | **+1** | **T0.2 — land second** |
| `axeyum-fp-canonical-sort` | `agent/rewrite/fp-constant-sort` | +1 | **already in `main`** (see T0.3) — prune |
| `axeyum-uflia-family-next` | `agent/solver/uflia-family-next` | 0 | tip is an ancestor of `main` — prune |
| `axeyum-s4-ground-int-fold` | `agent/solver/uflia-deadline-next` | +121 | **superseded by T0.1** — see audit below — prune |
| `axeyum-qfslia-population-next` | `agent/solver/qfslia-regex-length-next` | +34 | **HOLD — ~3.6k lines of unique capability** |
| `axeyum-s4-conbyte-gap` | `agent/solver/s4-conbyte-gap` | +20 | all patch-ids in `main` — prune |
| `axeyum-smtcomp` | `agent/smtcomp/full-preparation-live` | +19 | **HOLD — unique tooling incl. the frontier fix** |
| `axeyum-s4-pyex-split` | `agent/solver/s4-pyex-nested-suffix` | +17 | all patch-ids in `main` — prune |
| `axeyum-s4-pyex-tail` | `agent/solver/s4-pyex-tail` | +15 | all patch-ids in `main` — prune |
| `axeyum-s4-pyex-gap` | `agent/solver/s4-pyex-gap` | +13 | all patch-ids in `main` — prune |
| `axeyum-soundness-s4` | `agent/solver/s4-soundness-refresh` | +11 | all patch-ids in `main` — prune |
| `axeyum-mbqi-seed111` | `agent/solver/mbqi-seed111-ci` | 0 | tip is an ancestor of `main` — prune |
| `axeyum-integ-full`, `axeyum-integ-s4`, `axeyum-verify-tip` | — | — | integration scratch — prune |
| `/tmp/axeyum-d781-baseline`, `/tmp/axeyum-fixed-prefix-baseline-*`, `/tmp/axeyum-main-verify.*` | — | — | `/tmp` scratch — prune |
| `/nas4/…/claude-axeyum-cas-work` | `agent/cas/gap-probe-wave-twenty-four` | — | **DO NOT TOUCH** — separate paused CAS lane, see [CAS handoff](../cas-parity-handoff-2026-07-22.md) |

---

## T0.1 — Land the Noetzli QF_SLIA closure

**Branch:** `agent/solver/uflia-main-next` @ `e6f393d8` (7 commits).

**What it is.** The fixed 1,880-file Noetzli QF_SLIA population goes to
**1,880/1,880 decided** (26 SAT / 1,854 UNSAT / 0 unknown) at 250 ms internal /
750 ms outer. Cumulative movement from the retained baseline: 106
`unknown`→`unsat` plus 7 replay-checked `unknown`→`sat`, **zero losses, zero
verdict flips**. The final SAT route is a deterministic source-witness evaluator
capped at 20,000 concrete assignments with no UNSAT capability, fail-closed on
unsupported expressions or malformed witnesses.

**Diff shape:** `axeyum-smtlib/src/parse.rs` +1,845, `axeyum-solver/src/smtlib.rs`
+93, `axeyum-solver/tests/qf_slia_fixed_splice.rs` +380,
`axeyum-strings/tests/membership_deadline.rs` +26, `axeyum-smtlib/src/lib.rs` +4,
`STATUS.md` +30.

**Steps**
1. In the lane worktree, rebase onto `origin/main` and resolve.
2. Foreground full gate in the lane worktree: `just check`. Do **not** pipe the
   output through `tail` and trust the exit code — a piped exit code is `tail`'s,
   not the gate's; grep the *content* for failures (real incident, 2026-07-24).
3. Fast-forward `main`, push.
4. Re-run `cargo test -p axeyum-solver --test corpus_regression` and
   `cargo test -p axeyum-solver --test progress_frontier` on the merged `main`.

**Exit criteria**
- `main` contains `e6f393d8`'s content; `just check` green on `main`.
- The 1,880-row replay reproduces 26 SAT / 1,854 UNSAT / 0 unknown from a
  release build off `main`.
- Both historical wrong-UNSAT guards and both decision regressions still pass.
- `progress_frontier` shows no capability regression.

---

## T0.2 — Land the FP prefix-monotonicity route

**Branch:** `agent/smtlib/fp-ground-div` @ `ce27ba32` (1 commit, ADR-0373
"preregister source FP prefix monotonicity").

**Diff shape:** `axeyum-smtlib/src/parse.rs` +417 (**conflicts with T0.1**),
`axeyum-solver/src/smtlib.rs` +17, `axeyum-fp/tests/fpa2bv_faithfulness.rs` +32,
`axeyum-solver/tests/smtlib.rs` +32, ADR-0373 +127.

**Steps**
1. Rebase onto the *post-T0.1* `main`. Expect a real `parse.rs` conflict —
   resolve by keeping both routes; they are disjoint in intent (string views vs
   FP prefix monotonicity).
2. Re-run the FP tests plus `cargo test --workspace --lib` after resolution;
   a hand-resolved conflict in a soundness-critical parser gets the full lib
   sweep, not a targeted `--test`.
3. Confirm ADR-0373 is recorded in `docs/research/09-decisions/README.md`.
4. Fast-forward `main`, push.

**Exit criteria**
- `just check` green on `main` after the merge.
- The eight-file QF_BVFP Bitwuzla slice is still 8/8 decided, DISAGREE = 0, zero
  replay failures.
- The 34/34 ESBMC serial gate still passes.

---

## T0.3 — Verify-then-prune the stale lanes

> **AUDIT COMPLETED 2026-07-28. Two branches are NOT stale duplicates.** The
> working assumption going in was that the middle group was safe to prune. It
> was not, and the ahead-count was a poor guide in both directions. Findings:
>
> **`git cherry` gave false positives in both directions.** Branches showing
> `+N` unmerged patches often hold content `main` already has under a different
> patch-id (rebased/squashed); branches showing all-`−` can still differ because
> they retain code `main` later *deleted*. The decisive checks were
> `git merge-base --is-ancestor`, the two-dot `git diff main <branch>`, and a
> symbol-level scan asking whether each added identifier exists anywhere in
> `main`'s **history** (`git log -S`) — that last one distinguishes "main
> deleted this later" from "main never had it."
>
> **All ten named branches exist on `origin` at identical SHAs**, so removing a
> worktree — or even the local branch — cannot lose commits. The only real risk
> was uncommitted working-tree content, and there was none of substance: three
> worktrees carried the same `bench-results/frontier/*.json` `solve_ms` jitter
> plus disposable `artifacts/local-ci/*.log`.
>
> **HOLD 1 — `agent/solver/qfslia-regex-length-next`.** 34 commits, **zero**
> patch-ids in `main`, and `main` has touched **none** of its files since the
> `aa58aeba` fork point — so the whole +3,622/−222 diff is unique, not overlap.
> It carries roughly a dozen QF_SLIA/regex decision procedures, each with an
> exhaustive-reference soundness test: decimal-comparison regex preimages for
> `str.to_int` ordering, fixed-segment overlap refutation, boolean-path conflict
> closure, opposite-order cycle detection, length/emptiness bridging, and
> bounded-witness acceleration. Seven representative symbols returned **zero
> hits** against `main`'s entire history. This is capability, not scaffolding.
> Tracked as its own decision — integrate or explicitly abandon with a recorded
> rationale. Expect conflicts with T0.1's `parse.rs` work.
>
> **HOLD 2 — `agent/smtcomp/full-preparation-live`.** 18 unique commits, 4
> touching source. `scripts/smtcomp_repro/full_capture.py` (693 lines) exists in
> `main` at **no path**, nor does `prepare-smtcomp-credited-full.py`; plus
> `full_readiness.py` hardening (`require_exact_integrated_main`). The
> highest-value piece is `fe32194d`, which adds
> `AXEYUM_PROGRESS_FRONTIER_ARTIFACT_DIR` to `progress_frontier.rs` so volatile
> timing curves redirect to a temp dir instead of dirtying the worktree — i.e.
> **it fixes the T0.4 gate-jitter problem at the source** rather than requiring a
> manual revert every session. It has a test rejecting empty/relative paths.
> Cherry-pick that commit on its own; route the SMT-COMP capture tooling to
> Lane D.
>
> **RESOLVED — `agent/solver/uflia-deadline-next`.** Initially flagged HOLD: 110
> of its 121 commits were patch-identical in `main`, but 6 touched source and
> their symbols were absent from `main`'s history. Those six turned out to be
> the *same work* that `agent/solver/uflia-main-next` re-ports onto fresh `main`
> (identical commit subjects). After T0.1 merged, all 11 flagged symbols —
> `build_source_string_sat_problem`, `SourceStringWitness`, `source_replace`,
> `source_indexof`, `source_word_candidates`, `apply_source_string_sat_problem`,
> `exact_rewrite_correlated_at_view`, `exact_rewrite_substring_index_view`,
> `exact_empty_subject_replace_commutes`, `exact_conjugate_replace_identity`,
> `exact_boundary_commutation_identity` — are **present**. Safe to prune.
>
> **DO NOT DROP `stash@{0}`** — "On main: main-checkout frontier bench WIP
> (pre-landing, backed up)". It is a single shared stash visible from every
> worktree, unaffected by `git worktree remove`. Confirm it is genuinely
> superseded before any cleanup that could drop it.

**Do not prune on the ahead-count alone.** A branch showing `+121` may be
pre-rebase noise *or* may hold unique content. For each stale branch:

```sh
# 1. Is every source change already in main?
git diff --stat main...<branch> -- crates/ scripts/
# 2. Any commit whose patch is NOT reachable in main?
git cherry -v main <branch> | grep '^+'
```

Special case already checked: `agent/rewrite/fp-constant-sort` @ `da9e0410` —
`canonical.rs` and `fp_preprocess.rs` are byte-identical to `main`, and `main`'s
`propagate_values.rs` is a **superset** (it also carries `6b5b42ac`'s batching).
It is fully integrated; prune without further review.

**Steps**
1. Run the two commands above for each of the nine stale branches.
2. For any branch with genuinely unique source content, **stop and report** —
   do not prune, do not merge unreviewed; open a follow-up task.
3. Prune the rest: `git worktree remove <path>` then `git branch -d <branch>`
   (`-d`, never `-D`, so git refuses if content would be lost).
4. Remove the three integration-scratch and three `/tmp` worktrees.
5. Leave `/nas4/…/claude-axeyum-cas-work` untouched.

**Exit criteria**
- `git worktree list` shows `main` plus only the six new lane worktrees.
- A committed note in this folder listing every pruned branch and the evidence
  it was fully contained in `main`.

---

## T0.4 — Resolve the dirty working tree

Current dirty state on `main`:

| Path | Kind | Disposition |
|---|---|---|
| `bench-results/frontier/{bv_reduction,lia_cuts,nia_unsat,nra_degree,string_bound}.json` | modified | **gate jitter** — the frontier gates rewrite these; the diffs are `solve_ms` noise only, no `decided`/`status`/`frontier` change. Revert. |
| `artifacts/local-ci/` | untracked | triage: keep locally, add to `.gitignore` if it is generated output |
| `corpus/glaurung-qfbv/` | untracked | corpus capture — decide committed-slice vs gitignored, per the "measure once on a committed slice" rule |
| `docs/plan/multiagent-integration-diary-2026-07-24.md` | untracked | **commit it** — it is the operational record referenced by the contributor guide |
| `docs/reviews/multiagent-20260717/` | untracked | **commit it** — four review reports (core, architecture, glaurung seam, breadth) |

**Verify before reverting the frontier files:** confirm the diff touches only
`solve_ms` and never `decided`, `status`, or `frontier`. If a `decided`/`status`
value moved, that is a capability change, not jitter — stop and investigate.

**Exit criteria:** `git status --short` on `main` is empty except for
deliberately gitignored paths.

---

## T0.5 — Publish the fan-out

1. Create the six lane worktrees from the new `main` (table in
   [README §5](README.md#5-worktree-and-branch-assignment)).
2. Update root `PLAN.md`'s workstream state and recent-change table with the
   Phase 0 landing, and add a pointer to this program folder from
   [`docs/plan/README.md`](../README.md).
3. Confirm each lane brief's "first task" is unambiguous before handing off.

**Exit criteria:** `main` green, six worktrees live, every lane brief has an
owner and a starting commit.
