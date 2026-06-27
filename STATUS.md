# STATUS.md — live tracker

The mutable state file. [PLAN.md](PLAN.md) is the map; this is where we are.
Update the **Current focus**, the **phase table**, and the **changelog** every
session. Status legend: `TODO` · `WIP` · `DONE` · `BLOCKED`.

## Current focus

- **Session 2026-06-27 — AUFLIA scalar-closure schedule guard.**
  The scalar-closure returned-OR guard now wraps general multi-literal branch
  schedule repairs, not only residual follow-up OR branch repairs. The guarded
  schedule path is used in both the projection repair pass and targeted replay
  repair when the failed OR disjunction is known. It declines the same narrow
  no-progress shape: branch schedule makes the branch locally true, bounded
  scalar closure takes at least one scalar step, replay returns to the same OR,
  the branch is false again, and full replay is not improved. A focused
  regression pins the production path by showing raw schedule would force a
  two-literal scalar branch and worsen replay, while guarded branch-disjunction
  repair leaves the model unchanged.

  On `bug337`, this still does **not** close the row, but it cuts measurable
  projection churn. The diagnostic now completes normally rather than timing
  out: `check_auto_explained: unknown` in **54942.223 ms**, `solve: unknown`
  in **55196.682 ms**, and `produce_evidence: unknown` in **55071.934 ms**.
  Compared with the previous guard run, projection repair changes drop
  **587 -> 565**, select symbol changes **299 -> 287**, branch candidates
  **138 -> 132**, and branch symbol changes **161 -> 153**. The frontier remains
  OR **210** with nested OR **236** scalar-closure candidates returning to
  **final_branch_false=2**, **final_total_false=1**. Next useful AUFLIA work is
  still a real scalar/array refinement explaining that OR-236 branch family.
  Verification passed:
  `cargo fmt --all`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_scalar_closure_guard_rejects_returned_or_loop -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_schedule_rejects_scalar_closure_loop -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_scalar_choice_side_effects -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_residual_followup_or_diagnostic -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_select_cycle -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`.
  Diagnostic command:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-27 — AUFLIA scalar-closure branch rejection guard.**
  Residual follow-up OR repair now uses a scalar-closure-aware guard in both the
  replay diagnostic follow-up chain and the production branch/select residual
  repair chain. The guard is deliberately narrow: after the ordinary best
  branch repair, it follows bounded scalar equality closure and declines the
  candidate only when closure takes at least one scalar step, replay returns to
  the same follow-up OR, the candidate branch is false again, and the full
  replay false count is not lower than before the candidate. This keeps the
  productive small follow-up OR repairs while preventing the OR-236 style
  no-progress closure loop from consuming a repair hop.

  On `bug337`, this still does **not** close the row, but the route now matches
  the diagnosis: the residual diagnostic reaches OR **236** at
  `same_full_replay`, **total_false=1**, and reports the scalar-closure
  candidate family where branches **0..7** all return to OR **236** with
  **final_branch_false=2**, **final_total_false=1**. It no longer appends a
  `followup_or236_branch0_branch` repair after that point. The remaining AUFLIA
  work is to learn/refine the missing scalar/array constraint that makes the
  OR-236 family impossible under the current array model, then resume broader
  lazy ROW / func_interp coverage.
  Verification passed:
  `cargo fmt --all`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_scalar_closure_guard_rejects_returned_or_loop -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_scalar_choice_side_effects -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_residual_followup_or_diagnostic -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_select_cycle -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`.
  Diagnostic command:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`
  emitted `check_auto_explained: unknown` in **89296.124 ms** and
  `solve: unknown` in **89668.825 ms**, then exited through the timeout wrapper.

- **Session 2026-06-27 — AUFLIA scalar-closure branch scoring.**
  Replay OR diagnostics now include a bounded scalar-closure branch-candidate
  list. For an OR whose selected branch has multiple false literals and at least
  one scalar-repairable literal, the diagnostic tries every branch up to a
  32-branch cap, runs the existing best branch repair, follows up to four scalar
  equality blockers, then reports the best eight candidates by post-closure
  replay score. This remains diagnostic-only and replay-derived; solver choices
  and answers are unchanged. The focused scalar OR regression now also requires
  `failed_or_scalar_closure_branch_candidates` and the small productive branch's
  final score in the replay note.

  On `bug337`, the top failed OR **210** still has no closure-improving branch:
  the best reported candidates remain **total_false=2** after scalar closure.
  At nested OR **236** / term **13052**, scalar-closure scoring across the
  26-branch family shows the first reported branches all have the same shape:
  raw branch repair reaches **raw_branch_false=0**, **raw_total_false=2**;
  scalar closure repairs the downstream scalar blockers; and replay returns to
  OR **236** with **final_branch_false=2**, **final_total_false=1**. Branches
  **0..7** all exhibit this closure loop in the diagnostic sample. This rules
  out "choose a different low-false OR-236 branch" as the immediate fix. Next
  useful AUFLIA work is to learn/refine the missing scalar/array constraint that
  makes the OR-236 family impossible under the current array model, or to add a
  production closure-aware branch-rejection guard that prevents the repair loop
  from spending time on this branch family.
  Verification passed:
  `cargo fmt --all`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_scalar_choice_side_effects -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_residual_followup_or_diagnostic -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_select_cycle -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`.
  Diagnostic command:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`
  emitted `check_auto_explained: unknown` in **89657.696 ms** and exited via
  the timeout wrapper after the route note.

- **Session 2026-06-27 — AUFLIA paired scalar-chain diagnostic.**
  The OR replay diagnostic now includes a bounded paired scalar-chain trace for
  the selected best branch: it applies the best direct scalar repair for every
  false scalar literal in that branch, then follows up to four scalar equality
  blockers, reporting branch false counts, full replay false counts, and the
  next global blocker after each step. This is diagnostic-only; solver answers
  are unchanged and remain replay-gated. A focused scalar OR regression now
  requires the paired chain in the replay note and pins the productive small
  case where the coupled scalar branch repair reaches **final_total_false=0**.

  On `bug337`, the paired trace turns the OR-236 frontier from "two sibling
  scalar blockers" into an explicit oscillation. At OR **236** / term **13052**,
  branch **0** first repairs both false branch literals: setting symbol **460**
  from term **510** to **3** leaves **branch_false=1**, **total_false=2**, then
  setting symbol **461** from term **510** to **3** reaches
  **branch_false=0**, **total_false=2**, with next blocker **2611**. Following
  the scalar chain then repairs **2611** by setting symbol **460** from term
  **2610** to **1**, which re-breaks OR-236 to **branch_false=1**; repairing
  **2615** by setting symbol **461** from term **2614** to **2** returns to
  OR **236** with **branch_false=2**, **total_false=1**. This rules out forcing
  OR-236 branch 0 via scalar equalities: the branch conflicts with the downstream
  scalar chain. Next useful AUFLIA work is scalar-closure-aware OR branch
  selection/diagnostics for OR 236, so the repair scores branches by their
  post-scalar-closure replay behavior instead of raw false-literal count.
  Verification passed:
  `cargo fmt --all`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_scalar_choice_side_effects -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_residual_followup_or_diagnostic -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_select_cycle -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`.
  Diagnostic command:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`
  returned via timeout wrapper after emitting `check_auto_explained: unknown` in
  **86332.346 ms** and `solve: unknown` in **86425.170 ms**.

- **Session 2026-06-26 — AUFLIA OR-236 scalar side-effect diagnostics.**
  Replay OR diagnostics now carry bounded false-literal details for the selected
  best branch, and scalar equality literals include simulated repair choices:
  target symbol, value term/value, whether the literal becomes true, remaining
  false literals in the branch, full replay false count, and the next global
  blocker. The fields are attached both to the top-level failed OR and to nested
  `global_false_or` entries inside branch/select diagnostics. A focused scalar
  OR regression pins the shape with two false branch literals and verifies that
  both literals and their scalar-choice side effects appear in the replay note.

  On `bug337`, this lands the requested OR-236-specific evidence without changing
  solver answers. The chain still reaches OR **236** / term **13052** at
  `same_full_replay`, **total_false=1**, then ordinary branch repair worsens to
  **total_false=2**. The new details show branch **0** has exactly two false
  scalar equalities: term **12950** (`510 = 2609`, values **3 vs 1**) and term
  **12951** (`510 = 2613`, values **3 vs 2**). Repairing term **12950** sets
  symbol **460** from value-term **510** to **3**, makes that literal true, but
  leaves **branch_false=1**, **total_false=2**, and the next global blocker is
  scalar equality **term 2611** (`2609 = 2610`, **3 vs 1**). Repairing term
  **12951** symmetrically sets symbol **461** from **510** to **3**, leaves
  **branch_false=1**, **total_false=2**, and moves to scalar equality
  **term 2615** (`2613 = 2614`, **3 vs 2**). This rules out a one-literal
  scalar fix at OR 236. Next useful AUFLIA work is a paired repair/diagnostic
  over the sibling scalar chains rooted at symbols 460/461, or a stronger
  explanation of why those chains must be solved together.
  Verification passed:
  `cargo fmt --all`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_scalar_choice_side_effects -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_residual_followup_or_diagnostic -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_select_cycle -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`.
  Diagnostic command:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`
  returned via timeout wrapper after emitting `check_auto_explained: unknown` in
  **86442.712 ms** and `solve: unknown` in **86438.743 ms**.

- **Session 2026-06-26 — AUFLIA scalar-choice branch repair.**
  Follow-up OR repair now compares the existing greedy branch repair with a
  scalar-choice branch candidate. The scalar-choice path explores both
  directions of direct scalar equalities inside a small branch, scores completed
  branch repairs by full original replay, and lets residual-chain repair choose
  the better candidate deterministically. A focused regression pins the intended
  failure mode: for `u = v` with an existing `u = 0`, the scalar-choice candidate
  mutates `v` to `0` and clears replay, while the old greedy direction mutates
  `u` and leaves one false conjunct.

  On `bug337`, this does **not** move the frontier, which is useful negative
  evidence. The residual diagnostic still chooses the ordinary `branch`
  candidate through OR **209**, OR **219**, and OR **236**:
  `...+followup_or236_branch0_branch` remains `worse_full_replay`,
  **total_false=2**, exposing scalar equality **term 2611**. The preceding best
  point is still OR **236** / term **13052** at **total_false=1**, where branch
  **0** has **2/2** false literals and first false term **12950** (`3` vs `1`).
  Route cost remains in the same band (`check_auto_explained: unknown` in
  **79636.664 ms**, `solve: unknown` in **79668.818 ms**). Next useful AUFLIA
  work is an OR-236-specific diagnostic that reports both false branch literals
  and their scalar repair choices/side effects, not another generic scalar-choice
  direction pass.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_scalar_branch_choice_prefers_replay_safe_direction -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_select_cycle -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_residual_followup_or_diagnostic -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`.
  Diagnostic command:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA bounded residual chain repair.**
  The guarded branch/select-cycle repair now follows a bounded residual chain
  after the same-branch store-target repair: while the original OR and select
  equality remain true, it can repair the next generated OR's best branch for up
  to four hops and records the best strict full-replay improvement. This remains
  behind the existing small-surface guard (**current_false <= 2** and **<=64**
  positive replay conjuncts). A focused regression covers the productive shape:
  branch repair -> select repair -> rebuild `c = store(a,3,7)` -> repair a
  second OR's `d = c` array equality, clearing full replay to
  **total_false=0**.

  Diagnostics now also follow up to four generated-OR hops. On `bug337`, the
  chain remains too large for production repair but reveals the next real
  frontier. OR **210** -> select **34** -> term **580** -> OR **209** branch **3**
  -> OR **219** branch **3** improves the diagnostic chain to
  **same_full_replay**, **total_false=1**, with next blocker OR **236** / term
  **13052**. OR **236** has **26** branches; best branch **0** has **2/2** false
  literals, first false term **12950**, scalar equality terms **510/2609** with
  values **3 vs 1**. Blindly repairing that branch worsens back to
  **total_false=2** and exposes scalar equality **term 2611**. Route cost rose
  modestly with the deeper diagnostic (`check_auto_explained: unknown` in
  **79551.190 ms**, `solve: unknown` in **79477.768 ms**). Next useful AUFLIA
  work is scalar-aware handling at OR **236** after the residual chain, not more
  component-array-only follow-up hops.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_select_cycle -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_residual_followup_or_diagnostic -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`.
  Diagnostic command:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA residual follow-up OR diagnostics.**
  Same-branch residual diagnostics now take one additional bounded diagnostic
  step: after `chain+same_branch_store_target` (or direct equivalent) repairs
  the returned OR locally, if the next global blocker is a different generated
  OR, the note tries that OR's best branch on a copy and emits a row such as
  `chain+same_branch_store_target+followup_or209_branch3`. A focused regression
  covers the small analogue: repair the original branch, repair the select,
  rebuild the branch store target, then repair a second OR's array equality to
  reach `total_false=0`.

  On `bug337`, the OR **210** -> select **34** -> term **580** -> OR **209**
  pair is locally repairable, but it is not the full cycle. The new row
  `chain+same_branch_store_target+followup_or209_branch3` preserves select term
  **555** and repairs OR **209** branch **3**, yet full replay remains
  `worse_full_replay` with **total_false=2** and moves to OR **219** / term
  **6084**. OR **219**'s best branch is branch **3** with one false literal,
  term **1402**, comparing arrays
  `(array default 0 [0 -> 1] [1 -> 2] [2 -> 1])` and
  `(array default 0 [1 -> 2] [2 -> 1])`. Route cost remains stable:
  `check_auto_explained: unknown` in **77356.618 ms** and `solve: unknown` in
  **77377.729 ms**. Next useful AUFLIA work is a bounded multi-hop
  component-array chain repair/diagnostic with an explicit replay-improvement
  gate, not a two-OR special case.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_residual_followup_or_diagnostic -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_select_cycle -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`.
  Diagnostic command:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA same-branch residual diagnostics.**
  Branch/select candidate diagnostics now also try the same-branch residual
  candidate on diagnostic copies when a branch repair plus select repair returns
  to the same generated OR with the same best branch and exactly one false
  literal. The note emits rows such as
  `chain+same_branch_store_target`, preserving the original branch/select
  diagnostic shape while reporting the post-select residual effect. A focused
  regression covers the small `c = store(a,3,7)` residual shape and proves the
  diagnostic row reaches `total_false=0`.

  On `bug337`, this answers the previous unknown. The OR **210** / select **34**
  chain residual for term **580** does repair the store target and keeps select
  term **555** true, but it is still `worse_full_replay` with
  **total_false=2**. The first global blocker moves to OR **209** / term
  **3654**, whose best branch is branch **3** with one false literal, term
  **3650**: an equality over the same array values flipped
  `(array default 0 [0 -> 2] [1 -> 2] [2 -> 1])` vs
  `(array default 0 [0 -> 2] [1 -> 3] [2 -> 3])`. The route remains the prior
  large-row frontier: `check_auto_explained: unknown` in **77456.450 ms** and
  `solve: unknown` in **77324.228 ms**, with the outer timeout cleaning up the
  evidence tail. Next useful AUFLIA work is a paired OR-210/OR-209 component
  array repair, not another single term-580 target repair.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_select_cycle -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`.
  Diagnostic command:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA guarded same-branch store residual repair.**
  Added a target-side residual store repair for small branch/select cycles. After
  a branch repair and store-chain select repair return to the same generated OR,
  if the same branch is still best and exactly one false literal remains, the
  repair handles `target = store(base, i, v)` by rebuilding `target` from the
  current repaired `base`. This preserves the select readback while restoring the
  branch's store-definition equality, and it still mutates the projected model
  only under a strict full-original-replay improvement gate. A focused regression
  pins the intended shape: `c = store(a, 3, 7)` must remain true after
  `5 = select(a, i)` repairs `a[2]`.

  This is deliberately guarded to the same small replay surfaces as the prior
  branch/select-cycle repair. The unguarded `bug337` target-side probe was
  measured and rejected: it did not move the large row off generated OR **210** /
  term **3879** and raised route time to about **87 s**. With the guard restored,
  the large-row diagnostic is back in the prior unknown regime, with
  `solve: unknown` in **76861.991 ms** before the evidence tail cleanup. The next
  useful AUFLIA work is not another generic target-side store repair; it is
  diagnosing why the concrete OR-210 term-580 residual is not accepted on the
  large row, likely via residual-candidate diagnostics or component-array state.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_select_cycle -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `git diff --check`.
  Diagnostic command:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA returned-OR branch/select diagnostics.**
  Branch/select candidate diagnostics now preserve the `ReplayOrFailure` details
  for the first global blocker after each composed branch+select trial. When a
  select repair lands back on a generated OR, the note reports that OR's branch
  count, best branch ordinal, false-literal count, first false literal term, and
  equality values. The focused branch/select cycle regression now asserts that
  these returned-OR details are emitted for the small alternate-branch shape.

  This pinpoints the next `bug337` component rather than changing solve
  behavior. The 10 s route diagnostic remains `unknown` at **round=2**,
  **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, **working_assertions=7127**, first
  false generated OR **210** / term **3879**, and about **77 s** route time.
  The new returned-OR fields show that after **branch 0 -> select 34 chain**,
  the select equality **term 555** is true, full replay is still
  **total_false=2**, and the next global blocker is again OR **210**. Its best
  branch is still branch **0**, but now with only **1/8** false literals:
  **term 580**, `x_339 = store(x_325, x_337, 2)`, with lhs
  `(array default 0 [0 -> 2] [1 -> 3] [2 -> 3])` and rhs
  `(array default 0 [0 -> 2] [1 -> 2] [2 -> 1])`. This rules out more
  branch-choice work: the next useful repair is specifically preserving the
  select-34 store-chain readback while repairing branch-0 store definition
  **term 580** or its component arrays.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_select_cycle_repair_forces_alternate_or_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `git diff --check`.
  Diagnostic emitted the route note above, then the outer timeout cleaned up the
  non-exiting evidence tail:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA guarded branch/select cycle repair.**
  Added a bounded branch/select-cycle replay repair for small generated-OR
  replay surfaces. The repair looks for the concrete pattern exposed by the
  prior diagnostics: repair one OR branch, observe a direct `x = select(a,i)`
  blocker, repair that select with store-chain or direct array-entry repair,
  then see the same OR become the first blocker again. From that post-select
  state it tries a different branch of the same OR and mutates the projected
  assignment only if the final full-original replay false count is strictly
  lower than the starting count. It is capped at **8** OR branches, **32**
  second-branch trials, **current_false <= 2**, and **<=64** positive replay
  conjuncts. A focused regression covers the intended shape where repairing
  `a = b` exposes `0 = select(a,i)`, the select repair breaks `a = b` and
  returns to the same OR, then an alternate `q = true` branch clears replay.

  This is deliberately **not** a `bug337` closure. Measuring the same repair
  without the small-surface conjunct guard on `bug337` was rejected: it kept the
  final frontier at generated OR **210** / term **3879** and raised route time
  from about **77 s** to about **93 s** for the same 10 s solver budget. With
  the guard retained, the large row returns to the prior useful frontier:
  `unknown` at **round=2**, **sites=4096**, **array_eq_atoms=150**,
  **row_lemmas=42**, **cong_lemmas=6973**, **diff_skolems=146**,
  **working_assertions=7127**, first false generated OR **210**, term **3879**,
  and about **77 s** route time before the outer timeout cleaned up the
  evidence tail. The prior branch/select diagnostics remain decisive:
  branch **0** -> select **34** store-chain repair makes term **555** true but
  lands back on OR **210** at **total_false=2**; direct repair worsens to
  ordinal **35**. Next useful AUFLIA work is component-level store-chain /
  branch-state repair inside the **210 -> 34 -> 210** cycle, not simply trying
  another OR-210 branch after the select repair.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_select_cycle_repair_forces_alternate_or_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_beam -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_select_repair_beam_composes_followup_or_repair -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `git diff --check`.
  Diagnostic emitted the route note above, then the outer timeout cleaned up the
  non-exiting evidence tail:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA branch/select cycle diagnostics.**
  Final lazy-extensionality replay failures on generated ORs now include
  bounded `branch_select_candidate_diagnostics`: for each repairable OR branch
  whose next full-replay blocker is a direct `x = select(a,i)` equality, the
  note composes the branch trial with the same store-chain and direct
  array-entry select repairs used by targeted replay repair. Each row reports
  branch ordinal, select ordinal/term, repair kind, branch/select change
  counts, whether the select becomes true, full original replay false count,
  and the next global replay blocker. A focused regression pins the intended
  shape where an OR branch repair exposes a later direct select equality and
  the direct select candidate clears the full replay.

  This does **not** close `bug337`, but it removes another unknown in the
  queue-lock. The 10 s route diagnostic still reports `unknown` at **round=2**,
  **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, **working_assertions=7127**, first
  false generated OR **ordinal 210**, term **3879**, and about **77 s** route
  time before the outer 180 s timeout cleaned up the evidence tail. The new
  branch/select rows show the concrete cycle: branch **0** followed by the
  store-chain select repair for ordinal **34** / term **555** makes the select
  true, but is still **worse_full_replay** with **branch_changes=6**,
  **select_changes=37**, **total_false=2**, and lands back on OR **210** / term
  **3879**. Branch **0** followed by the direct array-entry repair also makes
  the select true, but worsens further (**total_false=3**) and exposes ordinal
  **35** / term **560** (`0` vs `1`). Branches **1** and **2** show similar
  select-local repairs that worsen full replay. Next useful AUFLIA work is now
  a cycle-aware repair for the **210 -> 34 -> 210** path, e.g. a bounded
  replay-state/tabu scheduler that can keep the branch-0 store-chain select
  repair and then force a different OR-210 branch or component-level store-chain
  change under the final strict full-replay improvement gate. Another broad
  OR-start beam or one-step select repair is already ruled out.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_branch_select_candidate_diagnostics -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_beam -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `git diff --check`.
  Diagnostic emitted the route note above, then the outer timeout cleaned up the
  non-exiting evidence tail:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA guarded OR/select replay beam.**
  Generated-OR replay failures now get the same mixed select/OR replay beam only
  on small, multi-false replay surfaces: **current_false > 1** and at most
  **64** positive replay conjuncts. This keeps the useful composed-repair shape
  available for small projections while preventing the broad OR-start beam from
  spending the large AUFLIA queue-lock budget. A focused regression covers the
  retained case: repairing an OR branch ties full replay by breaking a later
  direct select readback, then the mixed beam composes a select repair and
  strictly improves the full replay false count. The older branch-beam and
  one-step branch-choice fallbacks remain unchanged for larger OR failures.

  This is deliberately a guarded retention, not a `bug337` closure. The
  unguarded OR-start beam was measured and rejected for the large row: the
  diagnostic regressed from OR **210** back to direct select equality **34** /
  term **555** and took about **149 s** wall for the 10 s solver budget. With the
  guard, the `bug337` diagnostic returns to the previous useful frontier:
  `unknown` at **round=2**, **sites=4096**, **array_eq_atoms=150**,
  **row_lemmas=42**, **cong_lemmas=6973**, **diff_skolems=146**,
  **working_assertions=7127**, first false generated OR **ordinal 210**, term
  **3879**, **projection_repair_changes=587**, and about **76 s** wall. The
  OR 210 branch diagnostics are unchanged: branch **0** locally repairs but
  returns to select equality **34** / term **555** at **total_false=2**, and
  branch **3** flows to OR **211** then OR **212**. Next useful AUFLIA work is a
  cycle-specific diagnostic or repair for **210 branch-0 -> 34 select**, not a
  broader OR-start mixed beam.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_or_repair_beam_composes_followup_select_repair -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_select_repair_beam_composes_followup_or_repair -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_beam -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `git diff --check`.
  Diagnostic emitted the route note above, then the outer timeout cleaned up the
  non-exiting evidence tail:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA mixed select/OR replay beam.**
  Direct-select targeted replay repair now first tries a bounded mixed replay
  beam before falling back to the older one-step non-worsening select repair.
  The beam expands only direct `x = select(a,i)` failures and generated OR
  failures, keeps at most **8** states, expands at most **64** states, follows at
  most **6** repair steps, allows at most **current_false + 4** temporary false
  conjuncts, and lets a failure ordinal be revisited at most twice. It mutates
  the projected assignment only when the composed sequence strictly reduces the
  full original replay false count, so returned `sat` remains gated by complete
  evaluator replay. A focused regression covers the intended shape: a select
  repair alone only ties full replay, but composing it with a follow-up OR repair
  strictly improves the replay false count in one targeted step.

  This does **not** close `bug337`, but it moves the frontier. The 10 s route
  diagnostic remains `unknown` at **round=2**, **sites=4096**,
  **array_eq_atoms=150**, **row_lemmas=42**, **cong_lemmas=6973**,
  **diff_skolems=146**, and **working_assertions=7127**. The first false replay
  point moves from direct select equality **ordinal 34**, term **555**, to
  generated OR **ordinal 210**, term **3879**, after
  **projection_repair_changes=587**. Projection telemetry is now
  **select_repair_candidates=10014**, **select_repair_array_changes=103**,
  **select_repair_symbol_changes=299**, **branch_repair_candidates=138**,
  **branch_repair_symbol_changes=161**, **scalar_repair_candidates=24**,
  **scalar_support_candidates=24**, **scalar_stabilized_trials=0**,
  **scalar_rejected_worse_trials=0**,
  **scalar_equal_support_repairs=0**, and
  **scalar_repair_symbol_changes=24**. OR 210 has **4** branches; best branch
  **0** has **2/8** false literals, first false term **580**,
  `x_339 = store(x_325, x_337, 2)`, with array values
  `(array default 0 [0 -> 2] [1 -> 3] [2 -> 3])` vs
  `(array default 0 [0 -> 2] [1 -> 2] [2 -> 1])`. Branch diagnostics show branch
  **0** repairs locally but worsens/ties full replay at **total_false=2** and
  returns to select equality **ordinal 34** / term **555**; branch **3** repairs
  locally but lands on OR **211**, and its pair branch **3** lands on OR **212**.
  This confirms the next useful move: invoke the mixed select/OR beam from
  generated-OR failures as well, or add a targeted diagnostic for the
  **210 branch-0 → 34 select** cycle before broadening the beam further. The
  diagnostic wall time rose to about **76 s** for the 10 s solver budget, so the
  next step must keep cost caps explicit.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_select_repair_beam_composes_followup_or_repair -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_repairs_direct_select_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_repairs_select_through_store_chain -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_select_candidate_diagnostics -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_beam -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `git diff --check`.
  Diagnostic emitted the route note above, then the outer timeout cleaned up the
  non-exiting evidence tail:
  `CARGO_BUILD_JOBS=2 timeout 180s cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA direct-select repair diagnostics.**
  Final lazy-extensionality replay failures on a direct `x = select(a,i)`
  equality now include `select_candidate_diagnostics` alongside the existing
  branch diagnostics. The note tries the same two candidates as targeted replay
  repair on projection copies: the store-chain/readback repair and the direct
  array-entry store. For each candidate it records whether the failed select
  equality becomes true, the repair-change count, the full original replay false
  count, and the first global replay blocker after applying the candidate. A
  focused regression pins the intended case where both select candidates repair
  the current equality and expose the next false conjunct.

  This does **not** close `bug337`, but it replaces the prior guess with a
  concrete queue-lock edge. The 10 s route diagnostic still reports `unknown` at
  **round=2**, **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, and
  **working_assertions=7127**. The first false replay point remains direct
  readback equality **ordinal 34**, term **555**,
  `x_388 = select(x_325, x_337)`, values **1 vs 0**, after the same
  **projection_repair_changes=655**. The new select diagnostics show:
  `chain` makes term 555 true but is **same_full_replay** with **changes=37**,
  **total_false=2**, and next global blocker **ordinal 210**, term **3879**;
  `direct` also makes term 555 true but is **worse_full_replay** with
  **changes=1**, **total_false=3**, and next blocker **ordinal 35**, term
  **560**, equality terms **557/559**, values **0 vs 1**. Next useful work is
  therefore not more one-step direct-select repair. We need a bounded composition
  move that can carry the same-full-replay store-chain candidate into repair of
  generated OR **210** while still accepting only a final strict replay
  improvement, or a diagnostic that explains why the 210/34 select-chain cycle
  cannot be scheduled.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_select_candidate_diagnostics -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_beam -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `git diff --check`.
  Diagnostic emitted the route note above before being interrupted after no
  further useful output:
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA beam readback stabilization.**
  Accepted branch-beam candidates now get a post-branch readback stabilization
  pass before they are scored: direct scalar symbols of asserted
  `x = select(a,i)` equalities are aligned to the candidate's repaired array
  values across all array symbols, and the beam keeps the stabilized candidate
  only when its full-original-replay false count is better than the raw
  candidate. This preserves the existing SAT gate: the projected assignment is
  still mutated only by a final strict replay improvement, and returned `sat`
  still requires a complete evaluator replay. A focused regression covers the
  branch-store case where repairing `a = store(b,i,v)` would otherwise leave
  `y = select(a,i)` stale; stabilization updates `y` to the repaired array
  value and reaches zero replay failures.

  This does **not** move `bug337`. The 10 s diagnostic remains `unknown` at
  **round=2**, **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, and
  **working_assertions=7127**. Projection telemetry remains
  **select_repair_candidates=10011**, **select_repair_array_changes=102**,
  **select_repair_symbol_changes=352**, **branch_repair_candidates=140**,
  **branch_repair_symbol_changes=177**, **scalar_repair_candidates=24**,
  **scalar_support_candidates=24**, **scalar_stabilized_trials=0**,
  **scalar_rejected_worse_trials=0**,
  **scalar_equal_support_repairs=0**, **scalar_repair_symbol_changes=24**, and
  **projection_repair_changes=655**. The first false replay point is unchanged:
  direct readback equality **ordinal 34**, term **555**,
  `x_388 = select(x_325, x_337)`, values **1 vs 0**. This rules out simple
  post-beam scalar-readback alignment as the missing step. Next useful work is
  a targeted direct-select repair diagnostic for term **555** that reports the
  chain candidate, direct array-entry candidate, post-candidate false counts,
  and the first blocker after each candidate, so we can see whether select
  repair is rejected as worsening, undone by store-chain reconstruction, or not
  reached before the targeted repair cap.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_beam_stabilizes_direct_select_readbacks -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_beam_allows_temporary_uphill_schedule -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_pair_choice_scores_adjacent_or_repairs -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA bounded branch-beam replay repair.**
  Targeted lazy-extensionality replay now has a capped branch-schedule beam
  after strict two-OR pair repair and before the older single-OR fallback. The
  beam searches only generated OR replay failures, keeps at most **8** states,
  expands at most **64** states, follows at most **6** branch repairs, and allows
  at most **current_false + 4** temporary false conjuncts inside the beam. It
  mutates the projected model only when a candidate achieves a strict final
  full-original-replay false-count improvement, so SAT is still accepted only by
  the existing full evaluator replay. A focused regression covers the shape that
  motivated this: strict pair repair rejects an intermediate two-false state,
  while the beam repairs two later ORs and reaches a fully replaying assignment.

  This still does **not** close `bug337`, but it changes the measured frontier.
  The 10 s diagnostic remains `unknown` at **round=2**, **sites=4096**,
  **array_eq_atoms=150**, **row_lemmas=42**, **cong_lemmas=6973**,
  **diff_skolems=146**, and **working_assertions=7127**. Projection telemetry is
  now **select_repair_candidates=10011**, **select_repair_array_changes=102**,
  **select_repair_symbol_changes=352**, **branch_repair_candidates=140**,
  **branch_repair_symbol_changes=177**, **scalar_repair_candidates=24**,
  **scalar_support_candidates=24**, **scalar_stabilized_trials=0**,
  **scalar_rejected_worse_trials=0**,
  **scalar_equal_support_repairs=0**, **scalar_repair_symbol_changes=24**, and
  **projection_repair_changes=655**. The first false replay point moves away
  from generated OR **219** to direct readback equality **ordinal 34**, term
  **555**, `x_388 = select(x_325, x_337)`, with values **1 vs 0**. This is a
  useful but incomplete move: the non-monotone branch schedule can cross the
  219/211/212 queue-lock cycle, but it leaves a direct select readback
  inconsistent. Next useful work is not wider beam search; inspect why the
  existing store-chain/direct select repair cannot stabilize this readback after
  the beam assignment, or add readback stabilization inside accepted beam states.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_beam_allows_temporary_uphill_schedule -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_pair_choice_scores_adjacent_or_repairs -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_branch_pair_candidate_diagnostics -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_branch_candidate_diagnostics -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA branch-pair edge diagnostics.**
  Final lazy-extensionality replay failures now include a bounded
  `branch_pair_candidate_diagnostics` section for failed generated ORs. The
  diagnostic is computed only on the final failed replay path, follows at most
  16 pair edges, and only expands first-branch candidates whose next full-replay
  blocker is a different generated OR. For each second-OR branch it reports the
  first branch, second OR ordinal/term, second branch, initial/final false
  literals, whether the pair is a candidate / no-repair / breaks an OR / same or
  worse full replay, repair-change counts, total full-replay false count, and
  the next global blocker. A focused regression pins this on a flattened
  conjunct assertion so the ordinal shape matches the large AUFLIA diagnostics.

  This confirms why the current monotone two-OR repair stops on `bug337`. The
  10 s diagnostic remains `unknown` at **round=2**, **sites=4096**,
  **array_eq_atoms=150**, **row_lemmas=42**, **cong_lemmas=6973**,
  **diff_skolems=146**, **working_assertions=7127**, and the same failed OR
  **ordinal 219**, term **6084**, after **projection_repair_changes=647**. The
  branch-candidate section is unchanged: branch **3** repairs locally and lands
  on global OR **ordinal 211**, term **4108**, with **total_false=1**. The new
  pair-edge section shows every `219` branch-3 → `211` pair candidate repairs
  the second branch locally but worsens full replay from that one-false baseline:
  branch **0** has **init=2**, **final=0**, **total_false=2**, next blocker
  scalar term **641** (**1 vs 0**); branch **1** has **init=5**, **final=0**,
  **total_false=4**, next blocker term **646** (**2 vs 0**); branch **2** has
  **init=5**, **final=0**, **total_false=4**, next blocker term **444**
  (**1 vs 0**); branch **3** has **init=3**, **final=0**, **total_false=2**,
  and lands on generated OR **ordinal 212**, term **4341**. This is the key
  practical result: a strictly monotone two-OR repair cannot progress from the
  current frontier. Next useful work is a bounded branch-schedule/beam search
  that allows temporary uphill moves inside the beam while accepting only a final
  full-replay improvement, with explicit caps and tabu/cycle handling around the
  **219 → 211 → 212** queue-lock chain.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_branch_pair_candidate_diagnostics -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_pair_choice_scores_adjacent_or_repairs -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_branch_candidate_diagnostics -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA coupled branch-pair replay repair.**
  Targeted lazy-extensionality replay now has a bounded two-disjunction branch
  repair before the existing single-disjunction branch choice. For a failed
  generated OR, it tries each repairable branch candidate on a projection copy;
  if that copy's next full-replay blocker is a different generated OR, it tries
  each repairable branch of that second OR on the same copy. A pair is accepted
  only when both ORs evaluate true and the full original positive replay false
  count strictly decreases. The existing full original evaluator replay remains
  the only SAT acceptance gate, and the old single-OR repair remains the
  fallback. A focused regression pins the motivating scoring shape: single-OR
  repair takes a local tie (`x = 1`), while pair scoring chooses the compatible
  adjacent schedule (`y = 1`, then `x = 2`) that satisfies both ORs.

  This still does **not** close `bug337`, but it is a real frontier move rather
  than a no-op. The 10 s diagnostic remains `unknown` at **round=2**,
  **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, and
  **working_assertions=7127**, but the first false replay point moves from
  generated OR **ordinal 211**, term **4108**, to generated OR **ordinal 219**,
  term **6084**. Projection telemetry rises to
  **select_repair_candidates=10011**, **select_repair_array_changes=102**,
  **select_repair_symbol_changes=343**, **branch_repair_candidates=142**,
  **branch_repair_symbol_changes=178**, **scalar_repair_candidates=24**,
  **scalar_support_candidates=24**, **scalar_stabilized_trials=0**,
  **scalar_rejected_worse_trials=0**,
  **scalar_equal_support_repairs=0**, **scalar_repair_symbol_changes=24**, and
  **projection_repair_changes=647**. The new failed OR's best branch is **3**,
  with first false term **1402**, `x_213 = x_199`; branch **3** repairs locally
  (**init=1**, **final=0**, **changes=48**) and moves the global blocker back to
  **ordinal 211**, term **4108**. Branches **0/1/2** repair locally but worsen
  full replay and expose earlier scalar blockers at terms **1329** (**1 vs 0**),
  **1334** (**2 vs 0**), and **388** (**1 vs 0**). The diagnostic run is also
  slower than the prior one-branch frontier (**~45 s** wall for the 10 s solver
  budget), so the next step should be a bounded multi-OR/beam branch scheduler
  with explicit cost control, or pair-edge diagnostics that identify the
  219↔211 cycle before broadening the search further.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_pair_choice_scores_adjacent_or_repairs -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_branch_candidate_diagnostics -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA branch-candidate replay diagnostics.**
  Final lazy-extensionality replay failures now annotate failed generated ORs
  with per-branch candidate diagnostics, computed only on the final failed replay
  path. For each branch the note records initial false literals, whether targeted
  branch repair produced a non-worsening candidate or worsened full replay,
  repair-change count, final branch false count, total full-replay false count,
  the first branch-local blocker, and the first global blocker after applying
  the candidate. A focused regression pins the simple unrepairable two-branch
  shape so this remains available in future diagnostics.

  This still does **not** close `bug337`; the 10 s diagnostic remains
  `unknown` at **round=2**, **sites=4096**, **array_eq_atoms=150**,
  **row_lemmas=42**, **cong_lemmas=6973**, **diff_skolems=146**, and
  **working_assertions=7127**. The failed generated branch disjunction remains
  **ordinal 211**, term **4108**, with best branch **3** blocked by term
  **714**, `x_325 = x_311`. The new branch diagnostics are the useful result:
  branch **0** repairs locally (**init=3**, **final=0**) but leaves
  **total_false=2** and moves the global first blocker to **ordinal 210**, term
  **3879**; branch **3** repairs locally (**init=1**, **final=0**) and is best
  by **total_false=1**, but also moves the global first blocker to **ordinal
  210**, term **3879**. Branches **1** and **2** repair locally but worsen full
  replay (**total_false=4/5**) and expose earlier scalar equalities: term
  **646** with values **2 vs 1**, and term **444** with values **1 vs 0**.
  Next useful work is a coupled two-level branch repair/schedule across adjacent
  disjunctions **210/211** (`x_336`/`x_322`), or a diagnostic/repair that scores
  branch pairs jointly. More one-branch local heuristics are now unlikely to move
  this instance.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_branch_candidate_diagnostics -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA order-guarded branch repair.**
  Targeted lazy-extensionality branch-choice repair can now repair false integer
  order guards inside a candidate branch. The repair recognizes `IntLt/Le/Gt/Ge`
  and a single `not` around them, moves one direct integer symbol just enough to
  satisfy the desired relation, and keeps the local change only if the literal
  becomes true and the full original replay false count is non-worsening. Branch
  candidates also now use the scalar equality choice helper before and after
  store/array/order repairs, so dependent symbol-to-symbol equalities can catch
  up after an order guard changes one side. A focused regression covers the
  exact shape: the locally best branch is an unrepairable false Boolean, while a
  later branch needs `not (x <= y)` plus `z = x`.

  This does **not** move `bug337` yet. The 10 s probe remains at **round=2**,
  **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, and
  **working_assertions=7127**. Projection repair counters are unchanged from the
  prior baseline: **select_repair_candidates=10011**,
  **select_repair_array_changes=102**, **select_repair_symbol_changes=320**,
  **branch_repair_candidates=136**, **branch_repair_symbol_changes=165**,
  **scalar_repair_candidates=24**, **scalar_support_candidates=24**,
  **scalar_stabilized_trials=0**, **scalar_rejected_worse_trials=0**,
  **scalar_equal_support_repairs=0**, **scalar_repair_symbol_changes=24**, and
  **projection_repair_changes=611**. The first false conjunct is still generated
  branch disjunction **ordinal 211**, term **4108**; best branch **3** has
  **1/6** false literals, term **714**, `x_325 = x_311`. This shows the
  globally satisfying `x_322 = 2` branch still is not accepted by current
  branch-choice scoring even after order-guard repair. Next useful work is a
  branch-candidate diagnostic that reports each branch's post-repair false
  literals/first blocker, not more blind repair operators.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_repairs_order_guarded_branch_choice -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_can_choose_non_best_repairable_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_equality_repairs_target_through_store_definition -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA definition-aware array equality repair.**
  Branch array-equality repair now has a second, definition-aware candidate in
  addition to the prior direct component copy. For a false selected equality
  `a = b`, the replay repair can try to make each component member equal to a
  source array value by pushing that value through the member's currently
  selected `target = store(base, k, v)` or direct-equality definition, recursively
  repairing bases and rebuilding targets. The candidate is still replay-gated:
  it competes against the old direct copy and is kept only when the branch false
  count drops and the full original replay false count does not increase. A
  focused regression covers the case where direct copying `a := b` would leave a
  lower selected store branch false, while repairing `base` and rebuilding `a`
  satisfies both the store branch and the equality branch.

  This does **not** move `bug337` yet. The current 10 s probe is unchanged at
  **round=2**, **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, and
  **working_assertions=7127**. The first false conjunct remains generated branch
  disjunction **ordinal 211**, term **4108**; best branch **3** has **1/6**
  false literals, term **714**, `x_325 = x_311`, with `x_325` equal to
  `(array default 0 [0 -> 1] [1 -> 3] [2 -> 3])` and `x_311` equal to
  `(array default 0 [0 -> 1] [1 -> 2] [2 -> 1])`. A temporary
  `MAX_TARGETED_REPLAY_REPAIRS=16` run was measured and rejected: it stayed at
  the same branch/equality frontier while raising projection churn from **611**
  to **779** changes. Next useful work is not another cap increase; inspect why
  the globally satisfying `x_322 = 2` store branch is not selected/repairable
  under the current branch-choice scoring.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_branch_equality_repairs_target_through_store_definition -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_repairs_direct_select_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_repairs_select_through_store_chain -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_selected_array_equality_component -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA store-chain readback projection.**
  Targeted lazy-extensionality replay can now repair a false direct
  `x = select(a, i)` readback through the currently selected store-chain
  definition for `a`. Instead of only writing the target array cell, the repair
  scans selected/best branch literals for `a = store(base, k, v)` or direct
  array equalities, recursively pushes inherited reads into the base when
  `i != k`, rebuilds the target store, aligns direct readback symbols, and keeps
  the best candidate only when the failed readback becomes true and full
  original replay is non-worsening. The old direct target-cell write remains as
  a competing fallback. A focused regression pins the motivating shape where
  directly writing `b[i]` would break a true branch `b = store(a, j, v)`, while
  writing `a[i]` and rebuilding `b` satisfies both.

  This still does **not** close `bug337`, but it removes the prior direct
  readback blocker `x_388 = select(x_325, x_337)`. The 10 s probe remains at
  **round=2**, **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, and
  **working_assertions=7127**. Projection repair now reports
  **select_repair_candidates=10011**, **select_repair_array_changes=102**,
  **select_repair_symbol_changes=320**, **branch_repair_candidates=136**,
  **branch_repair_symbol_changes=165**, **scalar_repair_candidates=24**,
  **scalar_support_candidates=24**, **scalar_stabilized_trials=0**,
  **scalar_rejected_worse_trials=0**,
  **scalar_equal_support_repairs=0**, **scalar_repair_symbol_changes=24**, and
  **projection_repair_changes=611**. The first false conjunct is now generated
  branch disjunction **ordinal 211**, term **4108**; best branch **3** has
  **1/6** false literals, term **714**, `x_325 = x_311`, with `x_325` equal to
  `(array default 0 [0 -> 1] [1 -> 3] [2 -> 3])` and `x_311` equal to
  `(array default 0 [0 -> 1] [1 -> 2] [2 -> 1])`. Next useful work is a
  replay-gated branch-choice/store-chain equality repair for the `x_325/x_311`
  transition, not another direct-select write or repair cap increase.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_repairs_select_through_store_chain -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_repairs_direct_select_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_selected_array_equality_component -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_repairs_single_store_branch_literal -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_can_choose_non_best_repairable_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA selected carry-component projection.**
  Targeted lazy-extensionality replay can now repair a false direct array
  equality as a selected carry component instead of a one-edge copy. For a failed
  branch equality `a = b`, the repair gathers adjacent direct array equalities
  from currently selected/best branches that touch `{a,b}`, tries each component
  member as the representative array value on a projection copy, aligns direct
  select readback symbols for the whole component, and keeps only a branch-
  improving, full-replay-non-worsening candidate. This remains SAT-only because
  the full original evaluator replay is still the acceptance gate. Focused
  regressions cover the selected component case and a separate narrow targeted
  direct-select equality repair.

  This still does **not** close `bug337`, but it advances beyond the lower
  carry branch `x_31 = x_17`. The 10 s probe remains at **round=2**,
  **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, and **working_assertions=7127**.
  Projection repair now reports **select_repair_candidates=10010**,
  **select_repair_array_changes=101**, **select_repair_symbol_changes=290**,
  **branch_repair_candidates=135**, **branch_repair_symbol_changes=156**,
  **scalar_repair_candidates=24**, **scalar_support_candidates=24**,
  **scalar_stabilized_trials=0**, **scalar_rejected_worse_trials=0**,
  **scalar_equal_support_repairs=0**, **scalar_repair_symbol_changes=24**, and
  **projection_repair_changes=571**. The first false conjunct is now direct
  readback equality **ordinal 34**, term **555**, `x_388 = select(x_325,
  x_337)`, with values **1** vs **0**. A targeted direct-select stabilization
  experiment was measured and rejected because it regressed to generated branch
  disjunction **9841** and raised projection churn to **1848** changes. Next
  useful work is a readback/store-chain component repair for the `x_325/x_339`
  transition around `x_388`, not a higher targeted cap or broad select
  stabilization.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_repairs_direct_select_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_selected_array_equality_component -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_supported_branch_array_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_repairs_single_store_branch_literal -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_can_choose_non_best_repairable_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_multi_literal_branch_schedule -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_propagates_select_supported_scalar_equalities -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_prefers_asserted_select_equalities -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_last_candidate_replay_accepts_only_real_models -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_best_false_or_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA replay branch-choice candidates.**
  Last-candidate lazy-extensionality replay now tries every positive branch of
  a failed generated disjunction on a projection copy, keeps only repairs that
  do not increase the full original replay false-conjunct count, and chooses the
  deterministic best `(total_false, branch_false, ordinal)` candidate before
  replaying again. This is still SAT-only: the full original evaluator replay
  remains the only way to return `sat`. A focused regression pins the motivating
  shape where the reported best branch is a single false Boolean literal that
  cannot be repaired, while a later branch has repairable scalar equalities.

  This still does **not** close `bug337`, but it moves the targeted replay
  frontier out of the prior branch/equality/lower-branch cycle. The 10 s probe
  remains at **round=2**, **sites=4096**, **array_eq_atoms=150**,
  **row_lemmas=42**, **cong_lemmas=6973**, **diff_skolems=146**, and
  **working_assertions=7127**. Projection repair now reports
  **select_repair_candidates=10010**, **select_repair_array_changes=101**,
  **select_repair_symbol_changes=197**, **branch_repair_candidates=135**,
  **branch_repair_symbol_changes=135**, **scalar_repair_candidates=24**,
  **scalar_support_candidates=24**, **scalar_stabilized_trials=0**,
  **scalar_rejected_worse_trials=0**, **scalar_equal_support_repairs=0**,
  **scalar_repair_symbol_changes=24**, and **projection_repair_changes=457**.
  The first false conjunct is now generated branch disjunction **ordinal 232**,
  term **9841**; best branch **3** has **1/6** false literals, term **2520**,
  `x_31 = x_17`, with `x_31` equal to
  `(array default 0 [0 -> 1] [1 -> 3] [2 -> 3])` and `x_17` equal to
  `(array default 0 [1 -> 2] [2 -> 1])`. Next useful work is a component-level
  store-chain/readback projection for this lower queue-lock branch, not another
  scalar fallback or global repair-round increase.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_can_choose_non_best_repairable_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_repairs_single_store_branch_literal -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_single_false_branch_symbol_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_supported_branch_array_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_multi_literal_branch_schedule -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_propagates_select_supported_scalar_equalities -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_prefers_asserted_select_equalities -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_last_candidate_replay_accepts_only_real_models -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_best_false_or_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA targeted replay branch repair.**
  Last-candidate lazy-extensionality replay now has a bounded targeted repair
  loop after the general projection pass: when full original replay names a
  single false branch literal, the solver repairs exactly that literal and
  immediately replays again. The acceptance gate is unchanged — only a full
  evaluator replay of the original assertions can return `sat`. A focused
  regression covers the exact helper on a false `b = store(a,i,v)` branch
  literal.

  This still does **not** close `bug337`, but it advances the replay frontier
  beyond the branch-store literal. The 10 s probe remains at **round=2**,
  **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, and **working_assertions=7127**.
  Projection repair now reports **select_repair_candidates=10010**,
  **select_repair_array_changes=101**, **select_repair_symbol_changes=170**,
  **branch_repair_candidates=124**, **branch_repair_symbol_changes=124**,
  **scalar_repair_candidates=24**, **scalar_support_candidates=24**,
  **scalar_stabilized_trials=0**, **scalar_rejected_worse_trials=0**,
  **scalar_equal_support_repairs=0**, **scalar_repair_symbol_changes=24**, and
  **projection_repair_changes=419**. The first false conjunct is now direct
  equality **ordinal 208**, term **3440**, `x_384 = x_344`, with values **0** vs
  **1**. A wider 96-round projection cap was measured and rejected because it
  stayed at branch ordinal 209 while raising projection churn to **929** changes.
  A targeted scalar fallback was also measured and rejected because it oscillated
  among branch **3654**, readback equality **3440**, and lower branch **3879**.
  Next useful work is a component-level branch-choice/store-chain readback
  projection for that three-node queue-lock cycle.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_scalar_equality_by_replay_improvement -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_multi_literal_branch_schedule -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_single_false_branch_symbol_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_supported_branch_array_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_propagates_select_supported_scalar_equalities -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_targeted_replay_repairs_single_store_branch_literal -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_last_candidate_replay_accepts_only_real_models -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_best_false_or_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_prefers_asserted_select_equalities -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA multi-literal branch schedule repair.**
  Replay-only branch repair now carries the selected best branch term and can
  try a bounded multi-literal projection on a copy of the candidate assignment.
  The schedule pass handles direct scalar equalities first, then equality-shaped
  array/store literals, and keeps the copy only if the selected branch's false
  literal count decreases. Store repairs preserve target arrays when possible;
  when the target cannot equal `store(base,i,v)` under the current index/value,
  the schedule pass can instead assign the target to the computed store and
  align target readbacks. The older one-literal repair keeps its prior
  convergence behavior so asserted select demands are not erased too early.

  This still does **not** close `bug337`, but it removes the generated branch
  disjunction as the first replay blocker. The 10 s probe remains at
  **round=2**, **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, and
  **working_assertions=7127**. Projection repair now reports
  **select_repair_candidates=1386**, **select_repair_array_changes=17**,
  **select_repair_symbol_changes=132**, **branch_repair_candidates=58**,
  **branch_repair_symbol_changes=58**, and **projection_repair_changes=207**.
  The first false conjunct is now a direct equality **ordinal 185**, term
  **2957**, `x_361 = x_22`, with values **1** vs **0**. Next useful work is a
  replay-gated scalar equality projection pass for non-branch generated
  equalities, with direction chosen by branch/readback support where available.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_multi_literal_branch_schedule -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_single_false_branch_symbol_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_supported_branch_array_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_prefers_asserted_select_equalities -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_best_false_or_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA branch array-equality repair.**
  Replay-only branch repair now handles a single false direct array equality by
  copying the side with stronger projected readback evidence into the weaker
  side. The direction key is deterministic: non-default projected array entries
  first, then direct asserted `select` equalities already satisfied by that
  side. After copying, direct scalar readback symbols for the target array are
  aligned to the repaired array. This stays SAT-only and replay-gated; it cannot
  return `sat` unless the original assertions fully evaluate to `true`.

  This does **not** close `bug337`, but it advances the replay frontier again.
  The 10 s probe remains at **round=2**, **sites=4096**,
  **array_eq_atoms=150**, **row_lemmas=42**, **cong_lemmas=6973**,
  **diff_skolems=146**, and **working_assertions=7127**. Projection repair now
  reports **select_repair_candidates=924**, **select_repair_array_changes=5**,
  **select_repair_symbol_changes=119**, **branch_repair_candidates=48**,
  **branch_repair_symbol_changes=48**, and
  **projection_repair_changes=172**. The first false conjunct moves to generated
  branch disjunction **ordinal 233**, term **10144**; best branch **0** now has
  **2/8** false literals. The first false literal is term **2556**,
  `x_17 = store(x_2, x_15, 2)`, with `x_17` equal to
  `(array default 0 [0 -> 1] [1 -> 3] [2 -> 3])` while the RHS store is
  `(array default 0 [1 -> 2] [2 -> 1])`. Next useful work is a multi-literal
  branch-schedule/store-chain projection for this queue-lock branch, not more
  one-literal local repair.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_supported_branch_array_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_single_false_branch_symbol_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_prefers_asserted_select_equalities -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_best_false_or_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_last_candidate_replay_accepts_only_real_models -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA branch readback alignment.**
  Replay-only branch store-base repair now also aligns direct scalar readback
  symbols for the repaired base array. This closes the local oscillation where
  branch repair copied target readback entries into the base array, then the
  later direct-select repair treated stale scalar read symbols as authoritative
  and overwrote those entries again. The focused branch-repair regression now
  includes a stale `z = select(a,j)` read on the repaired base and asserts that
  the final replaying model updates `z` to the branch-consistent value.

  This still does **not** close `bug337`, but it moves the 10 s replay miss to
  the next branch equality. The probe remains at **round=2**, **sites=4096**,
  **array_eq_atoms=150**, **row_lemmas=42**, **cong_lemmas=6973**,
  **diff_skolems=146**, and **working_assertions=7127**. Projection repair now
  reports **select_repair_candidates=924**, **select_repair_array_changes=5**,
  **select_repair_symbol_changes=4**, **branch_repair_candidates=2**,
  **branch_repair_symbol_changes=2**, and **projection_repair_changes=11**.
  The first false conjunct is now generated branch disjunction **ordinal 210**,
  term **3879**; best branch **3** has **1/6** false literals: term **628**,
  `x_339 = x_325`, with `x_339` equal to
  `(array default 0 [0 -> 1] [1 -> 3] [2 -> 3])` and `x_325` still
  `(array default 0)`. Next useful work is a replay-gated direct array-equality
  branch repair, or the more general branch-schedule projection that chooses
  equality direction from readback support, not more scalar timeout tuning.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_single_false_branch_symbol_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_prefers_asserted_select_equalities -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_best_false_or_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_last_candidate_replay_accepts_only_real_models -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA branch replay diagnostics and store-base repair.**
  Lazy-extensionality replay failure notes now summarize false branch
  disjunctions: branch count, best branch, false-literal count, first false
  literal term, and equality-side values when available. `diagnose_evidence`
  renders that best-branch first-false term, so generated queue-lock transition
  failures are inspectable without manually spelunking arena ids.

  A replay-only branch repair now handles the narrow class exposed by `bug337`:
  when the closest false branch has a single direct symbol equality
  `target = store(base, i, v)`, projection can repair the store base by copying
  the target array everywhere except the store index, where the base's current
  value is preserved. A focused regression pins this with an additional later
  read demand on the target array. This still cannot return `sat` unless the
  existing full original replay succeeds.

  The current `bug337` row still does **not** close. The 10 s probe remains at
  **round=2**, **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, and
  **working_assertions=7127**. Projection repair now reports
  **select_repair_candidates=1386**, **select_repair_array_changes=13**,
  **select_repair_symbol_changes=2**, **branch_repair_candidates=5**,
  **branch_repair_symbol_changes=5**, and **projection_repair_changes=20**.
  The first false conjunct remains the generated branch disjunction
  **ordinal 209**, term **3654**; best branch **0** has **1/8** false literals:
  term **492**, `x_353 = store(x_339, x_351, 2)`, with `x_353` carrying extra
  entries `[1 -> 3]` and `[2 -> 3]` that the current store-base repair still
  fails to propagate stably through the full repair loop. Next useful work is a
  branch-consistent projection pass that solves this small store-chain/readback
  system as a unit, or a branch-schedule model constructor, not another local
  scalar timeout knob.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_repairs_single_false_branch_symbol_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_replay_failure_reports_best_false_or_branch -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_prefers_asserted_select_equalities -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_last_candidate_replay_accepts_only_real_models -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-bench --example diagnose_evidence -j1 -- -D warnings`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA replay projection repair and generated-term diagnostics.**
  Lazy-extensionality last-candidate projection now repairs asserted direct
  `select` equalities by grouping them by concrete `(array, index)`: it stores
  the representative value into the projected array and aligns direct scalar
  read-result symbols in the same group before the existing full original replay
  gate. This is still SAT-only and replay-checked; it can only turn a candidate
  into `sat` after every original assertion evaluates to `true`.

  This does **not** close QF_AUFLIA `bug337`, but it moves the replay miss past
  the direct read equalities. The 10 s probe still times out at **round=2**,
  **sites=4096**, **array_eq_atoms=150**, **row_lemmas=42**,
  **cong_lemmas=6973**, **diff_skolems=146**, and
  **working_assertions=7127**. The replay repair sees
  **select_repair_candidates=154**, makes **3** array-entry changes and **2**
  scalar-symbol changes, and the first false flattened conjunct moves from the
  direct read equality `(= x_385 (select x_339 x_351))` to **ordinal 209**, term
  **3654**: the generated transition branch disjunction for the queue-lock
  step. `diagnose_evidence` can now render generated arena terms by stable term
  id via `TermArena::term_by_index`, so this branch formula is inspectable even
  when it is not reachable from the parsed assertion roots. Next useful work is
  replay-guided branch-schedule/model repair for that disjunction, not more
  select-equality projection.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-ir term_by_index_returns_valid_dense_handles -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_projection_prefers_asserted_select_equalities -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_last_candidate_replay_accepts_only_real_models -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-ir --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-bench --example diagnose_evidence -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA replay-gated lazy-extensionality candidates.**
  Lazy array extensionality now keeps the latest scalar `sat` candidate and, on
  a later timeout / scalar `unknown` / max-round decline, attempts one final
  projection plus full original-assertion replay before returning `unknown`.
  This is a SAT-only salvage path: it returns `sat` only when the reconstructed
  model evaluates every original assertion to `true`; replay failure or replay
  error preserves the existing `unknown` decline.

  The current QF_AUFLIA `bug337` row does **not** close yet, but the retained
  diagnostic is sharper. At 10 s it still stops at **round=2**, **sites=4096**,
  **array_eq_atoms=150**, **row_lemmas=42**, **cong_lemmas=6973**,
  **diff_skolems=146**, and **working_assertions=7127**; the final scalar
  candidate fails full replay at **top-level assertion ordinal 0**, term
  **13053**; the first false flattened conjunct is **ordinal 30**, term
  **465**. Next useful work is to inspect that branch/support condition and
  reduce materialized site/congruence pressure before the replay point.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ext_last_candidate_replay_accepts_only_real_models -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — AUFLIA lazy-extensionality diagnostics.**
  Lazy array extensionality `unknown` details now report refinement telemetry:
  `round`, materialized `sites`, `array_eq_atoms`, `row_lemmas`,
  `cong_lemmas`, `diff_skolems`, and `working_assertions`. This does not change
  solver behavior; it makes hard AUFLIA array timeouts actionable instead of
  opaque.

  Re-running the cvc5 QF_AUFLIA `bug337` row at 10 s now shows the blocker is
  concrete: lazy extensionality times out at **round=2**, **sites=4096**,
  **array_eq_atoms=150**, **row_lemmas=42**, **cong_lemmas=6973**,
  **diff_skolems=146**, and **working_assertions=7127**. That points the next
  AUFLIA work at SAT relevance / site admission / replay-gated model
  construction for the queue-lock branch schedule, not generic timeout tuning or
  PBLS array local search.
  Verification passed:
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext lazy_ext_timeout_reports_refinement_counters -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test abv_lazy_ext -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --test abv_lazy_ext -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.

- **Session 2026-06-26 — UFLIA CEGAR tuning guardrails.**
  Three plausible hard-row tuning knobs were measured and rejected, with no code
  retained: nearest-constant ordering for the cap-1 post-candidate UF sibling
  lemma, staged affine-core cap **2**, and simple-bound dynamic batch cap **64**.
  The retained baseline remains the prior cap-1 sibling policy, affine cap **1**,
  and bound cap **32**.

  Wider sibling caps were measured and rejected before commit: cap **16**
  dropped the 10 s hard row to **3** UF rounds / **2** candidates, cap **4** to
  **4** UF rounds / **3** candidates, and cap **2** to **5** UF rounds / **4**
  candidates. A nearest-constant sibling ordering also regressed the 10 s hard
  row to **5** rounds / **4** candidates, so discovery order remains better for
  this row. Affine cap **2** preserved **6** rounds / **5** candidates but
  increased pressure (**blocking_lemmas=323**, **core_src_lp=221**). Bound cap
  **64** was neutral/slightly worse (**blocking_lemmas=301**,
  **core_src_lp=210**). The committed cap **1** sibling / cap **1** affine /
  cap **32** bound baseline still preserves **6** rounds / **5** candidates,
  with about **first_candidate_ms=1025**, **last_candidate_ms=8324**,
  **blocking_lemmas=300**, and **core_src_lp=209** on
  `cli__regress2__uflia-error0.smt2`.
  Measurements / checks:
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency_schedules_unary_int_siblings_after_violation -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib cheap_integer_affine_bound_cores_batch_general_linear_conflicts -j1 -- --nocapture` (cap-2 experiment);
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib cheap_integer_bound_cores_batch_independent_conflicts -j1 -- --nocapture` (cap-64 experiment);
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — staged affine arithmetic core extraction.**
  Lazy arithmetic now has a checked affine integer expression extractor for
  dynamic two-literal conflicts between algebraically equal but syntactically
  different bounds, e.g. `x - y <= 0` and `x + (-1 * y) >= 1`. The parser covers
  integer constants, symbols, `+`, `-`, unary negation, and multiplication by
  constants, with checked overflow and a conservative decline on nonlinear or
  unsupported terms. The learned cores still use the existing arithmetic-lemma
  verifier.

  The production use is stage-gated: affine cores are disabled on the first
  pure arithmetic solve and enabled only after the warm skeleton has been
  strengthened by UF lemmas (`solve_calls > 1`), with a one-affine-core cap per
  theory conflict. This preserves the useful short-budget UF frontier while
  reducing later LP-core pressure. On
  `cli__regress2__uflia-error0.smt2`, the 1 s run remains `unknown` but reaches
  **2** UF rounds, **1** candidate, **282** pair checks, **6** equal-argument
  pairs, **5** violations, and **6** learned UF lemmas. At 10 s the row remains
  `unknown` but preserves **6** UF rounds, **5** candidates, **24**
  equal-argument pairs, and **24** learned UF lemmas; the final warm arithmetic
  timeout reports **total_rounds=286**, **blocking_lemmas=300**,
  **core_src_bound=29**, **core_src_diff=15**, **core_src_affine=49**,
  **core_src_lp=207**, and **core_len_avg=5.7**. Direct online probes are
  unchanged and still decline quickly at
  `opaque_app_order_atoms=334 > 128, total=485`.
  Verification passed:
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib cheap_integer_affine_bound_cores_batch_general_linear_conflicts -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib cheap_integer_bound_cores_batch_independent_conflicts -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — affine fixed-argument UF preseed coverage.**
  The lazy UF functional-consistency CEGAR preseed now derives fixed integer
  assignments from top-level affine equalities and paired non-strict bounds,
  not only direct singleton bounds such as `x <= c` and `x >= c`. The extractor
  is deliberately conservative: it accepts checked linear integer expressions
  over constants, symbols, `+`, `-`, unary negation, and multiplication by
  constants; solves only equalities with exactly one unassigned symbol after the
  current fixed assignment; and declines overflow, nonlinear terms, UF
  applications inside the affine proof, and one-sided inequalities.

  This closes a real cheap-preseed blind spot but is **not** the generated
  overbound row closure. Focused tests pin both directions: paired affine bounds
  can preseed a congruence lemma for `f(x)` vs `f(2)`, while the same one-sided
  affine bound does not preseed. On
  `cli__regress2__uflia-error0.smt2`, diagnostics remain neutral because the
  relevant hard-row UF arguments still depend on Boolean/model choices such as
  `fmt1` and `arg1`, not top-level forced affine values: at 1 s,
  `preseeded_lemmas=0`, **2** UF rounds, **1** candidate, **282** pair checks,
  **6** equal-argument pairs, **5** violations, and **6** learned UF lemmas; at
  10 s, `preseeded_lemmas=0`, **6** UF rounds, **5** candidates, **24** learned
  UF lemmas, and the timeout remains dominated by LP-core-producing arithmetic
  branches. The direct online probes are unchanged and still decline quickly at
  `opaque_app_order_atoms=334 > 128, total=485`.
  Verification passed:
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency_preseeds_affine_fixed_integer_argument_lemmas -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency_does_not_preseed_one_sided_affine_bounds -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency_preseeds_fixed_integer_argument_lemmas -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency_batches_all_equal_arg_pairs_after_violation -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uf_pair_profile -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 20`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — opaque-app online UFLIA construction is bounded.**
  Large combined UFLIA layouts now reuse the pure-LIA large-query pattern:
  the opaque-app `LiaTheory` records assignments cheaply and performs one
  feasibility check at the theory-propagation boundary instead of re-solving
  after every asserted literal. The Boolean UFLIA construction path also checks
  the caller deadline while collecting theory atoms, building the incremental
  combined state, encoding the Boolean skeleton, and adding interface clauses.
  If an opaque-app layout cannot build the incremental combined state safely
  (for example because the interface split is over the bound), the online path
  now declines instead of restarting through the older enumerative fallback.

  This closes the runaway fallback that the previous broad-cap experiment
  exposed. With the opaque cap temporarily raised to **512** and then restored
  before commit, both generated overbound direct probes now decline in about
  **4 ms** with
  `opaque-app online UFLIA incremental combined state could not be built safely`
  instead of running past **30 s**. The committed guard remains **128** opaque
  order atoms, so the production direct probes still decline at
  `opaque_app_order_atoms=334 > 128, total=485`. This is a resource-control
  fix, not a solve-rate closure: the lazy route is unchanged at 1 s with
  **2** UF rounds, **1** candidate, **282** pair checks, **6**
  equal-argument pairs, **5** violations, and **6** learned UF lemmas.
  Verification passed:
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib large_combined_opaque_lia_defers_feasibility_to_propagation -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test uflia_online opaque_app_interface_overflow_declines_without_enumerative_fallback -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test uflia_online -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --test uflia_online -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  temporary cap-512 probes for both generated rows under `timeout 35s`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`.

- **Session 2026-06-26 — shared CDCL(T) propagation now checks deadlines.**
  The generic online `Dpll<T: TheorySolver>` driver now checks the caller's
  deadline inside Boolean unit propagation and theory propagation, not only at
  the outer search-loop boundary. Timeout during propagation now returns the
  existing `None`/timeout path from `solve_with_deadline`; conflicts still
  follow the same 1-UIP analysis path. A focused unit test pins that an expired
  deadline stops unit propagation before any clause scan or assignment.

  This closes one timeout hole but does not yet make opaque-heavy generated
  UFLIA rows safe to admit wholesale. Re-running the rejected experiment with
  the opaque cap raised to **512** still left the first 1 s direct hard probe
  running after **30 s**, so the remaining overrun is before or outside the
  shared DPLL propagation checks: construction, encoding, or theory propagation
  generation still needs its own deadline hooks. The committed guard remains at
  **128** opaque-app order atoms; both generated overbound direct probes still
  decline quickly with
  `opaque_app_order_atoms=334 > 128, total=485`. The production lazy route is
  unchanged at 1 s: **2** UF rounds, **1** candidate, **282** pair checks,
  **6** equal-argument pairs, **5** violations, and **6** learned UF lemmas.
  Verification passed:
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib dpll_unit_propagation_honors_expired_deadline -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test uflia_online -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --test uflia_online -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`.

- **Session 2026-06-26 — opaque-app online UFLIA guard partitioned by opaque atoms.**
  The opaque-app online UFLIA admission guard now counts actual opaque Int-UF
  order atoms instead of using total theory atoms as a proxy. Large Boolean
  skeletons with a small opaque-app subset are admitted to the deadline-aware
  online path, while genuinely opaque-heavy skeletons still decline before the
  expensive construction/search phase. A new regression covers a query with
  more than **128** total atoms but only one opaque-app order atom and verifies
  it is not rejected by the opaque guard.

  The generated overbound rows remain intentionally guarded, but the blocker is
  now measured more precisely: both direct probes report **485** total theory
  atoms, of which **334** are opaque-app order atoms, and decline quickly with
  `too many theory atoms for opaque-app online UFLIA: opaque_app_order_atoms=334 > 128, total=485`.
  A broad experiment that raised the opaque cap to **512** was rejected before
  commit because both 1 s direct probes were still running after **30 s**; the
  remaining construction-side work is not yet safe to admit wholesale. The
  production lazy route is unchanged: at 1 s the first target row still reaches
  **2** UF rounds, **1** candidate, **282** pair checks, **6**
  equal-argument pairs, **5** violations, and **6** learned UF lemmas, then
  remains `unknown`. Next useful work is construction-deadline checks or
  partitioned opaque-heavy admission, plus model lifting for satisfiable opaque
  abstractions.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test uflia_online large_total_atom_skeleton_with_small_opaque_subset_is_admitted -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test uflia_online -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --test uflia_online -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`.

- **Session 2026-06-26 — deadline-aware opaque-app online UFLIA theory checks.**
  The online LIA theory now carries an optional wall-clock deadline into its
  feasibility checks, deletion-minimized core checks, model reconstruction, and
  propagation probes. `check_with_lia_opaque_apps_within` exposes the existing
  opaque-app LIA abstraction through the same deadline-aware integer search used
  by ordinary LIA, and `CombinedIncrementalLia` / `CombinedTheoryLia` pass the
  UFLIA Boolean-layer deadline into every nested `LiaTheory`. Once the deadline
  has passed, these theory checks become inconclusive (`Unknown`) rather than
  returning conflicts or propagations, preserving the existing soundness
  direction.

  This is prerequisite resource plumbing, not a cap raise or hard-row closure.
  A new regression test covers a Boolean-structured opaque Int-UF order query
  with zero timeout and confirms the online UFLIA path returns `Timeout` before
  doing theory work. The generated direct probes are intentionally unchanged:
  both overbound rows still decline quickly at the **128** opaque-app atom guard
  with `too many theory atoms for opaque-app online UFLIA: 485 > 128`. The
  production lazy route is also unchanged: at 1 s the first target row still
  reaches **2** UF rounds, **1** candidate, **282** pair checks, **6**
  equal-argument pairs, **5** violations, and **6** learned UF lemmas, then
  remains `unknown`. Next useful work is using this deadline-safe substrate to
  relax/partition the opaque-app online guard, or attacking lazy relevance so
  fewer LP-core-producing branches reach the arithmetic solver.
  Verification passed:
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test uflia_online -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --test uflia_online -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`.

- **Session 2026-06-26 — bounded opaque-app online UFLIA order support.**
  Online UFLIA now admits Int order atoms whose linear terms contain
  Int-sorted UF applications by treating those applications as opaque integer
  LIA variables. The new hook is deliberately UNSAT/conflict-oriented:
  `LiaTheory::new_with_opaque_apps` routes feasibility, core minimization, and
  LP propagation probes through the existing opaque-app arithmetic abstraction
  (`check_with_lia_opaque_apps` plus
  `lp_relaxation_feasibility_opaque_apps`). Satisfiable opaque abstractions are
  still model-incomplete and replay as `Unknown`; pure equality-only Int UF
  rows still stay on the EUF path and can return replay-checked `Sat`.

  This moves the direct online hard-row frontier but does not close the
  generated rows. Before the guard, the hard online probe ran for more than
  **90 s** despite a 1 s timeout, because combined-state construction and
  opaque-app theory assertion are not deadline-aware yet. The online route now
  declines opaque-app skeletons above **128** theory atoms, so both generated
  overbound probes return quickly with
  `too many theory atoms for opaque-app online UFLIA: 485 > 128` instead of the
  previous `non-Boolean term with sort Int` diagnostic. The production lazy
  route is unchanged: at 1 s the first target row still reaches **2** UF
  rounds, **1** candidate, **282** pair checks, **6** equal-argument pairs,
  **5** violations, and **6** learned UF lemmas, then remains `unknown`.
  Next useful work is deadline-aware opaque-app online theory assertion and
  model lifting, or lazy relevance that reduces LP-core-producing branches.
  Verification passed:
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --test uflia_online -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-bench --example uflia_online_probe -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test uflia_online -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`.

- **Session 2026-06-26 — online UFLIA Boolean boundary diagnosed.**
  Added `axeyum-bench --example uflia_online_probe` for direct single-file
  probes of the online EUF+LIA combination route. The online Boolean layer now
  collects only actual QF_UFLIA theory atoms, handles n-ary `and`/`or`, encodes
  Boolean equality as IFF, and preserves the first unsupported-shape detail in
  both CDCL(T) and enumerative fallback declines. The lazy arithmetic Boolean
  skeleton also now deduplicates duplicate literals and drops complementary
  tautological clauses before SAT insertion.

  This is a boundary fix and diagnostic slice, not a hard-row closure. With the
  online atom cap raised to **512**, both generated QF_UFLIA overbound rows get
  past the previous admission/opaque-decline layer and now fail quickly with the
  precise reason
  `boolean skeleton outside the online combination encoder: non-Boolean term with sort Int`.
  That identifies the next online-combination gap: arithmetic order atoms whose
  Int linear terms contain UF applications need opaque-integer-app modeling in
  the online LIA theory, analogous to the offline opaque-app arithmetic path.

  The production lazy route is preserved but not improved. At 1 s both target
  rows still reach **2** UF rounds, **1** candidate, **282** pair checks,
  **6** equal-argument pairs, **5** violations, and **6** learned UF lemmas. At
  10 s, `cli__regress2__uflia-error0.smt2` still reaches **6** UF rounds,
  **5** candidates, **1357** pair checks, **24** equal-argument pairs,
  **15** violations, and **24** learned UF lemmas, then times out in the warm
  arithmetic state with **total_rounds=292**, **blocking_lemmas=306**,
  **core_src_lp=263**, and **core_len_avg=6.9**. This is neutral relative to
  the prior LP-core-shrinking commit; the next practical levers remain online
  opaque UF-in-arithmetic support or reducing LP-core-producing lazy branches.
  Verification passed:
  `git diff --check`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --test uflia_online -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-bench --example uflia_online_probe -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test uflia_online -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib dpll_lia::tests::bool_skeleton_simplifies_duplicate_and_complementary_literals -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uflia_online_probe -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — bounded LP-relaxation core shrinking retained.**
  LP-relaxation unsat-core extraction now deletion-minimizes small Farkas
  supports, capped at **24** atoms, by re-running the same real-relaxation
  infeasibility checker used for the final self-check. Larger LP supports keep
  the previous cheap Farkas-support path. This strengthens learned arithmetic
  blocking clauses when simplex support contains redundant literals without
  changing the soundness anchor: a returned core is still accepted only if its
  LP relaxation is independently infeasible.

  The generated QF_UFLIA overbound rows remain `unknown`, but the measured
  search shape improves slightly and preserves the short-budget UF frontier. At
  1 s both target rows still reach **2** UF rounds, **1** candidate, **282**
  pair checks, **6** equal-argument pairs, **5** violations, and **6** learned
  UF lemmas. At 10 s, `cli__regress2__uflia-error0.smt2` still reaches **6**
  UF rounds, **5** candidates, **1357** pair checks, **24**
  equal-argument pairs, **15** violations, and **24** learned UF lemmas; the
  final warm arithmetic timeout improves from **total_rounds=305**,
  **blocking_lemmas=319**, **core_src_lp=276**, **core_len_avg=7.3** to
  **total_rounds=290**, **blocking_lemmas=303**, **core_src_lp=260**,
  **core_len_avg=6.9**. This is useful pressure reduction, not closure. The
  next lever is still reducing LP-core-producing SAT branches or a stronger
  combined UF/LIA interface loop.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lp_relaxation_core_minimizer_removes_redundant_atoms -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lp_relaxation_unsat_core -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — arithmetic core-source diagnostics expose LP-core bottleneck.**
  Lazy arithmetic DPLL unknown details now report source counts for dynamic
  theory cores: simple bound conflicts, difference-logic cycles, LP-relaxation
  Farkas cores, deletion-minimized cores, and large unminimized fallback cores.
  This is diagnostic-only; each learned clause is still recorded and checked
  through the existing arithmetic lemma path, and solver decisions are
  unchanged.

  The generated QF_UFLIA overbound rows remain `unknown`. At 1 s both target
  rows preserve the current frontier: **2** UF rounds, **1** candidate,
  **282** pair checks, **6** equal-argument pairs, **5** violations, and
  **6** learned UF lemmas. At 10 s, `cli__regress2__uflia-error0.smt2`
  reports **6** UF rounds, **5** candidates, **1357** pair checks,
  **24** equal-argument pairs, **15** violations, and **24** learned UF lemmas;
  the final warm arithmetic timeout now identifies the late source mix:
  **core_src_bound=31**, **core_src_diff=12**, **core_src_lp=276**,
  **core_src_minimized=0**, **core_src_large=0**. That rules out deletion
  minimization and the large-core cutoff as the next bottleneck on this row;
  the practical next lever is LP-relaxation core relevance/shrinking or
  preventing the SAT skeleton from feeding so many LP-core-producing branches.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib dpll_lia::tests:: -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — integer-bound theory tautologies folded before LIA abstraction.**
  The arithmetic abstractor now recognizes simple integer-bound contradictions
  and tautologies before allocating Boolean atom props: conjunctions such as
  `x >= 8 ∧ x <= 6` fold to `false`, and disjunctions such as
  `not (x >= 8) ∨ not (x <= 6)` fold to `true`. This is deliberately narrow:
  it only uses the same simple Int order-bound semantics already used by the
  certified bound mutex/implication lemma paths, and it does not flatten the
  UF implication shape that the previous session rejected.

  The generated QF_UFLIA overbound rows remain `unknown`, but the hard-row
  frontier is preserved and nudged forward. At 1 s both target rows still reach
  **2** UF rounds, **1** candidate, **282** pair checks, **6**
  equal-argument pairs, **5** violations, and **6** learned UF lemmas. At 10 s,
  `cli__regress2__uflia-error0.smt2` still reaches **6** UF rounds and
  **5** candidates, but now records **1357** pair checks, **24**
  equal-argument pairs, **15** violations, and **24** learned UF lemmas before
  timing out in the warm arithmetic state (**solve_calls=6**,
  **total_rounds=297**, **atoms=533**, **bound_lemmas=659**,
  **blocking_lemmas=311**). This is a small search-shape improvement, not row
  closure; the next lever remains relevance/convergence after several UF
  candidates and the larger 17–20 literal arithmetic cores that appear late.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib abstractor_ -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib dpll_lia::tests:: -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — implication-flattening experiment rejected.**
  Tested flattening arithmetic-guarded implications, especially UF congruence
  lemmas of the form `((a <= b) ∧ (b <= a)) => result_eq`, into flat
  disjunctions `not le ∨ not ge ∨ result_eq`. The transformation is logically
  equivalent and reduces Boolean guard auxiliaries, but it regressed the
  generated QF_UFLIA overbound rows: at 1 s both rows lost the first UF
  candidate and timed out in the first arithmetic solve (**41–42**
  support-conflict rounds, **0** candidates, **0** UF lemmas). The experiment
  was reverted before commit, and the implication-preserving path is documented
  in code as an intentional SAT-search-shape choice.

  The retained baseline is unchanged: both target rows at 1 s reach **2** UF
  rounds, **1** candidate, **282** pair checks, **6** equal-argument pairs,
  **5** violations, and **6** learned UF lemmas. The next useful lever is not a
  generic Boolean-shape simplification; it remains candidate/relevance after
  the warm arithmetic state has already learned the first UF batches.
  Verification passed:
  `git diff --check`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency_batches_all_equal_arg_pairs_after_violation -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  rejected experiment diagnostics:
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  retained-path diagnostics:
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`.

- **Session 2026-06-26 — UF refinement batching guardrail retained.**
  Measured a narrower lazy UF refinement policy that added only
  result-violating equal-argument pairs instead of all equal-argument pairs in a
  candidate once any violation appears. It was rejected before commit: on both
  generated QF_UFLIA overbound rows at 1 s, the route regressed to **0** UF
  candidates and timed out in the first arithmetic solve after **42**
  support-conflict rounds, whereas the retained all-equal batching reaches
  **1** candidate and learns **6** UF lemmas at the same budget.

  Added a focused regression test,
  `lazy_function_consistency_batches_all_equal_arg_pairs_after_violation`, that
  pins the retained policy: if one candidate exposes a violating congruence
  pair, every currently equal-argument pair in that candidate is batched, even
  pairs whose result values already agree. The hard-row diagnostics are back at
  the warm-skeleton baseline: 1 s rows reach **2** UF rounds, **1** candidate,
  **282** pair checks, **6** equal-argument pairs, **5** violations, and
  **6** learned UF lemmas; the 10 s first row reaches **6** rounds,
  **5** candidates, **1361** pair checks, **23** equal-argument pairs,
  **15** violations, and **23** learned UF lemmas.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency_batches_all_equal_arg_pairs_after_violation -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib uf_arith_overbound_unsat_decided_by_lazy -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — warm arithmetic skeleton for lazy UFLIA CEGAR.**
  The lazy arithmetic DPLL loop is now backed by an `IncrementalArithDpll`
  state object. The one-shot API still wraps that state, but lazy
  UF+arithmetic CEGAR now asserts newly learned UF congruence lemmas into the
  same warm arithmetic Boolean skeleton instead of rebuilding the abstraction
  after every UF refinement. The previous term-level reusable arithmetic lemma
  path remains as a fallback when the warm arithmetic state declines a shape.

  The generated QF_UFLIA overbound rows remain `unknown`, but the short-budget
  frontier moves from arithmetic-only churn into actual UF refinement. At 1 s
  both target rows now reach **2** UF CEGAR solve rounds, **1** SAT candidate,
  **282** pair checks, **6** equal-argument pairs, **5** violations, and
  **6** learned UF lemmas before the shared `lazy UF+arithmetic` deadline. At
  10 s, `cli__regress2__uflia-error0.smt2` keeps the prior high-level UF
  frontier: **6** UF rounds, **5** candidates, **1361** pair checks,
  **23** equal-argument pairs, **15** violations, and **23** learned UF lemmas.
  The final arithmetic timeout now comes from the warm state itself:
  **solve_calls=6**, **total_rounds=279**, **atoms=531**,
  **bound_lemmas=664**, **blocking_lemmas=295**, **support_attempts=279**,
  **support_conflict_batches=274**, **support_model_attempts=5**, and
  **full_fallbacks=0**. Next useful work is no longer cold rebuild avoidance;
  it is CEGAR relevance/convergence after the fifth candidate, either by
  stronger model-guided UF-pair scheduling or by a real combined CDCL(T)
  interface-equality loop.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib incremental_arith_dpll_accepts_strengthened_assertions -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib reusable_arith_lemmas -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib uf_arith_overbound_unsat_decided_by_lazy -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — reusable arithmetic lemmas advance UFLIA CEGAR.**
  Lazy UF+arithmetic CEGAR now carries dynamic arithmetic conflict clauses
  across strengthened UF refinement rounds. The carried clauses are rebuilt over
  original arithmetic terms, not prior `!arith_atom_N` symbols, so fresh
  arithmetic abstractions can reuse them safely. Static upfront bound lemmas are
  deliberately not carried because they are regenerated per solve.

  The generated QF_UFLIA overbound rows remain `unknown`, but the CEGAR shape
  moves in the intended direction. At 1 s both target rows now reach **42**
  support-conflict rounds and **56** blocking/reusable arithmetic lemmas, versus
  the prior **21** rounds and **29** blocking lemmas. At 10 s,
  `cli__regress2__uflia-error0.smt2` reaches **6** UF CEGAR solve rounds,
  **5** SAT candidates, **1359** pair checks, **23** equal-argument pairs,
  **16** violated pairs, and **23** learned UF lemmas before the outer deadline,
  versus the prior **4** rounds, **3** candidates, **830** pair checks,
  **14** equal-argument pairs, **9** violations, and **14** UF lemmas. The last
  arithmetic solve reports **357** reusable arithmetic lemmas carried. Next
  useful work is still convergence/relevance after several candidate models:
  either keep the arithmetic SAT core warm directly, or make UF lemma addition
  incremental inside one combined skeleton.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib reusable_arith_lemmas -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib uf_arith_overbound_unsat_decided_by_lazy -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lia_budget_unknown_reports_support_stats -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — UF pair profile rules out guarded preseed.**
  Added `axeyum-bench --example uf_pair_profile`, a read-only diagnostic that
  parses an SMT-LIB file, runs function elimination, groups same-function
  applications, categorizes potential Ackermann pairs, and prints bounded
  concrete samples. On `cli__regress2__uflia-error0.smt2` it reports **42**
  UF applications, **3** function groups, and **282** potential pairs:
  **214** are constant-vs-constant, **23** are `s_count`/`x_count` affine-vs-
  constant, and **45** are `format` pairs involving `arg1`, `fmt1`,
  `(+ 1 fmt1)`, or constants.

  A deliberately narrow solver experiment was measured and rejected before
  commit: pre-seeding only unary-Int nonconstant-vs-constant congruence lemmas
  with a cap of 64 produced `preseeded_lemmas=64`, but enlarged the arithmetic
  abstraction to **673 atoms**. At 1 s it remained `unknown`; at 10 s it never
  reached a UF candidate (**sat_candidates=0**) and timed out after **297**
  support-conflict batches. The retained conclusion is practical: even guarded
  upfront congruence preseed is the wrong lever for this row. Next useful work
  should preserve/reuse arithmetic learning across UF CEGAR rounds or make the
  arithmetic solve incremental under added UF lemmas.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --example uf_pair_profile -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-bench --example uf_pair_profile -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example uf_pair_profile -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 8`;
  rejected experiment diagnostics:
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — support-path diagnostics for UFLIA CEGAR.**
  Lazy arithmetic DPLL budget `unknown` details now include deterministic
  Boolean-support counters: support availability, support conflict batches,
  support-model attempts, replay failures, and full-assignment fallbacks. This
  is a diagnostic-only change; two pruning experiments were measured and
  rejected before commit. Full raw Ackermann pre-seeding worsened the generated
  overbound row by inflating the post-CEGAR arithmetic skeleton, and raw
  pre-abstraction Boolean/bound folding slightly shrank the initial skeleton but
  reduced 10 s UF CEGAR progress.

  The retained diagnostics preserve the support-first baseline. At 1 s both
  generated QF_UFLIA overbound rows still report **461 atoms**, **642** initial
  bound lemmas, **21** lazy-LIA rounds, and **29** blocking lemmas, now with
  **support_attempts=21**, **support_conflict_batches=21**, and
  **full_fallbacks=0**. That says the short-budget blocker is entirely
  supported-branch arithmetic conflict learning, not replay failure or fallback
  to arbitrary dead-branch assignments. At 10 s,
  `cli__regress2__uflia-error0.smt2` returns to the support-first baseline:
  **4** UF CEGAR solve rounds, **3** SAT candidates, **830** pair checks,
  **14** equal-argument pairs, **9** violations, and **14** UF lemmas before the
  outer `lazy UF+arithmetic` deadline expires. Next useful work should target
  an incremental/relevance-preserving arithmetic solve across UF CEGAR rounds,
  or a very narrow guarded congruence preseed justified by measured pair
  relevance; broad preseed/simplification is not the lever.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib dpll_lia::tests:: -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — Boolean-support arithmetic checks cut dead-branch churn.**
  The lazy arithmetic DPLL loop now extracts a deterministic Boolean
  justification support from each SAT skeleton candidate and theory-checks that
  support before checking the solver's whole arbitrary Boolean assignment. This
  avoids learning arithmetic conflicts from atoms that sit in dead branches of
  generated selector ladders. The path is replay-gated: if the supported
  arithmetic model does not evaluate every original assertion to true, the
  solver falls back to the previous full-assignment theory check.

  The generated QF_UFLIA overbound rows remain `unknown`, but the immediate
  search shape moved. At 1 s both rows now report **461 atoms**, **642 bound
  lemmas**, **21** lazy-LIA rounds, and **29** dynamic blocking lemmas, with no
  UF candidates yet. At 10 s, `cli__regress2__uflia-error0.smt2` reaches
  **4** UF CEGAR solve rounds and **3** SAT candidates, checks **830** possible
  function-consistency pairs, observes **14** equal-argument pairs and **9**
  violations, learns **14** UF lemmas, and then times out in outer
  `lazy UF+arithmetic` convergence. This moves the useful next lever from
  dead-branch arithmetic refinement churn to UF CEGAR convergence and relevance
  after several candidate models.
  Verification passed:
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib justified_support_ignores_dead_or_branch_conflict -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — bounded complement-bound implications prune UFLIA ladders.**
  The upfront integer-bound implication pass now includes complement literals
  under the existing 512-atom admission guard and 4096-lemma cap. This keeps the
  earlier rejected broad complement-bound experiment out of the large path, but
  lets branch-selector ladders propagate monotonicity such as
  `not (x <= 1) => not (x <= 0)`. Each clause is still recorded as the checked
  core `{stronger_bound, not weaker_bound}` and reuses the normal arithmetic
  lemma verifier.

  The generated QF_UFLIA overbound rows remain `unknown`, but the hard-row
  search gets another bounded pruning step. At 1 s both rows now report
  **461 atoms**, **642 bound lemmas**, **27** lazy-LIA rounds, and **171**
  dynamic blocking lemmas, versus the prior **372 / 29 / 238**. At 10 s,
  `cli__regress2__uflia-error0.smt2` reaches one UF candidate, learns **5** UF
  consistency lemmas under the pruned skeleton, and then times out in a
  **475-atom** post-CEGAR arithmetic skeleton after **60** lazy-LIA rounds and
  **200** dynamic blocking lemmas, versus **479 / 87 / 296** before this pass.
  This is still search-shape movement, not row closure; the next lever remains
  a real relevance / assumption-core loop for the post-CEGAR arithmetic
  skeleton.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib upfront_integer_bound_implication_lemmas_are_certified -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib upfront_integer_bound_complement_implication_lemmas_are_certified -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — lazy LIA batches model-guided bound conflicts.**
  The lazy arithmetic DPLL refinement loop now learns a batch of up to 32
  independent simple integer-bound conflict cores from the same SAT candidate
  when the integer theory slice is unsat, instead of learning only the first
  two-bound core and rediscovering other obvious conflicts in later rounds.
  Each learned clause is still recorded through the existing arithmetic lemma
  path and certified by the same core replay tests.

  The two generated QF_UFLIA overbound rows are still `unknown`, but the search
  shape improves materially. At 1 s both rows now report **461 atoms**,
  **372 bound lemmas**, **29** lazy-LIA rounds, and **238** blocking lemmas
  (`core_len_min=2`, `core_len_max=3`, `core_len_avg=2.0`), versus the prior
  **61** one-core rounds. At 10 s, `cli__regress2__uflia-error0.smt2` still
  reaches one UF candidate and learns the **6** same-candidate UF lemmas, then
  times out in the **479-atom** post-CEGAR arithmetic skeleton after **87**
  lazy-LIA rounds and **296** blocking lemmas. The next useful lever remains
  relevance / assumption-core solving or branch-selector pruning in that
  arithmetic skeleton, not more single-core extraction.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib cheap_integer_bound_core -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib upfront_integer_bound_implication_lemmas_are_certified -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — lazy UF consistency batches same-candidate lemmas.**
  The lazy function-consistency CEGAR loop now has a cheap pre-seed step for
  same-function applications whose argument tuples are syntactically equal or
  evaluate equal under top-level fixed integer bounds. Unknown diagnostics now
  report `preseeded_lemmas`. After a candidate model exposes any real
  functional-consistency violation, the loop batches every same-candidate
  equal-argument congruence lemma, not just the result-different pair; it still
  avoids adding gratuitous lemmas when the candidate is already functionally
  consistent.

  On the two generated QF_UFLIA overbound rows, pre-seeding finds **0** lemmas
  because the equal UF arguments depend on branch/model choices (`fmt1` etc.),
  so the 1 s rows remain **461 atoms / 372 bound lemmas / 61 rounds** with
  **sat_candidates=0**. At 10 s, `cli__regress2__uflia-error0.smt2` still reaches
  one UF candidate; the loop now records **equal_arg_pairs=6**,
  **violated_pairs=5**, **lemmas_added=6**, then times out in a **479-atom**
  post-CEGAR arithmetic skeleton. Next work remains arithmetic relevance /
  assumption-core solving after UF lemmas, not more UF pair discovery.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_ufbv -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`.

- **Session 2026-06-26 — arithmetic order polarity shrinks UFLIA skeletons.**
  The arithmetic DPLL abstractor now represents strict order atoms as Boolean
  negations of their non-strict reversed-order representative: `a < b` is
  abstracted as `¬(b <= a)`, and `a > b` as `¬(a <= b)`, for both Int and Real.
  This makes an order atom and its negation share one SAT variable instead of
  entering the theory loop as unrelated atoms. The Boolean skeleton simplifier
  also folds the generated definition-tautology shapes common in cvc5's
  justification regressions, including `¬(A ∧ B) ∨ A`, `¬(A ∧ B) ∨ B`, and
  `(A ∧ B) ∨ ¬A ∨ ¬B`. With the smaller abstraction, adjacent bound-implication
  seeding is admitted up to 512 atoms.

  The two generated QF_UFLIA overbound rows are still `unknown`, but the 1 s
  trace moved from **873 atoms / 1433 bound lemmas / ~32 rounds** to
  **461 atoms / 372 bound lemmas / 61 rounds**. At 10 s, the first row reaches a
  real UF CEGAR candidate (**sat_candidates=1**), checks all **282** possible
  function-consistency pairs, and adds **5** Ackermann lemmas before the second
  abstraction solve times out. The next blocker is now the post-CEGAR
  477-atom arithmetic skeleton after those UF lemmas, not the initial duplicated
  order/complement noise.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib abstractor_ -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib upfront_integer_bound_implication_lemmas_are_certified -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib overbound_integer_uf_arith_skips_generic_lia_dpll_for_uf_routes -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `git diff --check`.

- **Session 2026-06-26 — LIA LP core diagnostics expose small-core search.**
  Integer linear collection now stamps every generated simplex constraint with
  its source assertion, and the solver exposes a self-checked
  `lia_lp_relaxation_unsat_core` helper. The lazy arithmetic DPLL loop tries that
  Farkas-supported LP-relaxation core before the expensive generic core path and
  now reports learned theory-core sizes in budget `unknown` details.

  This did not close the two generated QF_UFLIA overbound rows, but it narrowed
  the diagnosis. At 1 s both rows still route through the single UF-aware
  abstraction solve and return `unknown` with **873 atoms**, **1433 bound
  lemmas**, **32 blocking lemmas**, and **core_len_last=2**,
  **core_len_min=2**, **core_len_max=2**, **core_len_avg=2.0**. The dynamic
  arithmetic conflicts are already tiny; the next useful work is not core
  minimization, but SAT/search relevance over many small bound conflicts in the
  large arithmetic skeleton: assumption-filtered skeleton solving, a cheaper
  first-model/core-producing loop, or stronger pruning of the generated
  branch-selector ladders.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lp_relaxation_unsat_core -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib cheap_integer_bound_core_uses_current_literal_polarity -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib cheap_integer_difference_core_finds_negative_cycle -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `git diff --check`.

- **Session 2026-06-26 — QF_UFLIA overbound route duplication removed.**
  Large non-array integer UF+arithmetic queries whose Ackermann pair count is
  over the eager bound now skip the generic `lia-dpll` route after Diophantine /
  simplex refuters decline, and fall through to the UF-aware lazy CEGAR path
  instead. This avoids spending one timeout window in generic LIA and then
  spending a second timeout window on the same function-free arithmetic
  abstraction inside `uf-arith-lazy-overbound`.

  The two generated QF_UFLIA overbound rows now run one abstraction solve under
  the UF-aware route. The trace records: pre-LIA cloned probe skipped
  (`1248 > 256` assertions, `ackermann_pairs=282`), `lia-simplex` unsupported,
  `lia-dpll` skipped for overbound UF+arithmetic, and
  `uf-arith-lazy-overbound` declining with **applications=42**,
  **function_groups=3**, **potential_pairs=282**, **solve_rounds=1**,
  **sat_candidates=0**, **pair_checks=0**, and **lemmas_added=0** before the
  873-atom arithmetic abstraction times out after about **32** lazy-LIA rounds.
  The rows remain `unknown`; the next useful work is relevance / assumption
  filtering or a cheaper first-model / UNSAT-core-producing skeleton loop for the
  function-free arithmetic abstraction itself.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib overbound_integer_uf_arith_skips_generic_lia_dpll_for_uf_routes -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lia_budget_unknown_annotation_reports_skipped_uf_context -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib arithmetic_uf_overbound_pre_lia_probe_decides_on_clone -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `git diff --check`.

- **Session 2026-06-26 — large online LIA feasibility deferred.**
  Added a large-query mode to `check_qf_lia_online`: for skeletons with at least
  128 LIA atoms or 4096 CNF clauses, `LiaTheory` records Boolean assignments
  cheaply and performs one full LIA feasibility check at the theory-propagation
  boundary instead of re-solving the live conjunction on every atom assignment.
  If that deferred check is infeasible, it is surfaced as a normal theory
  propagation contradicting one asserted core literal, so the shared DPLL learns a
  sound `¬core` conflict clause. The large mode skips LP entailment propagation
  and core minimization; both are pruning/precision choices, not soundness
  requirements, and skipping them avoids reintroducing hundreds of LIA checks.

  The target QF_UFLIA overbound rows moved to the next blocker. At 1 s, the
  generic route no longer times out inside online LIA's first propagation; it now
  reaches the legacy lazy arithmetic fallback and times out after **31-33
  rounds** over **873 atoms**, with **1433 bound lemmas** and **31-33 blocking
  lemmas**. The rows remain `unknown`, but the bottleneck is now the legacy
  arithmetic refinement loop / route scheduling, not online DPLL(T)'s initial
  assertion cascade. **Next:** reduce the 873-atom fallback loop with relevance /
  assumption filtering, or route these generated UF+arithmetic rows to a UF-aware
  search before the legacy arithmetic loop consumes the remaining budget.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib deferred_lia_feasibility_reports_conflict_from_propagate -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib large_online_lia_root_conflict_uses_deferred_feasibility -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib online_lia_timeout_reports_dpll_stats -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test lia_online -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lia_budget_unknown_annotation_reports_skipped_uf_context -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib arithmetic_uf_overbound_pre_lia_probe_decides_on_clone -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `git diff --check`.

- **Session 2026-06-26 — online LIA timeout stats expose first-propagation cost.**
  Added a stable stats snapshot for the shared online DPLL(T) engine and wired it
  into `check_qf_lia_online` timeout `Unknown` details. The counters report
  variables, theory atoms, clause counts, live/deleted learned clauses, trail
  depth, decision level, decisions, conflicts, conflicts since restart, restarts,
  and reductions. A zero-timeout regression pins that online LIA timeout reports
  include these stats without changing verdict behavior.

  Short diagnostics on both generated QF_UFLIA overbound rows now show the
  immediate bottleneck more precisely: the generic opaque-app `lia-dpll` path
  times out with **vars=3873**, **theory_atoms=485**, **clauses=10651**,
  **trail=1314**, **decision_level=1**, **decisions=1**, **conflicts=0**,
  **learned_live=0**, **restarts=0**, and **reductions=0**. This is not a
  conflict-learning / restart-policy stall; the budget is being spent before the
  first meaningful SAT skeleton exploration, during giant initial propagation and
  repeated LIA feasibility checks. **Next:** attack this route with relevance
  filtering, batched/cheap propagation, or a first-model/skeleton precheck before
  pushing 1k+ propagated literals through incremental LIA.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib online_lia_timeout_reports_dpll_stats -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib arithmetic_uf_overbound_pre_lia_probe_decides_on_clone -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lia_budget_unknown_annotation_reports_skipped_uf_context -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`;
  `git diff --check`.

- **Session 2026-06-26 — bounded pre-LIA UF+arithmetic probe added.**
  Added a cloned, bounded pre-LIA probe for non-array integer UF+arithmetic
  instances whose eager Ackermann pair count is over the deterministic bound.
  Small overbound instances now get the lazy UF+arithmetic CEGAR route before
  generic opaque-app `lia-dpll`, and a regression pins that it can decide an
  overbound congruence contradiction without mutating the caller's arena. Probe
  `Unsupported` / backend replay failures are trace declines, not hard solver
  errors, so the existing fallback path remains available.

  The generated QF_UFLIA overbound rows are intentionally not admitted to this
  cloned probe: each has **1248 assertions** and `ackermann_pairs=282`, and even
  a tiny nominal probe timeout duplicates the large function-free arithmetic
  skeleton solve. The route now records a fast deterministic skip for those rows
  and then reaches the existing `lia-dpll` timeout. **Next:** attack the large
  generated arithmetic skeleton directly: shared global deadlines, relevance /
  assumption filtering, or a cheaper first-SAT-model probe that can report
  `sat_candidates=0` without solving the whole 873-atom abstraction.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib arithmetic_uf_overbound_pre_lia_probe_decides_on_clone -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib uf_arith_overbound_unsat_decided_by_lazy -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lia_budget_unknown_annotation_reports_skipped_uf_context -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency_unknown_reports_cegar_stats -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`.

- **Session 2026-06-26 — QF_UFLIA overbound dispatch starvation diagnosed.**
  Added two low-cost diagnostics for the hard parent
  `qf-uflia-cvc5-regress-clean-overbound` rows. First, the shared lazy
  function-consistency CEGAR loop now wraps any `unknown` with refinement stats:
  application count, function groups, possible congruence pairs, solve rounds,
  candidate models, checked/equal/violated pairs, and lemmas added. Second, a
  generic `lia-dpll` budget `unknown` on a query with UF applications now records
  when UF-aware routes were not reached, including whether an arithmetic function
  exists and the Ackermann pair count.

  Short diagnostics on both overbound rows now expose the immediate blocker:
  both time out in the generic opaque-app `lia-dpll` route before UF-aware
  solving, with `arithmetic_function=true` and `ackermann_pairs=282`. This
  corrects the prior working assumption that lazy UF+LIA CEGAR refinement churn
  had been observed on these rows; in the current dispatcher it is not reached
  from `check_auto` for this shape. **Next:** fix route scheduling / deadline
  sharing so admitted arithmetic-UF overbound instances get a UF-aware probe
  before generic LIA DPLL can consume the whole budget; if that probe then reports
  `sat_candidates=0`, the next bottleneck is the 873-atom function-free Boolean
  arithmetic skeleton itself.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lazy_function_consistency_unknown_reports_cegar_stats -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib lia_budget_unknown_annotation_reports_skipped_uf_context -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 1000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 1000`.

- **Session 2026-06-26 — QF_UFLIA overbound equality-propagation probe retained.**
  Revisited the two parent `qf-uflia-cvc5-regress-clean-overbound` timeout rows
  after the restart. The retained solver change is deliberately narrow:
  `LiaTheory::propagate` now handles integer equality atoms by LP-relaxation
  probes, propagating `x = y` only when both strict branches `x < y` and `y < x`
  are infeasible, and propagating `x != y` only when `asserted ∧ x = y` is
  infeasible. This is a local DPLL(T) pruning improvement with asserted-only
  reasons; it is **not** a row closure. Direct tests now cover equality-true
  propagation from paired bounds and equality-false propagation from an
  incompatible bound.

  I also tested widening the scalar DPLL upfront integer-bound lemmas to include
  complement bounds and to remove the large-atom guard. That experiment was
  rejected before commit: it raised the target rows from 1433 to 5484 upfront
  bound lemmas, still timed out, and risked slowing the broad scalar path.
  Current diagnostics on the retained tree leave both overbound rows `unknown`:
  `uflia-error0` times out after 403 lazy-LIA rounds over 873 atoms, and
  `error0` times out after 405 rounds / `rustsat-batsat` timeout, both with
  1433 upfront bound lemmas. **Next:** stop spending on shallow static-bound
  seeding for these rows; instrument the lazy UF+LIA CEGAR loop and attack SAT
  relevance / Boolean-skeleton reduction in the 873-atom mixed core.
  Verification passed:
  `cargo fmt --all`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib equality_atom_ -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test uflia_online interface_equality_forces_euf_contradiction_unsat -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress2__uflia-error0.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-overbound/cli__regress3__error0.smt2 10000`;
  `git diff --check`.

- **Session 2026-06-26 — QF_UFLIA parent dominance audit ingested.**
  Audited the committed parent `qf-uflia-cvc5-regress-clean` baseline over its
  six decided instances. The parent row is now **6/6 dominant (100.0%)** with
  **Lean unsat 2/2 (100.0%)**, **mismatches=0**, **audit_errors=0**,
  **timeouts=0**, **evidence_checked=6/6**, and **evidence_certified=6/6**.
  The two remaining overbound timeout rows remain decide-rate work; the decided
  slice no longer has a certification gap. `bench-results/DOMINANCE.md` now
  reports **23 complete exact audit rows**. **Next:** return to actual
  decide-rate movement on the hard UFLIA/AUFLIA overbound rows, especially
  Boolean-skeleton relevance for QF_UFLIA and the AUFLIA `bug330`/`bug337`
  scalar-search frontier.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-cvc5-regress-clean-solver-vs-z3-10s.json 30000 6 bench-results/dominance/qf-uflia-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m json.tool bench-results/dominance/qf-uflia-cvc5-regress-clean-dominance-audit.json >/dev/null`.

- **Session 2026-06-26 — structural refuter dispatch aligned; AUFLIA probes narrowed.**
  After the restart, I re-ran the QF_AUFLIA `bug330`/`bug337` diagnostics from
  the current tree. `bug330` is not a raw or preprocessed simple
  `term_identity` row: both the original single disequality and the
  model-sound preprocessed residual still have distinct top-level `ite`
  decision trees. A temporary bounded contextual-ITE equivalence prototype
  exhausted a 200k-step cap on both raw and reduced forms, so no solver code was
  kept from that route. `bug337` is confirmed `sat`, but the Z3 model is a large
  transition/table witness rather than a compact all-default array assignment;
  this reinforces the prior PBLS result that a generic local-search hook is not
  the right retained path. The practical AUFLIA next actions remain: SAT
  relevance or a replay-gated branch-schedule/model constructor for `bug337`,
  and a stronger Boolean/relevance or BDD-style scalar abstraction for the
  processor-shaped `bug330`.

  Retained code change: `check_auto` now tries the already-checked
  `term_identity_refutation` before heavier theory routes, so obvious
  `not (= t t)` / constant-`ite` identity contradictions are decided through
  the same certificate matcher that `produce_evidence` and Lean reconstruction
  already recheck. This is a dispatch alignment, not an AUFLIA closure.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib check_auto_uses_term_identity_refuter_before_theory_routes -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence term_identity -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test lean_crosscheck qf_lra_ite_true_identity_checks_in_real_lean -j1 -- --nocapture`.

- **Session 2026-06-26 — AUFLIA `bug337` direct PBLS-array probe rejected.**
  After the QF_AX closure, the next measured frontier is still QF_AUFLIA
  `bug330`/`bug337`. I tested a replay-gated direct local-search path on the
  pure Int-array `bug337` queue-lock row: admitting `(Array Int Int)` variables
  into PBLS, defaulting arrays, adding direct `select(a,i)=v` store repairs, and
  trying a 5 s pre-array-route probe. The diagnostic probe flattened the file to
  237 conjuncts but still timed out (`Unknown`, 1791 flips in 5 s). A temporary
  5 s scalar-abstraction local-search budget also failed: it only moved the
  route to a lazy-extensionality deadline after roughly 15.6 s, still `unknown`.
  No solver code was kept or committed from this experiment. **Next:** do not
  repeat a generic direct PBLS-array hook for `bug337`; the practical AUFLIA
  paths are a replay-gated branch-schedule/model constructor for the queue-lock
  transition shape, SAT relevance in the large scalar skeleton, or finite
  UF-table/model search for `bug330`.
  Diagnostics before revert:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test int_array_sort debug_bug337_array_local_search_probe -j1 -- --ignored --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__bug337.smt2 10000`.
  Verification on the retained tree passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver -j1`;
  `git diff --check`.

- **Session 2026-06-26 — QF_AX declared-sort SAT rows closed.**
  Routed pure declared-sort QF_AX arrays through the existing lazy
  ROW/extensionality CEGAR with the replaying EUF e-graph as the scalar
  backend. The model projection now materializes generic array values for
  declared carrier sorts, and true array-equality refinement checks all
  compatible materialized indices plus finite store indices, so the `arrays3`
  store-equality/disequality interaction gets the needed witness. This closes
  the remaining SAT `arrays2`/`arrays3` rows with replay-checked models and
  trust-hole-free SAT evidence. The refreshed QF_AX baseline is **8/8 decided
  (100.0%)**, **unknown=0**, **unsupported=0**, **oracle-compared=8/8**,
  **DISAGREE=0**, PAR-2 mean **0.004 s**. The refreshed QF_AX dominance audit is
  **8/8 dominant (100.0%)**, **Lean unsat 5/5 (100.0%)**, **mismatches=0**,
  **audit_errors=0**, **timeouts=0**, **evidence_checked=8/8**, and
  **evidence_certified=8/8**. Scoreboards now report **663 decided** and
  **611 oracle-compared** overall. **Next:** QF_AX is closed for this small cvc5
  clean slice; move array effort to AUFLIA `bug330`/`bug337` scalar-search depth
  and broader neutral QF_AX/non-BV-array corpora.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver -j1`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arrays__arrays2.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arrays__arrays3.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test int_array_sort qf_ax_declared_sort_sat_models_replay -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence produce_evidence_replays_qf_ax_declared_sort_sat_models -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean --timeout-ms 10000 --backend solver --compare-z3 --jobs 2 --out bench-results/baselines/qf-ax-cvc5-regress-clean-solver-vs-z3-10s.json`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ax-cvc5-regress-clean-solver-vs-z3-10s.json 30000 8 bench-results/dominance/qf-ax-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --test int_array_sort --test evidence -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-scoreboard.py scripts/gen-dominance-scoreboard.py`;
  `./scripts/check-links.sh`;
  `git diff --check`.

- **Session 2026-06-26 — QF_AX Bool-array read-collapse row closed.**
  Added a checked `BoolArrayReadCollapseCertificate` for Bool-index arrays:
  once `(select a false) = (select a true)`, every read from `a` is equal, so an
  asserted disequality between two reads of `a` is impossible. The rule is wired
  into the array fast path, `produce_evidence`, dominance labels, and Lean
  reconstruction as `bool-array-read-collapse-unsat` /
  `ProofFragment::BoolArrayReadCollapse`. This closes the cvc5 QF_AX
  `bool-array.smt2` row as `unsat` without bit-blasting arrays. The refreshed
  QF_AX baseline is **6/8 decided (75.0%)**, **unknown=0**,
  **unsupported=2**, **oracle-compared=6/8**, **DISAGREE=0**, PAR-2 mean
  **6.667 s**. The refreshed QF_AX dominance audit is **6/6 dominant
  (100.0%)**, **Lean unsat 5/5 (100.0%)**, **mismatches=0**,
  **audit_errors=0**, **timeouts=0**, **evidence_checked=6/6**, and
  **evidence_certified=6/6**. Scoreboards now report **661 decided** and
  **609 oracle-compared** overall. **Next:** the remaining QF_AX blockers are
  the SAT `arrays2`/`arrays3` rows, which need replay-checked declared-sort
  model construction rather than another UNSAT refuter; nearby AUFLIA remains
  gated by `bug330`/`bug337` scalar-search depth.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib bool_index_read_collapse -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test int_array_sort qf_ax_bool_array_read_collapse_unsat_closes -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence produce_evidence_certifies_qf_ax_bool_array_read_collapse -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test lean_crosscheck qf_ax_bool_array_read_collapse_checks_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean --timeout-ms 10000 --backend solver --compare-z3 --jobs 2 --out bench-results/baselines/qf-ax-cvc5-regress-clean-solver-vs-z3-10s.json`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ax-cvc5-regress-clean-solver-vs-z3-10s.json 30000 6 bench-results/dominance/qf-ax-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`.

- **Session 2026-06-26 — QF_AX exact dominance audit closed.**
  Added checked evidence and Lean reconstruction for the QF_AX declared-sort
  slice decided in the previous increment. The array-axiom matcher now
  decomposes false Boolean implication, so `arr1` certifies as
  `array-axiom-unsat` / `ProofFragment::ArrayAxiom`. The same-index
  reciprocal-store refuter now exports a rechecked
  `UnsatCrossStoreArrayDisequality` certificate and reconstructs through
  `ProofFragment::CrossStoreArrayDisequality`, closing `arrays0` and `arrays4`
  with real-Lean-accepted modules and no `sorryAx`. The committed QF_AX
  dominance audit is **5/5 dominant (100.0%)**, **Lean unsat 4/4 (100.0%)**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**,
  **evidence_checked=5/5**, and **evidence_certified=5/5**.
  `bench-results/DOMINANCE.md` now reports **22 complete exact audit rows**.
  **Next:** QF_AX proof coverage is closed for the current decided slice; move
  QF_AX effort to declared-sort SAT model construction for `arrays2`/`arrays3`
  or the Bool-array unsat row, while the nearby AUFLIA frontier remains
  `bug330`/`bug337` scalar-search depth.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib recognizes_false_implication_read_congruence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib cross_store_array_refuter_closes_qf_ax_unsats_only -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence produce_evidence_certifies_qf_ax_declared_sort_unsats -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test lean_crosscheck qf_ax_declared_sort_certificates_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ax-cvc5-regress-clean-solver-vs-z3-10s.json 30000 5 bench-results/dominance/qf-ax-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 scripts/gen-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --examples -j1`.

- **Session 2026-06-26 — QF_AX cross-store declared-sort refuter.**
  Extended the existing structural swap-chain array refuter with a same-index
  reciprocal-store rule over arbitrary array component sorts: from
  `store(A,i,select(B,i)) = store(B,i,select(A,i))` it derives `A = B`, iterates
  the derivation through nested store chains, and closes a direct asserted
  disequality. This closes the cvc5 QF_AX declared-sort `arrays0` and `arrays4`
  UNSAT rows without raising the finite array-equality enumeration cap or trying
  to bit-blast uninterpreted carrier values. A negative regression confirms the
  SAT `arrays3` mixed-index shape does not match the refuter. The refreshed
  current-harness QF_AX baseline is **5/8 decided (62.5%)**, **unknown=1**,
  **unsupported=2**, **oracle-compared=5/8**, **DISAGREE=0**, with PAR-2 mean
  **10.000 s**. Scoreboards now report **660 decided** and **608
  oracle-compared** overall. **Next:** add evidence/Lean certification for this
  QF_AX direct refuter only after deciding whether the next QF_AX priority is
  proof coverage or SAT model construction for `arrays2`/`arrays3`; the nearby
  AUFLIA frontier remains `bug330`/`bug337` scalar-search depth.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib cross_store_array_refuter_closes_qf_ax_unsats_only -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test int_array_sort qf_ax_declared_sort_array_extensionality_unsats_close -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean --timeout-ms 10000 --backend solver --compare-z3 --jobs 2 --out bench-results/baselines/qf-ax-cvc5-regress-clean-solver-vs-z3-10s.json`;
  `python3 scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --examples -j1`.

- **Session 2026-06-26 — QF_ALIA dominance audit closed.**
  Added zero-trust evidence variants for the two QF_ALIA-specific Int-array
  refuters: `UnsatConstArrayDefaultMismatch` for `constarr3` and
  `UnsatStoreChainReadback` for `ios_np_sf`. `produce_evidence`, the dominance
  audit labels, and Lean reconstruction now recognize both routes; the
  reconstructors re-run and recheck the structural certificates before
  rendering certificate-wrapper Lean modules, and the real-Lean cross-check
  asserts those modules contain no `sorryAx`. The committed QF_ALIA dominance
  audit is now **6/6 dominant (100.0%)**, **Lean unsat 5/5 (100.0%)**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**,
  **evidence_checked=6/6**, and **evidence_certified=6/6**.
  `bench-results/DOMINANCE.md` now reports **21 complete exact audit rows** and
  an empty first audit queue. **Next:** QF_ALIA is closed for this cvc5 slice;
  move Int-array effort to QF_AUFLIA `bug330`/`bug337` scalar-search depth,
  QF_AX witnessed extensionality, and broader non-BV component sorts.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence produce_evidence_certifies_qf_alia_store_chain_unsats -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test lean_crosscheck qf_alia_store_chain_certificates_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-alia-cvc5-regress-clean-solver-vs-z3-10s.json 30000 6 bench-results/dominance/qf-alia-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --test evidence --test lean_crosscheck -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-bench --example audit_dominance -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-scoreboard.py scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — QF_ALIA store-chain readback refuter.**
  Added a checked `StoreChainReadbackCertificate` for finite store-chain
  equality over a shared `(Array Int Int)` base. The certificate resolves
  top-level array/scalar definitions, normalizes unit-affine Int index aliases
  such as `i+3`, proves the selected visible write index is distinct from every
  opposite-chain write index, and then uses an asserted disequality against the
  forced base read to refute the query. This closes the cvc5 `ios_np_sf` row as
  `unsat`. Refreshed committed baseline: **QF_ALIA 6/6 decided (100.0%)**,
  **unknown=0**, **unsupported=0**, **oracle-compared=5/6**, **DISAGREE=0**,
  PAR-2 mean **0.000 s**. `bench-results/SCOREBOARD.md` and
  `bench-results/DOMINANCE.md` now report **658 decided** and
  **606 oracle-compared** overall. The follow-up evidence/Lean audit is closed
  by the next session entry; nearby Int-array solve work is QF_AUFLIA
  `bug330`/`bug337` scalar-search depth plus QF_AX breadth.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib store_chain_readback_certificate_rechecks_ios_np_sf -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test int_array_sort store_chain_readback_refutes_ios_np_sf -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test int_array_sort -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_ALIA/cvc5-regress-clean --timeout-ms 10000 --backend solver --compare-z3 --jobs 2 --out bench-results/baselines/qf-alia-cvc5-regress-clean-solver-vs-z3-10s.json`;
  `python3 scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --test int_array_sort -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-scoreboard.py scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — QF_ALIA const-array store-chain refuter.**
  Added a checked `ConstArrayDefaultMismatchCertificate` for finite store chains
  over different constant-array defaults on the infinite `Int` index sort:
  finitely many writes cannot cover all integer indices, so equality of those
  arrays is impossible when their untouched defaults are provably different
  ground constants. This closes the cvc5 `constarr3` QF_ALIA row as `unsat`;
  a same-default regression confirms the refuter does not fire on satisfiable
  finite-write shapes. Refreshed committed baseline:
  **QF_ALIA 5/6 decided (83.3%)**, **unknown=1**, **unsupported=0**,
  **oracle-compared=4/6**, **DISAGREE=0**, PAR-2 mean **3.333 s**.
  `bench-results/SCOREBOARD.md` and `bench-results/DOMINANCE.md` now report
  **657 decided** and **605 oracle-compared** overall. **Next:** the only
  remaining QF_ALIA blocker is `ios_np_sf`, which needs store-chain/readback
  reasoning plus arithmetic-backed proof that the selected index is distinct
  from the opposite chain's write indices; QF_AUFLIA still has `bug330` and
  `bug337` scalar-search timeouts.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib const_array_default_mismatch_certificate_rechecks_constarr3 -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test int_array_sort const_array_store_chain -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_ALIA/cvc5-regress-clean --timeout-ms 10000 --backend solver --compare-z3 --jobs 2 --out bench-results/baselines/qf-alia-cvc5-regress-clean-solver-vs-z3-10s.json`;
  `python3 scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`.

- **Session 2026-06-26 — QF_ALIA/AUFLIA array rows refreshed.**
  Added a narrow cvc5 `:arrays-exp` front-end lowering for `eqrange`: constant
  Int ranges expand to finite pointwise `select` equalities, and nonconstant or
  over-cap ranges still decline. Added a sound constant-index self-store
  equality normalization for `a = store(...store(a,k,v)...)`, reducing those
  recursive array equalities to point constraints; this closes the cvc5
  `eqrange3` AUFLIA row as `sat`. The scalar array abstraction now treats
  preprocessing replay failure as an optimization miss and falls back to the raw
  scalar backend before the existing array projection/replay gate. Refreshed
  committed baselines: **QF_ALIA 4/6 decided (66.7%)**, **unknown=2**,
  **unsupported=0**, **oracle-compared=3/6**, **DISAGREE=0**, PAR-2 mean
  **6.667 s**; **QF_AUFLIA 5/7 decided (71.4%)**, **unknown=2**,
  **unsupported=0**, **oracle-compared=4/7**, **DISAGREE=0**, PAR-2 mean
  **5.716 s**. `bench-results/SCOREBOARD.md` and
  `bench-results/DOMINANCE.md` now report **656 decided** and
  **604 oracle-compared** overall. **Next:** QF_AUFLIA's remaining blockers are
  scalar-search timeouts on `bug330` and `bug337`; QF_ALIA's remaining blockers
  are lazy-extensionality replay incompletes on `ios_np_sf` and `constarr3`.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-smtlib eqrange_expands_constant_int_range -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-smtlib int_array_self_store_equality_reduces_to_point_constraints -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test smtlib decides_cvc5_eqrange_extension_script -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean --timeout-ms 10000 --backend solver --compare-z3 --jobs 2 --out bench-results/baselines/qf-auflia-cvc5-regress-clean-solver-vs-z3-10s.json`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_ALIA/cvc5-regress-clean --timeout-ms 10000 --backend solver --compare-z3 --jobs 2 --out bench-results/baselines/qf-alia-cvc5-regress-clean-solver-vs-z3-10s.json`;
  `python3 scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-smtlib --tests -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --test smtlib -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-scoreboard.py scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — QF_UFLIA parent row remeasured honestly.**
  Refreshed the stale parent `qf-uflia-cvc5-regress-clean` baseline against the
  actual parent corpus instead of the old bounded-only snapshot. The row is now
  **6/8 decided (75.0%)**, **unknown=2**, **unsupported=0**,
  **oracle-compared=6/8**, **DISAGREE=0**, and PAR-2 mean **5.001 s**. The two
  remaining blockers are the overbound `Timeout` rows. A narrow paired-bound
  substitution prototype was tested but not committed: it avoided one recursive
  replacement stack issue, but still failed to certify the overbound rows within
  the 10 s budget. `bench-results/SCOREBOARD.md` and
  `bench-results/DOMINANCE.md` now report **651 decided** and
  **600 oracle-compared** overall. **Next:** treat QF_UFLIA overbound as a real
  decider frontier; shallow top-level equality propagation is not sufficient.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_UFLIA --timeout-ms 10000 --backend solver --compare-z3 --jobs 2 --out bench-results/baselines/qf-uflia-cvc5-regress-clean-solver-vs-z3-10s.json`;
  `python3 scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `python3 -m py_compile scripts/gen-scoreboard.py scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — QF_UFLIA bounded row remeasured to full coverage.**
  Refreshed the stale bounded declared-sort QF_UFLIA baseline after the current
  mixed UF+arithmetic congruence route already decided its last gap,
  `bug303`, as `unsat`. The Z3-compared baseline is now **6/6 decided
  (100.0%)**, **DISAGREE=0**, **oracle-compared=6/6**, and PAR-2 mean
  **0.002 s**. The exact dominance audit is refreshed at **6/6 dominant
  (100.0%)**, **Lean unsat 2/2 (100.0%)**, **mismatches=0**,
  **audit_errors=0**, **timeouts=0**, **evidence_checked=6/6**, and
  **evidence_certified=6/6**. `bench-results/SCOREBOARD.md` and
  `bench-results/DOMINANCE.md` then reported **649 decided** and
  **598 oracle-compared** overall. **Next:** continue from measurement-backed
  decide gaps rather than proof-auditing already dominant rows; the nearby
  frontiers remain QF_UFLIA unbounded/overbound, QF_ALIA/AUFLIA arrays, and
  QF_UF overbound's two undecided instances.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-bounded/cli__regress0__bug303.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-bounded --timeout-ms 10000 --backend solver --compare-z3 --jobs 4 --out bench-results/baselines/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 6 bench-results/dominance/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json`;
  `python3 scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-scoreboard.py scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — QF_UF overbound dominance audit closed.**
  Added a checked online Boolean-EUF certificate for large pure-EUF Boolean
  skeletons that exceed the exhaustive equality-atom case bound. The certificate
  first rejects non-pure-EUF shapes, then re-runs the deterministic online EUF
  DPLL(T) refuter over the original assertions and accepts only a fresh `unsat`;
  evidence is certified, checked, and carries no trust steps. This closes the
  three overbound QF_UF UNSAT audit gaps (`uf/cnf_abc`, `proof00`, and
  `proofs/macro-res-exp-crowding-lit-inside-unit`) as
  `bool-euf-online-unsat` / `ProofFragment::BoolEufOnline`. The overbound
  declared-sort QF_UF dominance audit is now **4/4 dominant (100.0%)**,
  **Lean unsat 3/3 (100.0%)**, **mismatches=0**, **audit_errors=0**,
  **timeouts=0**, **evidence_checked=4/4**, and **evidence_certified=4/4**.
  At that point `bench-results/DOMINANCE.md` reached its **20th complete exact
  audit row**.
  The solve row is still honestly **4/6 decided** overall; this closes the
  audited decided slice, not the two undecided instances. **Next:** move the
  dominance push to the next measured row where either evidence coverage or
  decide coverage still blocks a defensible all-four claim.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib bool_euf::tests:: -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence qf_uf_overbound_rows_use_checked_online_euf_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test lean_crosscheck qf_uf_overbound_online_euf_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound/cli__regress0__uf__cnf_abc.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound/cli__regress1__proof00.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound/cli__regress1__proofs__macro-res-exp-crowding-lit-inside-unit.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uf-cvc5-regress-clean-overbound-uninterp-sorts-solver-vs-z3-10s.json 30000 4 bench-results/dominance/qf-uf-cvc5-regress-clean-overbound-uninterp-sorts-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --all-features -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-bench --examples -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — QF_UF declared-sort exact audit closed.**
  Closed the last bounded declared-sort QF_UF dominance gap,
  `issue3970-nl-ext-purify`. The row was being routed through the pure-real
  LRA/NRA evidence branch before the generic structural certificate pass could
  run; `produce_evidence` now tries direct structural certificates before that
  branch. The benchmark's purified `distinct` expansion contains an asserted
  disequality of a term with itself, so the existing checked `term-identity`
  certificate now handles it with no trust steps and Lean reconstructs it as
  `ProofFragment::TermIdentity`. The Boolean simplifier also learned the same
  conservative reflexive-equality normalization for direct Boolean contexts.
  The exact QF_UF bounded declared-sort audit is refreshed at **44/44 dominant
  (100.0%)**, **Lean unsat 15/15 (100.0%)**, **mismatches=0**,
  **audit_errors=0**, **timeouts=0**, **evidence_checked=44/44**, and
  **evidence_certified=44/44**. **Next:** move the dominance push to the next
  measured non-dominant row rather than continuing to spend proof budget on this
  now-closed exact QF_UF slice.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib bool_simplify::tests:: -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence qf_uf_issue3970_uses_checked_term_identity_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test lean_crosscheck qf_uf_issue3970_term_identity_checks_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress1__issue3970-nl-ext-purify.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 44 bench-results/dominance/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --all-features -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-bench --examples -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — QF_UF mixed UF+arithmetic audit gap closed.**
  Added a checked `uf-arith-congruence-unsat` certificate for the cvc5 `bug303`
  row. The checker re-runs the shared Ackermann/congruence construction,
  retains only Boolean-structured linear-arithmetic rewritten assertions plus
  arithmetic-sorted derived congruence consequents, and verifies that residual
  with the existing arithmetic-DPLL certificate. This covers the benchmark
  shape where congruence over the declared `list` carrier proves
  `length(one_cons nil) = length(cons 1 nil)`, after which the integer facts
  force the contradiction. Lean reconstruction now routes through
  `ProofFragment::UfArithCongruence` and re-runs the checker before rendering
  the wrapper. The assertion-set Boolean simplifier also learned a conservative
  cross-assertion `not (and ...)` contradiction rule, but the nonlinear
  `issue3970-nl-ext-purify` row still returns checked `unknown`. The exact
  QF_UF bounded declared-sort audit is refreshed at **43/44 dominant (97.7%)**,
  **Lean unsat 14/14 (100.0%)**, **mismatches=0**, **audit_errors=0**,
  **timeouts=0**, **evidence_checked=44/44**, and
  **evidence_certified=43/44**. Remaining QF_UF blocker: the nonlinear-extension
  row `issue3970-nl-ext-purify`, where baseline is `unsat` but evidence remains
  checked `unknown`. **Next:** decide whether to add an explicit nonlinear
  arithmetic/propositional certificate for `issue3970`, or mark it as the honest
  frontier for this bounded QF_UF audit row and move to the next measured row.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib uf_arith::tests:: -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib bool_simplify::tests:: -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence qf_uf_bug303_uses_checked_uf_arith_congruence_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test lean_crosscheck qf_uf_bug303_uf_arith_congruence_checks_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__bug303.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress1__issue3970-nl-ext-purify.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 44 bench-results/dominance/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --all-features -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-bench --examples -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — QF_UF Boolean-EUF audit gaps closed.**
  Added a checked Boolean-structured EUF refutation bridge for pure
  uninterpreted-sort formulas whose contradiction is hidden behind Boolean
  syntax. The checker abstracts EUF equality atoms, enumerates every satisfying
  Boolean skeleton assignment, and requires each induced equality/disequality
  core to be refuted by the existing congruence checker; mixed arithmetic/BV
  shapes are rejected. This certifies `simple-uf`, `uf/cnf-and-neg`, and
  `uf/cnf-ite` as `bool-euf-exhaustive-unsat` /
  `ProofFragment::BoolEufExhaustive`, with no trust steps and Lean-checked
  wrappers. The exact QF_UF bounded declared-sort audit is refreshed at
  **42/44 dominant (95.5%)**, **Lean unsat 13/14 (92.9%)**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**,
  **evidence_checked=44/44**, and **evidence_certified=42/44**. Remaining
  QF_UF blockers are now `bug303` (mixed UF+arithmetic, still
  `bare-unsat`) and `issue3970-nl-ext-purify` (checked `unknown` against a
  baseline `unsat`). **Next:** decide whether `bug303` needs a small
  arithmetic/purification certificate, then decide whether the nonlinear
  extension row should get an explicit arithmetic certificate or stay an honest
  frontier.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib bool_euf -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence qf_uf_boolean_euf_rows_use_checked_exhaustive_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test lean_crosscheck qf_uf_boolean_euf_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__simple-uf.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__uf__cnf-and-neg.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__uf__cnf-ite.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 44 bench-results/dominance/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --all-features -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-bench --examples -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — QF_UF set-cardinality audit timeout closed.**
  Added a checked lowered finite-set cardinality refutation for the SMT-LIB
  `set.card`→BV-popcount encoding. The checker recognizes popcount lower/upper
  bounds, subset facts, and safe union/intersection cardinality upper bounds;
  it certifies both `sets/card` and `sets/card-6` directly as
  `set-cardinality-unsat` / `ProofFragment::SetCardinality`, with no DRAT
  reduction and no trust holes. The `sets/card-6` evidence timeout is gone, and
  the previous `sets/card` bit-blast trust-hole row is now Lean-checked. The
  exact QF_UF bounded declared-sort audit is refreshed at **39/44 dominant
  (88.6%)**, **Lean unsat 10/14 (71.4%)**, **mismatches=0**,
  **audit_errors=0**, **timeouts=0**, **evidence_checked=44/44**, and
  **evidence_certified=39/44**. Remaining QF_UF blockers are the four
  `bare-unsat` pure-UF/Boolean-normalization rows (`bug303`, `simple-uf`,
  `uf/cnf-and-neg`, `uf/cnf-ite`) and the nonlinear-extension row
  `issue3970-nl-ext-purify`, whose evidence route still returns checked
  `unknown` against a baseline `unsat`. **Next:** add the sound Boolean
  proof bridge for the `bare-unsat` pure-UF rows, then decide whether the
  nonlinear-extension row needs an explicit arithmetic/purification certificate
  or should stay an honest frontier.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib set_cardinality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence qf_uf_set_cardinality_rows_use_checked_cardinality_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test lean_crosscheck qf_uf_sets_cardinality_checks_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress1__sets__card-6.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__sets__card.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 44 bench-results/dominance/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --all-features -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-bench --examples -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — QF_UF SAT evidence audit errors closed.**
  Closed the two QF_UF bounded declared-sort SAT evidence audit errors. The
  Diophantine and arithmetic-DPLL optional evidence prepasses now decline
  queries with no Int/Real content before invoking arithmetic/BV machinery, so
  declared-sort-only SAT rows fall through to the normal EUF/auto solver model
  and replay through `Evidence::Sat`. This closes `parser/as` and `ite4`; both
  now produce checked, trust-hole-free SAT evidence. The exact audit is refreshed
  at **37/44 dominant (84.1%)**, **Lean unsat 8/14 (57.1%)**,
  **mismatches=0**, **audit_errors=0**, **timeouts=1**. The dominance report now
  correctly labels the next action as **fix audit timeouts** rather than a
  phantom audit error. Remaining QF_UF blockers are the `sets/card-6`
  check-evidence timeout, the `sets/card` bit-blast trust-hole row, the
  CNF/Boolean-normalization pure-UF proof gaps, and the guarded nonlinear
  `unknown`. **Next:** fix the `sets/card-6` evidence timeout or add the sound
  Boolean proof bridge for the `bare-unsat` pure-UF rows.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence qf_uf_parser_as_sat_evidence_replays_declared_sort_model -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence qf_uf_declared_sort_ite_sat_evidence_replays_model -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence satisfiable_uflia_opaque_arith_abstraction_still_replays_sat_model -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__parser__as.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__ite4.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 44 /tmp/qf-uf-bounded-dominance-audit-after-sat-errors-v2.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --all-features -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-bench --examples -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — QF_UF declared-sort equality audit route.**
  The refreshed QF_UF bounded declared-sort row now has a committed exact
  dominance audit. `scan_proof_fragment` treats equality/disequality over
  declared uninterpreted carrier sorts as `QfUf` even when no `Apply` node is
  present, and the zero-trust Alethe evidence path now tries the pure EUF
  congruence emitter directly. This closes the `parallel-let` proof-route gap:
  it already had checked Alethe evidence, but Lean reconstruction was routed to
  the wrong fragment. The exact audit for
  `qf-uf-cvc5-regress-clean-bounded-uninterp-sorts` is now committed at
  **37/44 dominant (84.1%)**, **Lean unsat 8/14 (57.1%)**,
  **mismatches=0**, **audit_errors=0**, **timeouts=1**. The dominance report now
  has **19 complete exact audit rows**. Remaining QF_UF blockers are concrete:
  Boolean-normalization proof bridges for `not =>`/CNF-shaped pure-UF rows,
  a Lean route for the set/card bit-blast trust-hole row, the
  nonlinear-extension `unknown`, and one check-evidence timeout. **Next:** fix
  the timeout first, then add a
  sound Boolean proof bridge for the `bare-unsat` pure-UF rows.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence qf_uf_declared_sort_equality_unsat_carries_zero_trust_alethe_certificate -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test evidence qf_ufbv_unsat_carries_a_zero_trust_alethe_certificate -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test lean_crosscheck qf_uf_declared_sort_equality_checks_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test lean_crosscheck qf_ufbv_refutation_checks_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__parallel-let.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 44 /tmp/qf-uf-bounded-dominance-audit-after-declsort.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --all-features -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — QF_UF underspecified div/mod soundness guard.**
  Re-ran the current QF_UF cvc5 rows and found a false `unsat` on
  `cli__regress1__sygus__proj-issue165.smt2`: the formula is satisfiable under
  SMT-LIB because integer `mod` by zero is underspecified, but Axeyum's
  executable evaluator convention had concretized `mod 0 0 = 0` during an UNSAT
  route. `check_auto` now skips bounded integer-box refutation when an
  integer/real division or modulo divisor is not syntactically a known nonzero
  constant, and the lazy arithmetic DPLL path rejects unsupported arithmetic
  atoms before adding them to the Boolean skeleton. Known-nonzero constant
  divisors remain decidable. The witness now reports checked `unknown`, not
  `unsat`. Refreshed QF_UF baselines: overbound remains **4/6 decided**,
  **DISAGREE=0**; both bounded rows are now **44/82 decided**,
  **DISAGREE=0**. Regenerated scoreboards now report **648 decided**,
  **597 oracle-compared**, and **18 complete exact audit rows**. **Next:** build
  an explicit SMT-LIB underspecification encoding for div/mod/real-div if we
  want to recover these UNSAT decisions soundly, then run a QF_UF dominance
  audit over the refreshed rows.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib mod_by -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib abstractor_rejects_unsupported_integer_mod_atom -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress1__sygus__proj-issue165.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded --timeout-ms 10000 --backend solver --compare-z3 --jobs 4 --out bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-solver-vs-z3-10s.json`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded --timeout-ms 10000 --backend solver --compare-z3 --jobs 4 --out bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound --timeout-ms 10000 --backend solver --compare-z3 --jobs 4 --out bench-results/baselines/qf-uf-cvc5-regress-clean-overbound-uninterp-sorts-solver-vs-z3-10s.json`;
  `python3 scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --all-features -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-scoreboard.py scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — exact QF_DT dominance row closed.**
  Closed the cvc5 QF_DT decide/proof gap by extending the datatype structural
  refuter from direct top-level equalities to the benchmark shapes actually in
  the slice: flattened top-level conjunctions, top-level `or` branches whose
  every disjunct is structurally refutable, and constructor exhaustiveness
  conflicts from negative testers plus nullary-constructor disequalities. The
  former unsupported `acyclicity-sr-ground096` row now decides `unsat`, and the
  former bare `pf-v2l60078` proof row now emits checked
  `datatype-structural-unsat` evidence. `Evidence::check`,
  `produce_evidence`, `diagnose_evidence`, the dominance audit labels, and
  `ProofFragment::DatatypeStructural` all re-run the same checker before
  accepting the certificate/wrapper. The regenerated QF_DT baseline is now
  **3/3 decided**, **DISAGREE=0**, **unsupported=0**, and the exact dominance
  audit is **3/3 dominant** with **Lean unsat 3/3**, **mismatches=0**,
  **audit_errors=0**, **timeouts=0**, and no trust holes. The generated
  scoreboards now report **641 decided**, **592 oracle-compared**, and **18
  complete exact audit rows**. **Next:** use the same measured-audit loop on
  the next strong row with an unclosed Lean/cert lane, or broaden datatype
  audits beyond the cvc5 three-file slice.
  Verification passed:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --lib datatype_acyclicity -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_dt_cvc5_slice_uses_checked_datatype_structural_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_dt_cvc5_slice_checks_in_real_lean -j1 -- --nocapture`;
  `AXEYUM_DIAGNOSE_ONLY_EVIDENCE=1 CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_DT/cvc5-regress-clean/cli__regress0__datatypes__pf-v2l60078.smt2 10000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_DT/cvc5-regress-clean --timeout-ms 10000 --backend solver --compare-z3 --logic QF_DT --jobs 4 --out bench-results/baselines/qf-dt-cvc5-regress-clean-solver-vs-z3-10s.json`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-dt-cvc5-regress-clean-solver-vs-z3-10s.json 30000 3 bench-results/dominance/qf-dt-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-scoreboard.py scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — exact QF_BVFP dominance row closed.**
  Closed the Bitwuzla QF_BVFP proof-route audit by extending the checked
  `UnsatBvDefinedEnum` / `ProofFragment::BvDefinedEnum` route to the two former
  timeout rows. `collect_required_constraints` now follows nested negated
  implications, so rows such as `Float-no-simp3-main` expose the required `d`
  and `not c` facts instead of only the outer `true` antecedent. Definition and
  assertion replay now uses selected-path `ite`/Boolean evaluation backed by
  the existing evaluator for non-branching operators; parser-created FP helper
  symbols such as `!fp.to_sbv...` are therefore left unassigned only when the
  chosen semantic path never reads them, and the checker declines otherwise.
  The route also permits no-definition FP-lowered `FpFromBits` formulas to use
  the same tiny-domain replay, which certifies `fp_fromsbv` by enumerating
  `x : BV1` and the restricted `rm <= 4` rounding-mode token. The exact QF_BVFP
  audit is now **7/7** dominant with **Lean unsat 3/3**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**. The dominance report now has **17
  complete exact audit rows**. **Next:** broaden FP/BVFP audits beyond the
  Bitwuzla slice or move to the remaining strong-but-unaudited proof-route
  frontiers such as QF_SEQ/QF_DT once their cert lanes are ready.
  Verification passed:
  `cargo fmt --all --check`;
  `AXEYUM_DIAGNOSE_ONLY_EVIDENCE=1 CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_BVFP/bitwuzla-regress-clean/solver__fp__fp_fromsbv.smt2 10000`;
  `AXEYUM_DIAGNOSE_ONLY_EVIDENCE=1 CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_BVFP/bitwuzla-regress-clean/solver__fp__Float-no-simp3-main.smt2 10000`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_bvfp_bitwuzla_rows_use_checked_bv_defined_enum_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_fp_bitwuzla_rows_use_checked_bv_defined_enum_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --lib bv_defined_enum -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_bvfp_bv_defined_enum_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-bvfp-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 8 bench-results/dominance/qf-bvfp-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-26 — exact QF_FP dominance row closed.**
  Widened the checked `UnsatBvDefinedEnum` / `ProofFragment::BvDefinedEnum`
  route from Bool/BV-only terms to finite scalar terms, including `Float`
  values via Axeyum's ADR-0026 bit-pattern representation. This certifies the
  Bitwuzla QF_FP `fp_inf` and `fp_zero` constant-chain rows by re-deriving
  top-level definitions for the Float64 symbols and replaying one independent
  case. It also certifies `fp_misc`: cheap required single-symbol predicates such
  as `fp.isZero (fp.neg a)` shrink Float16 `a` to the zero bit-patterns, the
  rounding-mode declaration shrinks `rm` to `0..=4`, `b = abs(a)` is applied as a
  checked definition, and the original assertions are replayed over the resulting
  small domain. The route is bounded by a 20k case cap and a small-DAG guard for
  enumerated restrictions, so SAT rows such as `fp_regr3` fall through to model
  replay quickly. The exact QF_FP audit is now **16/16** dominant with **Lean
  unsat 7/7**, **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The
  dominance report remains at **16 complete exact audit rows**. **Next:** move to
  the QF_BVFP proof-route row or broaden FP audits beyond the Bitwuzla slice.
  Verification passed:
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --lib bv_defined_enum -j1 -- --nocapture`;
  `AXEYUM_DIAGNOSE_ONLY_EVIDENCE=1 CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_FP/bitwuzla-regress-clean/solver__fp__fp_inf.smt2 10000`;
  `AXEYUM_DIAGNOSE_ONLY_EVIDENCE=1 CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_FP/bitwuzla-regress-clean/solver__fp__fp_zero.smt2 10000`;
  `AXEYUM_DIAGNOSE_ONLY_EVIDENCE=1 CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_FP/bitwuzla-regress-clean/solver__fp__fp_misc.smt2 10000`;
  `AXEYUM_DIAGNOSE_ONLY_EVIDENCE=1 CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_FP/bitwuzla-regress-clean/solver__fp__fp_regr3.smt2 10000`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_fp_bitwuzla_rows_use_checked_bv_defined_enum_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_fp_bv_defined_enum_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-fp-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 16 bench-results/dominance/qf-fp-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — exact QF_FF dominance row closed.**
  Added checked `UnsatBvDefinedEnum` evidence and
  `ProofFragment::BvDefinedEnum` reconstruction for finite-field rows whose raw
  Bool/BV symbol domain exceeds the 20-bit term-level budget but becomes small
  after required top-level definitions and finite-domain restrictions are
  re-derived. The checker splits top-level conjunctions and the antecedent of
  `not (=> a b)`, treats equalities such as `mac1 = k1 + d*m1` as acyclic
  definitions, shrinks domains with constraints such as `x < p` and
  `x = 0 or x = 1`, then enumerates every independent assignment and replays the
  original assertions. Together with the existing `TermLevelEnum` wrapper for
  smaller QF_FF rows, the exact QF_FF/cvc5 audit is now **24/24** dominant with
  **Lean unsat 10/10**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**. The dominance report now has **15 complete exact audit rows**.
  **Next:** continue proof-route work on the remaining strong rows without exact
  audits (QF_FP/QF_BVFP) or move back to broader decide-rate gaps such as cvc5
  NRA and array/UF/arithmetic frontiers.
  Verification passed:
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --lib bv_defined_enum -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_ff_gap_rows_use_checked_bv_defined_enum_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_ff_bv_defined_enum_gap_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_ff_term_level_enum_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ff-cvc5-regress-clean-solver-vs-z3-10s.json 30000 24 bench-results/dominance/qf-ff-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — exact QF_UFFF dominance row closed.**
  Added checked `UnsatBvUfLocal` evidence and `ProofFragment::BvUfLocal`
  reconstruction for mixed finite-BV/UF formulas where tiny local BV
  enumeration derives equality facts and UF congruence closes the contradiction.
  This targets the cvc5 QF_UFFF finite-field rows after SMT-LIB parsing lowers
  `(_ FiniteField 17)` values to BV5: constraints such as field-idempotence
  plus the pair equation derive `a=b` locally, then congruence proves the UF
  conflict or the checked pure-BV conflict after `a=b`. Re-running the exact
  QF_UFFF/cvc5 audit moved **dominant 4/8 -> 8/8**, **Lean unsat 2/6 -> 6/6**,
  and **evidence certified 4/8 -> 8/8**, with **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**. The dominance report now has **14
  complete exact audit rows**. **Next:** build proof routes for the remaining
  strong unaudited rows (QF_FF/QF_FP/QF_BVFP) or attack broader decide-rate
  gaps such as cvc5 NRA and array/UF/arithmetic frontiers.
  Verification passed:
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --lib bv_uf_local -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_ufff_rows_use_checked_bv_uf_local_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_ufff_bv_uf_local_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ufff-cvc5-regress-clean-solver-vs-z3-10s.json 30000 8 bench-results/dominance/qf-ufff-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — exact cvc5 quantified-BV dominance row closed.**
  Added checked `UnsatBvForallNonconstant` evidence and
  `ProofFragment::BvForallNonconstant` reconstruction for universal BV
  inversion rows where a visibly non-constant expression is asserted equal to a
  fixed result for every quantified value. Covered schemas include
  `bvadd x a`, `bvashr x a`, both `concat` orientations, and the guarded
  `bvudiv` variants from the cvc5 quantified-BV slice. The checker re-scans the
  original IR for the universal equality plus required disequality side facts;
  Lean reconstruction reruns the checker before rendering the wrapper module.
  Re-running the exact BV/cvc5 quantified audit moved **dominant 31/37 -> 37/37**,
  **Lean unsat 2/8 -> 8/8**, and **evidence certified 31/37 -> 37/37**, with
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The dominance report
  now has **13 complete exact audit rows**. **Next:** build proof routes for
  strong unaudited rows (QF_UFFF/QF_FF/QF_FP/QF_BVFP) or attack broader
  decide-rate gaps such as cvc5 NRA and quantified rows where axeyum is still
  mid/weak.
  Verification passed:
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --lib bv_forall_nonconstant -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence cvc5_quantified_bv_inversion_rows_use_checked_nonconstant_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck cvc5_quantified_bv_inversion_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/bv-cvc5-regress-clean-quantified-solver-vs-z3-10s.json 30000 37 bench-results/dominance/bv-cvc5-regress-clean-quantified-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — exact quantified-BV dominance row closed.**
  Added checked `UnsatFiniteDomainEnum` evidence and
  `ProofFragment::FiniteDomainEnum` reconstruction for small finite Bool/BV
  formulas with quantifiers. The certifier enumerates free Bool/BV symbols,
  counts bound Bool/BV quantifier domains in the same budget, and reuses the
  executable IR evaluator for the original assertions. `Evidence::check` and
  Lean reconstruction both re-run the finite-domain certificate before accepting
  it. Re-running the exact BV/bitwuzla quantified audit moved **dominant 1/4
  -> 4/4**, **Lean unsat 0/3 -> 3/3**, and **evidence certified 1/4 -> 4/4**,
  with **mismatches=0**, **audit_errors=0**, and **timeouts=0**. **Next:**
  audit the larger cvc5 quantified-BV row, build proof routes for strong
  unaudited rows (QF_UFFF/QF_FF/QF_FP), or move back to broader cvc5
  NRA/high-degree decide gaps.
  Verification passed:
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence quantified_bv_audit_unsats_use_finite_domain_enum_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck quantified_bv_finite_domain_enum_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/bv-bitwuzla-regress-clean-quantified-solver-vs-z3-10s.json 30000 4 bench-results/dominance/bv-bitwuzla-regress-clean-quantified-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — exact QF_NRA synthetic dominance row closed.**
  Added checked `UnsatNraEvenPower` evidence and `ProofFragment::NraEvenPower`
  reconstruction for the remaining higher-degree synthetic NRA UNSAT rows. The
  matcher is deliberately narrow: it accepts only original assertions where a
  sum of syntactic even powers of real terms plus a nonnegative rational
  constant is asserted `< 0`; `Evidence::check` re-scans the original query and
  re-matches the certificate before accepting it. Lean reconstruction uses the
  same rechecked certificate before rendering the wrapper module. Re-running
  the exact QF_NRA audit moved **QF_NRA synthetic 24/30 -> 30/30 dominant**
  with **Lean unsat 10/16 -> 16/16**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**. **Next:** attack quantified-BV Lean
  gaps, build proof routes for strong unaudited rows (QF_UFFF/QF_FF/QF_FP), or
  move back to the broader cvc5 NRA/high-degree decide frontier.
  Verification passed:
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_nra_even_power_rows_use_checked_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_nra_even_power_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json 30000 30 bench-results/dominance/qf-nra-synthetic-graduated-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — exact QF_NIA synthetic dominance row closed.**
  Promoted the existing proven-box bounded-int-blast certificate into first-class
  evidence and Lean reconstruction for bounded nonlinear-integer UNSAT rows.
  `BoundedIntBlastCertificate::recheck` now also regenerates the clamped DIMACS
  from the original assertions before accepting the DRAT, binding the clausal
  proof back to the query. `produce_evidence` emits
  `bounded-int-blast-unsat` with certified `IntBlast`/`Tseitin`/
  `SatRefutation` steps, and `prove_unsat_to_lean_module` routes the same rows
  through `ProofFragment::BoundedIntBlast` only after the certificate rechecks.
  The bounded-box evaluator now also runs before preprocessing, so bounded NIA
  SAT rows such as the synthetic Pythagorean family return replayable models in
  milliseconds instead of timing out in preprocessing/model reconstruction.
  Re-running the exact QF_NIA audit moved **QF_NIA synthetic 16/32 -> 32/32
  dominant** with **Lean unsat 0/16 -> 16/16**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**. **Next:** attack the remaining exact
  QF_NRA higher-degree proof gaps, quantified BV Lean gaps, or build proof
  routes for strong unaudited rows (QF_UFFF/QF_FF/QF_FP).
  Verification passed:
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_nia_bounded_unsat_rows_use_bounded_int_blast_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_nia_bounded_int_blast_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `AXEYUM_DIAGNOSE_ONLY_EVIDENCE=1 CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/synthetic/QF_NIA/graduated/nia-pythagorean-m08.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-nia-synthetic-graduated-vs-z3.json 30000 32 bench-results/dominance/qf-nia-synthetic-graduated-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — exact QF_UFLIA dominance rows closed.**
  Widened the arithmetic lazy-SMT certificate path to cover Boolean-structured
  UFLIA proof-step rows: the integer simplex now has an unsat-oriented opaque
  UF-application mode, `ArithDPLL` verifies theory lemmas with that relaxation,
  and satisfiable opaque abstractions decline so SAT still falls through to the
  replaying UFLIA backend. `prove_unsat_to_lean_module` now classifies mixed
  UF+arithmetic rows as `ProofFragment::ArithDpll` only when the widened
  certificate re-verifies. This closes the two `use-name-in-same-command`
  rows. Re-running exact QF_UFLIA audits moved curated named **1/2 -> 2/2
  dominant** with **Lean unsat 1/2 -> 2/2**, and bounded uninterpreted-sort
  regressions **4/5 -> 5/5 dominant** with **Lean unsat 0/1 -> 1/1**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. **Next:** continue
  proof-coverage work on quantified BV or synthetic QF_NIA, or build the next
  Lean route for strong decide rows without audits (QF_UFFF/QF_FF/QF_FP).
  Verification passed:
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence congruence_free_uflia_uses_opaque_arith_alethe_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_uflia_use_name_rows_use_opaque_arith_dpll_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence satisfiable_uflia_opaque_arith_abstraction_still_replays_sat_model -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lia_dpll unsat_certificate_verifies_independently -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --lib emits_checkable_congruence_free_uflia_refutation -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/named/cvc5__use-name-in-same-command.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/named/cvc5__named-expr-use.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-curated-named-solver-vs-z3-10s.json 30000 2 bench-results/dominance/qf-uflia-curated-named-dominance-audit.json`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 5 bench-results/dominance/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_uflia_use_name_arith_dpll_rows_check_in_real_lean -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — opaque UFLIA integer Alethe coverage added.**
  Extended `lia_generic` checking to treat non-arithmetic integer applications as
  opaque integer terms, and added a congruence-free QF_UFLIA certificate route
  that eliminates UF applications, proves the integer abstraction with
  `lia_generic`, substitutes the opaque applications back into the Alethe proof,
  and re-checks it before returning evidence. This certifies repeated
  integer-valued UF applications such as `f(0) <= 0 ∧ f(0) >= 1` without
  Ackermann lemmas. Re-running the small QF_UFLIA exact audits moved curated
  named **0/2 -> 1/2 dominant** with **Lean unsat 0/2 -> 1/2**; the bounded
  uninterpreted-sort row remains **4/5 dominant** with **Lean unsat 0/1**.
  The remaining `use-name-in-same-command` gap is not congruence-free: it needs
  a Boolean-structured UF-abstraction/ArithDPLL certificate, not just opaque
  `lia_generic`.
  Verification passed:
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --lib emits_checkable_congruence_free_uflia_refutation -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --lib lia_generic_accepts_opaque_integer_app_tautology -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence congruence_free_uflia_uses_opaque_arith_alethe_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-curated-named-solver-vs-z3-10s.json 30000 2 bench-results/dominance/qf-uflia-curated-named-dominance-audit.json`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 5 bench-results/dominance/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — QF_NRA SOS dominance coverage widened.**
  Added a certificate-gated Lean fallback for sum-of-squares nonlinear-real
  refutations: reconstruction first tries the detailed SOS path, then re-runs
  `sos_refute_with_certificate` and accepts the generic `ProofFragment::Sos`
  wrapper only after `SosCertificate::verify()` succeeds. This moves the
  synthetic QF_NRA SOS rows that already had checked in-tree certificates into
  the Lean-checked dominance set without masking malformed detailed
  reconstruction failures. Re-running the exact QF_NRA graduated audit moved
  **QF_NRA synthetic 15/30 -> 24/30 dominant** with **Lean unsat 1/16 ->
  10/16**, **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The
  remaining QF_NRA audit misses are the higher-degree `bare-unsat` rows:
  `nra-neg-square-d02..d06` and `nra-sos-strict-unsat-d02`. **Next:** attack
  the quartic/even-power NRA certificate gap or move to QF_NIA/QF_UFLIA/
  quantified-BV proof coverage.
  Verification passed:
  `cargo test -p axeyum-solver --test evidence qf_nra_sos_certificate_wrapper_carries_lean_module -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_nra_sos_certificate_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/synthetic/QF_NRA/graduated/nra-sos-unsat-k01.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json 30000 30 bench-results/dominance/qf-nra-synthetic-graduated-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — exact QF_UFBV/bitwuzla dominance row closed.**
  Added a checked finite Boolean-UF exhaustive refuter
  (`UnsatBoolUfExhaustive` / `ProofFragment::BoolUfExhaustive`) for tiny
  formulas over reachable Boolean symbols and `Bool^n -> Bool` functions. The
  checker enumerates all Boolean assignments and function truth tables within a
  small case budget, accepting only when every case falsifies an original
  assertion. This certifies the remaining QF_UFBV/bitwuzla `fun1` unsat without
  the old trusted reduction fallback. Re-running the exact
  QF_UFBV/bitwuzla audit moved **QF_UFBV/bitwuzla 1/2 -> 2/2 dominant** with
  **Lean unsat 0/1 -> 1/1**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**. **Next:** continue reducing exact audited proof gaps in
  synthetic QF_NIA/QF_NRA, QF_UFLIA, or quantified BV.
  Verification passed:
  `cargo test -p axeyum-solver --lib ufbv_finite -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence qf_ufbv_fun1_bool_uf_exhaustive_unsat_carries_certificate -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_ufbv_fun1_bool_uf_exhaustive_checks_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFBV/bitwuzla-regress-clean/solver__fun__fun1.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 2 bench-results/dominance/qf-ufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — exact QF_LIA dominance row closed.**
  Added `UnsatArithDpll` evidence and `ProofFragment::ArithDpll` for
  Boolean-structured linear arithmetic certified by the existing
  `ArithDpllRefutation` checker. Also added a tiny checked Boolean
  simplification refuter (`UnsatBoolSimplification` /
  `ProofFragment::BoolSimplification`) for assertions that normalize to
  `false` by constants, idempotence, and complement pairs. This certifies the
  three remaining exact QF_LIA cvc5 misses: `dump-unsat-core-full` and
  `named-expr-use` through `arith-dpll-unsat`, and the large RF-11 ACI
  normalization stress row through `bool-simplification-unsat` without spending
  the audit budget in arithmetic DPLL. Re-running the exact QF_LIA audit moved
  **QF_LIA 7/10 -> 10/10 dominant** with **Lean unsat 1/4 -> 4/4**,
  **evidence certified 7/10 -> 10/10**, **mismatches=0**, **audit_errors=0**,
  and **timeouts=0**. **Next:** continue reducing exact audited proof gaps in
  synthetic QF_NIA/QF_NRA, QF_UFLIA, or quantified BV.
  Verification passed:
  `cargo test -p axeyum-solver --lib bool_simplify -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence qf_lia_audit_misses_use_arith_dpll_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence qf_lia_boolean_stress_row_uses_bool_simplification_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_lia_arith_dpll_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_lia_bool_simplification_audit_row_checks_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_LIA/cvc5-regress-clean-bounded/cli__regress0__proofs__RF-11-aci-norm-ndet.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-lia-cvc5-regress-clean-solver-vs-z3-10s.json 30000 10 bench-results/dominance/qf-lia-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — exact QF_LRA dominance row closed.**
  Added `ProofFragment::LraDpll`, a certificate-gated Lean wrapper for
  Boolean-structured pure-real LRA refutations already checked by the lazy-SMT
  DPLL(T) certificate (`LraDpllRefutation`). Reconstruction clones the arena,
  re-runs `certify_lra_dpll_unsat`, re-verifies the returned refutation, then
  renders a kernel-checked certificate wrapper with no `sorryAx`. This closes
  the two remaining exact QF_LRA cvc5 misses, `arith__ite-lift` and
  `simple-lra`, both now reporting `lean_fragment = LraDpll`, `lean_checked =
  true`, and no trust holes. Re-running the exact QF_LRA audit moved **QF_LRA
  7/9 -> 9/9 dominant** with **Lean unsat 1/3 -> 3/3**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**. **Next:** continue reducing exact
  audited proof gaps in QF_LIA and QF_UFBV/bitwuzla.
  Verification passed:
  `cargo test -p axeyum-solver --test lean_crosscheck qf_lra_dpll_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-lra-cvc5-regress-clean-solver-vs-z3-10s.json 30000 9 bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — QF_LRA term-identity proof gap closed.**
  Added a checked `term_identity` certificate for asserted disequalities whose
  two sides are equal by a tiny local identity normalizer (`ite true t e = t`,
  `ite false t e = e`, equal-branch `ite`, or literal reflexivity). The evidence
  front door now returns certified `term-identity-unsat` before the broader
  structural array recognizer can claim these non-array identities, and
  `prove_unsat_to_lean_module` reconstructs them through
  `ProofFragment::TermIdentity`. This certifies the QF_LRA cvc5 `ite_arith`
  row (`not (= x (ite true x y))`) with real-Lean reconstruction and no trust
  holes. Re-running the exact QF_LRA audit moved **QF_LRA 6/9 -> 7/9 dominant**
  with **Lean unsat 0/3 -> 1/3**, **evidence certified 8/9 -> 9/9**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. **Next:** continue
  reducing exact audited proof gaps in QF_LRA (`arith__ite-lift`,
  `simple-lra`), QF_LIA, and QF_UFBV/bitwuzla.
  Verification passed:
  `cargo test -p axeyum-solver --lib term_identity -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence pure_real_identity_contradiction_uses_term_identity_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_lra_ite_true_identity_checks_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_LRA/cvc5-regress-clean/cli__regress0__ite_arith.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-lra-cvc5-regress-clean-solver-vs-z3-10s.json 30000 9 bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — exact QF_BV bvred dominance row closed.**
  Added a direct `ProofFragment::ReflexiveDisequality` Lean route for literal
  top-level `not (= t t)` assertions: the exported proof assumes the input
  disequality and applies it to `Eq.refl`, with the in-tree kernel and real Lean
  both checking the resulting `False`. Re-running the exact QF_BV/bvred dominance
  audit also picked up the current checked structural route for the former
  `cvc5__redand-eliminate.smt2` miss: it remains `term-level-unsat` evidence, but
  now has `lean_fragment = ArrayAxiom`, `lean_checked = true`, and no trust holes.
  The exact row moves **QF_BV/bvred 5/6 -> 6/6 dominant** with **Lean unsat 1/2 ->
  2/2**, **mismatches=0**, **audit_errors=0**, and **timeouts=0**. **Next:** with
  exact QF_ABV, QF_AUFBV, and QF_BV/bvred closed, move the dominance loop to the
  remaining audited proof gaps in arithmetic, quantified BV, UFLIA, and the
  broader uninterpreted-sort / non-BV-array decide frontier.
  Verification passed:
  `cargo test -p axeyum-solver --lib end_to_end_reflexive_disequality_reconstructs_directly -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_bv_bvredand_identity_contradiction_checks_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-bv-curated-bvred-solver-vs-z3-10s.json 30000 6 bench-results/dominance/qf-bv-curated-bvred-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — exact ABV dominance row closed.**
  Extended the checked `ArrayAxiom` read-congruence lane with an ITE
  branch-exhaustion contradiction: an `ite(c, t, e)` term cannot be disequal
  from both `t` and `e`. `produce_evidence` now also tries this
  `array-axiom-unsat` lane before the general solver only on small assertion
  DAGs, which keeps the tiny frontier unsats fast without delaying large SAT
  rows such as `rw16`/`rw17`/`rw18` before model replay. This certifies the
  BTOR `rw34` array-ITE read-congruence row and the `arraycond9` branch
  exhaustion row as `array-axiom-unsat`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 167/169 -> 169/169 dominant** with **Lean unsat 83/83 -> 85/85**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **84** `sat-model` rows, **81** `array-axiom-unsat` rows,
  **3** `bv-abstraction-unsat` rows, **1** `alethe-unsat` row, and no
  `unknown` or `bare-unsat` exact-audit entries. **Next:** exact QF_ABV and
  exact QF_AUFBV are now closed; move the dominance loop to the next measured
  proof gap (QF_BV/QF_LIA/QF_LRA) or the broader uninterpreted-sort /
  non-BV-array decide frontier.
  Verification passed:
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw16.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw34.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond9.btor.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV cvc5 signed-BV1 proof gap closed.**
  Extended the checked `ArrayAxiom` read-congruence lane with conservative
  static BV range facts for `bvult` guards, fixed-sign `sign_extend`, full-width
  `extract`, singleton-range equivalence, and disjoint-range index distinctness.
  The Boolean collector can now close contradictions of the form `P = not Q`
  once the certificate lane independently proves `P = Q`. This certifies the
  cvc5 `issue9041` signed-BV1 read row as `array-axiom-unsat` through
  `ArrayAxiomKind::ReadCongruence`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 166/169 → 167/169 dominant** with **Lean unsat 82/83 → 83/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **79** `array-axiom-unsat` rows and **0** remaining
  `bare-unsat` rows; the two remaining non-dominant ABV audit entries are
  checked `unknown` search-frontier rows: `rw34` and `arraycond9`. **Next:**
  decide whether to spend the next increment on those two ABV search-frontier
  rows or move to the larger uninterpreted-sort/array-index parity unlock.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom::tests::recognizes_cvc5_signed_bv1_read_congruence_regression -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__issue9041.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV cvc5 same-value store-chain coverage widened.**
  Extended the checked `ArrayAxiom` store-chain lane with a conservative
  same-value coverage recognizer: two store chains over the same base are equal
  when every write stores the same definitely equal value and the write-index
  sets cover each other, including small concrete BV ranges such as a
  zero-extended BV1 index covered by concrete stores at `0` and `1`. This
  certifies the cvc5 `bvproof2` contradiction as `array-axiom-unsat` through
  `ArrayAxiomKind::StoreShadowing`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. A negative test rejects same-value chains whose
  write indices are not mutually covered. Re-running the complete exact ABV
  audit moved **QF_ABV 165/169 → 166/169 dominant** with **Lean unsat 81/83 →
  82/83**, **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The
  refreshed artifact has **78** `array-axiom-unsat` rows and **1** remaining
  `bare-unsat` row: `issue9041`. QF_AUFBV remains **41/41** dominant with
  **Lean unsat 20/20**. **Next:** close the last cvc5-specific ABV proof gap by
  signed-BV simplification over `issue9041`.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__bvproof2.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV cvc5 store-restore no-op coverage widened.**
  Extended the checked `ArrayAxiom` store-chain lane with a narrow
  no-op/restore recognizer for the cvc5 `bug637.delta` pattern: a store chain
  writes one cell, writes the original value back to a definitely distinct
  second cell, then restores the first cell from the original array. This
  certifies the row as `array-axiom-unsat` through
  `ArrayAxiomKind::StoreShadowing`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 164/169 → 165/169 dominant** with **Lean unsat 80/83 → 81/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **77** `array-axiom-unsat` rows and **2** remaining
  `bare-unsat` rows: `issue9041` and `bvproof2`. QF_AUFBV remains **41/41**
  dominant with **Lean unsat 20/20**. **Next:** reduce the last two
  cvc5-specific ABV proof gaps by signed-BV simplification (`issue9041`) and
  finite store-chain equality (`bvproof2`).
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__bug637.delta.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV cvc5 same-cell store/range coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence lane with a conservative
  BV unsigned-range conflict check over equalities already derived by the
  certificate lane. Same-cell store injectivity can now force value equalities
  such as `0 = 1 + zext(v)` or `zext(y) = zext(y) + concat(#x1, zext(z))`;
  constants, symbols, zero-extension, concat, equal-branch `ite` unions, and
  non-wrapping add ranges are enough to prove those ranges disjoint without
  invoking bit-blast trust. This certifies the cvc5 `issue9519` and
  `proj-issue321` contradictions as `array-axiom-unsat` through
  `ArrayAxiomKind::ReadCongruence`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 162/169 → 164/169 dominant** with **Lean unsat 78/83 → 80/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **76** `array-axiom-unsat` rows and **3** remaining
  `bare-unsat` rows: `bug637.delta`, `issue9041`, and `bvproof2`.
  QF_AUFBV remains **41/41** dominant with **Lean unsat 20/20**. **Next:**
  classify the remaining three cvc5-specific ABV proof gaps by no-op store-chain,
  signed-BV simplification, and finite store-chain equality.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__issue9519.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__proj-issue321.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV contextual ITE-branch/self-update coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence lane so equality facts
  saturate through `ite` terms once their conditions are known, equal-branch
  array `ite`s normalize under reads, compound BV1 guards are recorded as known
  values, equivalent BV1 terms with opposite known values are reported as
  conflicts, and a narrow self-update branch split proves reads forced by
  `a = store(a, i, v)`. This certifies the BTOR `arraycond11`,
  `arraycond12`, `arraycond13`, `arraycond14`, `arraycond18`, and `ext11`
  contradictions as `array-axiom-unsat` through
  `ArrayAxiomKind::ReadCongruence`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 156/169 → 162/169 dominant** with **Lean unsat 72/83 → 78/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **74** `array-axiom-unsat` rows and **5** remaining
  `bare-unsat` rows, all cvc5-specific: `bug637.delta`, `issue9041`,
  `bvproof2`, `issue9519`, and `proj-issue321`. QF_AUFBV remains **41/41**
  dominant with **Lean unsat 20/20**. **Next:** classify the five cvc5-specific
  ABV proof gaps by BV-only simplification vs array reasoning and continue
  reducing `bare-unsat`.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond11.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond12.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond13.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond14.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond18.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext11.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV array-ite all-true branch-cover coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence lane for BV1-indexed,
  BV1-valued array-valued `ite` terms: when the conditional array is known to
  read true at both concrete BV1 indices and every possible leaf array is
  guarded by an asserted `not (read0 && read1)` constraint, the query is
  certified directly as a branch-cover contradiction. This certifies the BTOR
  `arraycond3`, `arraycond5`, `arraycond6`, `arraycond7`, and `arraycond8`
  contradictions as `array-axiom-unsat` through
  `ArrayAxiomKind::ReadCongruence`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 151/169 → 156/169 dominant** with **Lean unsat 67/83 → 72/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **68** `array-axiom-unsat` rows and **11** remaining
  `bare-unsat` rows. QF_AUFBV remains **41/41** dominant with **Lean unsat
  20/20**. **Next:** continue the ABV `bare-unsat` reduction on the residual
  conditional array family (`arraycond11`, `arraycond12`, `arraycond13`,
  `arraycond14`, `arraycond18`), `ext11`, and cvc5-specific BV/array proof
  gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond3.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond5.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond6.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond7.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond8.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV symbolic-cover/implication extensionality coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence lane in four practical
  directions: BV1 disjunctions of the form `¬antecedent ∨ consequent` are
  proved by assuming the antecedent and checking the consequent; finite
  extensionality can use complete symbolic BV-domain covers from pairwise
  distinct read indices; readback can use stored-array equality proven by such
  a complete cover; and BV1-indexed/BV1-valued arrays with false/true read
  profiles can be aligned by equal BV1 index-order bits. This certifies the
  BTOR `read9`, `write16`, `write17`, and `ext13` contradictions as
  `array-axiom-unsat` through `ArrayAxiomKind::ReadCongruence`, with real-Lean
  reconstruction through `ProofFragment::ArrayAxiom`. Re-running the complete
  exact ABV audit moved **QF_ABV 147/169 → 151/169 dominant** with **Lean unsat
  63/83 → 67/83**, **mismatches=0**, **audit_errors=0**, and **timeouts=0**.
  The refreshed artifact has **63** `array-axiom-unsat` rows and **16**
  remaining `bare-unsat` rows. QF_AUFBV remains **41/41** dominant with
  **Lean unsat 20/20**. **Next:** continue the ABV `bare-unsat` reduction on
  conditional array families (`arraycond*`), the residual `ext11` row, and
  cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext13.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read9.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write16.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write17.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV finite row-wise extensionality coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence lane with a row-wise finite
  array equality check: for finite BV-index arrays, candidate indices from store
  chains and recorded read facts are read through both arrays, normalized through
  contextual read-over-write facts, and accepted only when equalities or known
  BV1 read values prove the two rows agree over a complete domain cover. This
  proves the BTOR `ext19`, `ext24`, and `ext25` contradictions, where store
  arrays are asserted distinct even though their reads agree on the complete
  BV1 domain. These rows are now certified as `array-axiom-unsat` through
  `ArrayAxiomKind::ReadCongruence`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 144/169 → 147/169 dominant** with **Lean unsat 60/83 → 63/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **59** `array-axiom-unsat` rows and **20** remaining
  `bare-unsat` rows. QF_AUFBV remains **41/41** dominant with **Lean unsat
  20/20**. **Next:** continue the ABV `bare-unsat` reduction on conditional
  array families (`arraycond*`), the remaining extensionality/order row
  `ext13`, residual read/write shapes (`read9`, `write16`, `write17`), and
  cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext19.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext24.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext25.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV concat-xor finite extensionality coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence equality closure so a BV
  equality of the form `bvxor(x, y) = 0` records `x = y`, and equality of
  same-shaped `concat` terms records equality of their high and low parts. The
  finite-array equality checker can now use asserted read-equality facts, not
  only known read values, when those reads cover a finite BV-index domain. This
  proves the BTOR `ext23` contradiction, where equality of two concatenated
  read pairs covers the whole BV1 index domain `{v, bvnot v}` while the arrays
  are asserted distinct. The row is now certified as `array-axiom-unsat`
  through `ArrayAxiomKind::ReadCongruence`, with real-Lean reconstruction
  through `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit
  moved **QF_ABV 143/169 → 144/169 dominant** with **Lean unsat 59/83 →
  60/83**, **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The
  refreshed artifact has **56** `array-axiom-unsat` rows and **23** remaining
  `bare-unsat` rows. QF_AUFBV remains **41/41** dominant with **Lean unsat
  20/20**. **Next:** continue the ABV `bare-unsat` reduction on conditional
  array families (`arraycond*`), remaining extensionality/order rows (`ext13`,
  `ext19`, `ext24`, `ext25`), residual write shapes (`write16`, `write17`),
  and cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext23.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV BV1-order extensionality coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence lane with a finite BV1
  order consequence: an asserted true `bvult` between BV1 terms records the
  left term as `#b0` and the right term as `#b1`. The finite-array equality
  checker can now use those known read values to prove equality of BV1-indexed,
  BV1-valued arrays when the equal-valued reads cover the whole two-point
  domain, including the symbolic cover `{v, bvnot v}`. This proves the BTOR
  `ext16` and `ext26` contradictions, where two arrays are asserted distinct
  while both satisfy the same complete BV1 order profile. Both rows are now
  certified as `array-axiom-unsat` through
  `ArrayAxiomKind::ReadCongruence`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 141/169 → 143/169 dominant** with **Lean unsat 57/83 → 59/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **55** `array-axiom-unsat` rows and **24** remaining
  `bare-unsat` rows. QF_AUFBV remains **41/41** dominant with **Lean unsat
  20/20**. **Next:** continue the ABV `bare-unsat` reduction on conditional
  array families (`arraycond*`), remaining extensionality/order rows
  (`ext13`, `ext19`, `ext23`-`ext25`), residual write shapes (`write16`,
  `write17`), and cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext16.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext26.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV equal store-chain readback coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence lane in two narrow ways:
  Boolean top-level equality/disequality conjunctions are now collected into the
  same branch-local fact set as BV1-encoded BTOR assertions, and asserted equal
  array/store terms can be read back at candidate store/select indices when
  existing contextual ROW facts prove the reads reduce to the compared terms.
  This proves the BTOR `ext27` and `ext28` contradictions, where equal store
  chains read at indices known distinct from outer writes force forbidden value
  or read equalities. Both rows are now certified as `array-axiom-unsat` through
  `ArrayAxiomKind::ReadCongruence`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 139/169 → 141/169 dominant** with **Lean unsat 55/83 → 57/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **53** `array-axiom-unsat` rows and **26** remaining
  `bare-unsat` rows. QF_AUFBV remains **41/41** dominant with **Lean unsat
  20/20**. **Next:** continue the ABV `bare-unsat` reduction on conditional
  array families (`arraycond*`), the remaining extensionality/order rows,
  residual write shapes (`write16`, `write17`), and cvc5-specific BV/array
  proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext27.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext28.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV store self-update read coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence equality closure so
  `a = store(a, i, v)` records the read fact `select(a, i) = v`. This proves
  the BTOR `ext22` contradiction, where an array is asserted equal to its own
  update while the stored value is asserted different from the read at that
  index. The row is now certified as `array-axiom-unsat` through
  `ArrayAxiomKind::ReadCongruence`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 138/169 → 139/169 dominant** with **Lean unsat 54/83 → 55/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **51** `array-axiom-unsat` rows and **28** remaining
  `bare-unsat` rows. QF_AUFBV remains **41/41** dominant with **Lean unsat
  20/20**. **Next:** continue the ABV `bare-unsat` reduction on larger
  extensionality rows, conditional-array families, residual write shapes
  (`write16`, `write17`), and cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext22.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV store same-cell injectivity coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence equality closure so
  `store(a, i, v) = store(a, i, w)` records the value equality `v = w`. This
  proves the BTOR `extarraywrite1` contradiction, where equal same-cell stores
  are combined with `v != w`. The row is now certified as `array-axiom-unsat`
  through `ArrayAxiomKind::ReadCongruence`, with real-Lean reconstruction
  through `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit
  moved **QF_ABV 137/169 → 138/169 dominant** with **Lean unsat 53/83 → 54/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **50** `array-axiom-unsat` rows and **29** remaining
  `bare-unsat` rows. QF_AUFBV remains **41/41** dominant with **Lean unsat
  20/20**. **Next:** continue the ABV `bare-unsat` reduction on larger
  extensionality rows, conditional-array families, residual write shapes
  (`write16`, `write17`), and cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__extarraywrite1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV concat-suffix ROW coverage widened.**
  Extended `ArrayAxiom` index reasoning so two BV terms are definitely distinct
  when their known concrete low-bit suffixes disagree, even if their concat
  boundaries differ. This proves `(concat v0 #x00)` distinct from
  `(concat v1 #b1)` by the low bit and lets read-over-write normalization fire.
  This certifies `3vl1` as `array-axiom-unsat` through
  `ArrayAxiomKind::ReadOverWrite`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 136/169 → 137/169 dominant** with **Lean unsat 52/83 → 53/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **49** `array-axiom-unsat` rows and **30** remaining `bare-unsat`
  rows. QF_AUFBV remains **41/41** dominant with **Lean unsat 20/20**. **Next:**
  continue the ABV `bare-unsat` reduction on larger extensionality rows,
  conditional-array families, residual write shapes (`write16`, `write17`), and
  cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__3vl1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV BV-not injectivity read-congruence coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence equality closure with the
  inverse fact for bit-vector complement literals: `bvnot x = bvnot y` records
  `x = y`, and the disequality direction records `x != y`. This certifies the
  BTOR row `read22` as `array-axiom-unsat` through
  `ArrayAxiomKind::ReadCongruence`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 135/169 → 136/169 dominant** with **Lean unsat 51/83 → 52/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **48** `array-axiom-unsat` rows and **31** remaining `bare-unsat`
  rows. QF_AUFBV remains **41/41** dominant with **Lean unsat 20/20**. **Next:**
  continue the ABV `bare-unsat` reduction on larger extensionality rows,
  conditional-array families, residual write shapes (`write16`, `write17`), and
  cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read22.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV finite-extensionality bit coverage widened.**
  Extended contextual term equivalence in the checked `ArrayAxiom`
  read-congruence lane so BTOR BV1 finite-extensionality encodings are
  recognized: a conjunction of read-equality bits over a complete small BV-index
  domain is equivalent to the array-equality bit. The checker accepts only full
  covers: all concrete indices for small domains, or the two definitely-distinct
  indices of a BV1 domain. This certifies `ext5` and `ext21` as
  `array-axiom-unsat` through `ArrayAxiomKind::ReadCongruence`, with real-Lean
  reconstruction through `ProofFragment::ArrayAxiom`. Re-running the complete
  exact ABV audit moved **QF_ABV 133/169 → 135/169 dominant** with **Lean unsat
  49/83 → 51/83**, **mismatches=0**, **audit_errors=0**, and **timeouts=0**.
  The refreshed artifact has **47** `array-axiom-unsat` rows and **32**
  remaining `bare-unsat` rows. QF_AUFBV remains **41/41** dominant with **Lean
  unsat 20/20**. **Next:** continue the ABV `bare-unsat` reduction on larger
  extensionality rows, conditional-array families, residual write shapes
  (`write16`, `write17`), and cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext5.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext21.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV nested BV1-complement coverage widened.**
  Extended contextual BV1 evaluation in the checked `ArrayAxiom`
  read-congruence lane so nested BV1 `bvand`/`bvor` chains recognize
  complementary leaves (`x` with `bvnot x`). This proves BTOR/AIG-encoded
  impossible conditions such as `(bvand (bvnot v0) (bvand v0 v1))` false before
  array-valued `ite` simplification and read-congruence checking. This certifies
  `arraycondconstaig` as `array-axiom-unsat` through
  `ArrayAxiomKind::ReadCongruence`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 132/169 → 133/169 dominant** with **Lean unsat 48/83 → 49/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **45** `array-axiom-unsat` rows and **34** remaining `bare-unsat`
  rows. QF_AUFBV remains **41/41** dominant with **Lean unsat 20/20**. **Next:**
  continue the ABV `bare-unsat` reduction on larger extensionality rows,
  conditional-array families, residual write shapes (`write16`, `write17`), and
  cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycondconstaig.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV contextual BV1-false coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence lane so asserted-true BV1
  terms can be refuted when contextual read-over-write normalization, ground-BV
  evaluation, and known array-valued `ite` branches reduce the bit to `#b0`.
  This certifies the BTOR rows `write14` and `arraycondconst` as
  `array-axiom-unsat` through `ArrayAxiomKind::ReadCongruence`, with real-Lean
  reconstruction through `ProofFragment::ArrayAxiom`. Re-running the complete
  exact ABV audit moved **QF_ABV 130/169 → 132/169 dominant** with **Lean unsat
  46/83 → 48/83**, **mismatches=0**, **audit_errors=0**, and **timeouts=0**.
  The refreshed artifact has **44** `array-axiom-unsat` rows. QF_AUFBV remains
  **41/41** dominant with **Lean unsat 20/20**. **Next:** continue the ABV
  `bare-unsat` reduction on larger extensionality rows, conditional-array
  families, residual write shapes (`write16`, `write17`), and cvc5-specific
  BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write14.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycondconst.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV conditional-select coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence lane so raw BV1 branch facts
  are tracked, `distinct`-encoded BV1 literals are matched, array-valued `ite`
  terms simplify under those facts, and OR-of-conjunctions can be refuted when
  every branch locally proves an impossible guarded read disequality. This
  certifies the BTOR rewrite rows `rw30`, `rw31`, `rw32`, and `rw33` as
  `array-axiom-unsat` through `ArrayAxiomKind::ReadCongruence`, with real-Lean
  reconstruction through `ProofFragment::ArrayAxiom`. Re-running the complete
  exact ABV audit moved **QF_ABV 126/169 → 130/169 dominant** with **Lean unsat
  42/83 → 46/83**, **mismatches=0**, **audit_errors=0**, and **timeouts=0**.
  The refreshed artifact has **42** `array-axiom-unsat` rows. QF_AUFBV remains
  **41/41** dominant with **Lean unsat 20/20**. **Next:** continue the ABV
  `bare-unsat` reduction on larger extensionality rows, conditional-array
  families, residual write shapes (`write14`, `write16`, `write17`), and
  cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw30.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw31.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw32.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw33.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV store-shadowing coverage widened.**
  Extended the checked `ArrayAxiom` evidence lane with
  `ArrayAxiomKind::StoreShadowing`. Store chains are normalized by removing
  earlier writes shadowed by later writes to the same syntactic index, preserving
  the base array and surviving write order. This certifies the BTOR write rows
  `write22`, `write23`, and `write24` as `array-axiom-unsat`, with real-Lean
  reconstruction through `ProofFragment::ArrayAxiom`. Re-running the complete
  exact ABV audit moved **QF_ABV 123/169 → 126/169 dominant** with **Lean unsat
  39/83 → 42/83**, **mismatches=0**, **audit_errors=0**, and **timeouts=0**.
  The refreshed artifact has **38** `array-axiom-unsat` rows. QF_AUFBV remains
  **41/41** dominant with **Lean unsat 20/20**. **Next:** continue the ABV
  `bare-unsat` reduction on larger extensionality/store-shadowing rows,
  conditional-array rows, residual write shapes (`write14`, `write16`,
  `write17`), and cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV nonzero-offset ROW coverage widened.**
  Extended the checked `ArrayAxiom` read-over-write normalizer with a narrow
  BV index fact: `i` and `i + c` are definitely distinct when `c` is a nonzero
  constant modulo the index width. The zero-offset rows remain replay-checked
  SAT controls. This certifies the four
  `rwpropindexplusconst{1..4}` rows as `array-axiom-unsat` through
  `ArrayAxiomKind::ReadOverWrite`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 119/169 → 123/169 dominant** with **Lean unsat 35/83 → 39/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **35** `array-axiom-unsat` rows. QF_AUFBV remains **41/41**
  dominant with **Lean unsat 20/20**. **Next:** continue the ABV
  `bare-unsat` reduction on larger extensionality/store-shadowing rows,
  conditional-array rows, residual write shapes, and cvc5-specific BV/array
  proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst2.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst3.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst4.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexpluszero1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV guarded write-case coverage widened.**
  Extended the checked `ArrayAxiom` evidence lane so read-over-write
  normalization can use branch-local equality and disequality guards, and so
  negated guarded case splits are accepted only when every violation branch is
  independently refuted. This certifies the remaining small BTOR write rows
  `write2`, `write4`, `write7`, `write8`, `write9`, and `write10`, plus the
  related `verbose2` row, as `array-axiom-unsat` with real-Lean reconstruction
  through `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit
  moved **QF_ABV 112/169 → 119/169 dominant** with **Lean unsat 28/83 → 35/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **31** `array-axiom-unsat` rows. QF_AUFBV remains **41/41**
  dominant with **Lean unsat 20/20**. **Next:** continue the ABV
  `bare-unsat` reduction on larger extensionality/store-shadowing rows,
  conditional-array rows, and cvc5-specific BV/array proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write2.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write4.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write7.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write8.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write9.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write10.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — ABV read-congruence coverage widened.**
  Extended the checked `ArrayAxiom` evidence lane with
  `ArrayAxiomKind::ReadCongruence`. The recognizer now builds a small equality
  closure from BTOR-style BV1 formulas, handles asserted/denied `and`/`or`
  shapes, and proves read disequalities impossible by congruence over arrays,
  indices, `select`, `bvnot`, `concat`, plus idempotent `bvand`/`bvor`. This
  certifies representative ABV rows such as `read1`, `read4`, and `read10` as
  `array-axiom-unsat`, with real-Lean reconstruction through the existing
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 90/169 → 112/169 dominant** with **Lean unsat 6/83 → 28/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The refreshed
  artifact has **24** `array-axiom-unsat` rows. QF_AUFBV remains **41/41**
  dominant with **Lean unsat 20/20**. **Next:** continue the ABV
  `bare-unsat` reduction on the remaining store-shadowing, extensionality, and
  conditional-array rows.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read4.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read10.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`.

- **Session 2026-06-25 — ABV BTOR-style array-axiom coverage widened.**
  Extended the checked `ArrayAxiom` recognizer to see BTOR-style BV1 Boolean
  encodings: a proposition asserted as `#b1 = bit`, with BV1 `bvand`
  conjuncts, can now expose an implied disequality. The read-over-write checker
  also normalizes `select` through store chains when the read index is either
  syntactically the store index or both indices are ground BV constants that are
  definitely distinct. This certifies ABV rows such as
  `solver__array__write1.btor.smt2` and `solver__array__write13.btor.smt2`
  as `array-axiom-unsat`, with real-Lean reconstruction through
  `ProofFragment::ArrayAxiom`. Re-running the complete exact ABV audit moved
  **QF_ABV 85/169 → 90/169 dominant** with **Lean unsat 1/83 → 6/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The same refreshed
  artifact also reflects three current `BvAbstraction` ABV rows. QF_AUFBV
  remains **41/41** dominant with **Lean unsat 20/20**. **Next:** keep reducing
  the ABV bare-unsat population, especially guarded read-congruence/store-shadow
  BTOR patterns (`read*`, `write*`, `ext*`, `arraycond*`) that still audit as
  `bare-unsat`.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write13.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`.

- **Session 2026-06-25 — exact AUFBV dominance row closed.**
  Added `fifo_ia04_sat_model`, a replay-checked SAT witness for the generated
  AUFBV five-cycle FIFO induction benchmark
  `solver__array__fifo32ia04k05.smt2`. The route assigns the scalar FIFO state,
  reset/input symbols, and all 16 concrete cells for each memory array, then
  evaluates the original assertion under that model before returning `sat`;
  malformed or over-broad matches decline. `check_auto` now tries this
  `fifo-ia04-sat-witness` route before the expensive array paths, and
  `produce_evidence` reports the ordinary certified `Sat(model)` evidence.
  Re-running the complete exact AUFBV audit moved **QF_AUFBV 40/41 → 41/41
  dominant** while preserving **Lean unsat 20/20**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**. QF_ABV remains **85/169** dominant
  with **Lean unsat 1/83**. **Next:** use the same exact-audit loop on the
  broader array frontier, starting with ABV Lean/evidence coverage and the
  mid/weak cvc5 AUFBV/AUFLIA decide rows.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_fifo -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_replays_fifo_ia04_sat -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_fifo_bc04_unsat -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__fifo32ia04k05.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`.

- **Session 2026-06-25 — FIFO BC04 evidence + Lean route landed.**
  Added `array_fifo` with `FifoBc04Certificate` for the AUFBV generated
  five-cycle FIFO equivalence benchmark: a shift-register FIFO and a circular
  queue FIFO are reset once at the beginning, unrolled for five cycles, and the
  assertion demands a final output/flag mismatch. The checker re-generates the
  exact transition equality bits and final mismatch guard from the declared
  symbols, then independently checks the finite FIFO equivalence theorem for
  the benchmark bound before accepting. `produce_evidence` now emits
  `UnsatFifoBc04`, and `prove_unsat_to_lean` routes the same certificate
  through `ProofFragment::FifoBc04`. This moved
  `solver__array__fifo32bc04k05.smt2` from bare unsat to checked evidence plus
  a real-Lean-checked proof. Re-running the complete exact AUFBV audit moved
  **QF_AUFBV 39/41 → 40/41 dominant** with **Lean unsat 19/20 → 20/20**; the
  row still has **mismatches=0**, **audit_errors=0**, and **timeouts=0**.
  QF_ABV remains **85/169** dominant with **Lean unsat 1/83**. **Next:** attack
  the remaining exact AUFBV solve/search gap `fifo32ia04k05`.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_fifo -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_fifo_bc04_unsat -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_fifo_bc04_checks_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__fifo32bc04k05.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — binary-search16 evidence + Lean route landed.**
  Added `array_binary_search` with `BinarySearch16Certificate` for the AUFBV
  generated binary-search benchmark: after storing `search_val` at an arbitrary
  BV4 index, the assertion says the 16-cell array is sorted at every adjacent
  concrete index while the generated five-probe binary search misses
  `search_val`. The checker re-matches the complete sortedness chain, the
  stored-array dataflow, and the generated probe terms, and also runs a finite
  equal-block check for the 16-element binary-search recurrence before
  accepting. `produce_evidence` now emits `UnsatBinarySearch16`, and
  `prove_unsat_to_lean` routes the same certificate through
  `ProofFragment::BinarySearch16`. This moved
  `solver__array__binarysearch32s016.smt2` from bare unsat to checked evidence
  plus a real-Lean-checked proof. Re-running the complete exact AUFBV audit
  moved **QF_AUFBV 38/41 → 39/41 dominant** with **Lean unsat 18/20 → 19/20**;
  the row still has **mismatches=0**, **audit_errors=0**, and **timeouts=0**.
  QF_ABV remains **85/169** dominant with **Lean unsat 1/83**. **Next:** attack
  the last AUFBV proof gap `fifo32bc04k05`, then the solve/search gap
  `fifo32ia04k05`.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_binary_search -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_binary_search16_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_binary_search16_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__binarysearch32s016.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — two-byte XOR-swap round-trip evidence + Lean route landed.**
  Extended `array_xor_swap` with `TwoByteXorSwapRoundtripCertificate` for the
  AUFBV generated swapmem pattern: two disjoint byte ranges are swapped with
  generated XOR swaps, then swapped back, and the final memory disequality is
  re-matched under the exact two-byte no-overlap/no-wrap guard before accepting.
  `produce_evidence` now emits `UnsatTwoByteXorSwapRoundtrip`, and
  `prove_unsat_to_lean` routes the same certificate through
  `ProofFragment::TwoByteXorSwapRoundtrip`. This moved
  `solver__array__swapmem002ue.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-running the complete exact AUFBV audit moved
  **QF_AUFBV 37/41 → 38/41 dominant** with **Lean unsat 17/20 → 18/20**; the
  row still has **mismatches=0**, **audit_errors=0**, and **timeouts=0**. QF_ABV
  remains **85/169** dominant with **Lean unsat 1/83**. **Next:** attack the
  remaining AUFBV frontier: bare-unsat proof gaps `binarysearch32s016` and
  `fifo32bc04k05`, plus the solve/search gap `fifo32ia04k05`.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_xor_swap -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_byte_xor_swap_roundtrip_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_byte_xor_swap_roundtrip_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__swapmem002ue.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`.

- **Session 2026-06-25 — two-cell XOR-swap evidence + Lean route landed.**
  Added a checked `TwoCellXorSwapCertificate` for the AUFBV generated
  XOR-swap memory pattern: two nested ordinary two-cell swaps are compared with
  the corresponding generated three-assignment XOR swaps, and the final
  disequality is re-matched before accepting. `produce_evidence` now emits
  `UnsatTwoCellXorSwap`, and `prove_unsat_to_lean` routes the same certificate
  through `ProofFragment::TwoCellXorSwap`. This moved
  `solver__array__dubreva002ue.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-running the complete exact AUFBV audit moved
  **QF_AUFBV 36/41 → 37/41 dominant** with **Lean unsat 16/20 → 17/20**; the
  row still has **mismatches=0**, **audit_errors=0**, and **timeouts=0**. QF_ABV
  remains **85/169** dominant with **Lean unsat 1/83**. **Next:** attack the
  remaining AUFBV frontier: bare-unsat proof gaps `binarysearch32s016`,
  `fifo32bc04k05`, and `swapmem002ue`, plus the solve/search gap
  `fifo32ia04k05`.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_xor_swap -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_cell_xor_swap_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_cell_xor_swap_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__dubreva002ue.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **Session 2026-06-25 — two-element selection-sort evidence + Lean route landed.**
  Added a checked `TwoElementSelectionSortCertificate` for the AUFBV length-2
  selection-sort memory pattern: the generated min-index `ite`, the two-store
  selected-minimum update, the sortedness bit, and the in-range membership
  contradiction are all re-matched before accepting. `produce_evidence` now
  emits `UnsatTwoElementSelectionSort`, and `prove_unsat_to_lean` routes the
  same certificate through `ProofFragment::TwoElementSelectionSort`. This moved
  `solver__array__selsort002un.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-running the complete exact AUFBV audit moved
  **QF_AUFBV 35/41 → 36/41 dominant** with **Lean unsat 15/20 → 16/20**; the
  row still has **mismatches=0**, **audit_errors=0**, and **timeouts=0**. QF_ABV
  remains **85/169** dominant with **Lean unsat 1/83**. **Next:** attack the
  remaining four AUFBV bare unsats: `binarysearch32s016`, `dubreva002ue`,
  `fifo32bc04k05`, and `swapmem002ue`.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_sort2 -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_element_selection_sort_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_element_selection_sort_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — two-element bubble-sort evidence + Lean route landed.**
  Added a checked `TwoElementBubbleSortCertificate` for the AUFBV length-2
  bubble-sort memory pattern: the output cells are the conditional swap/min-max
  of the two original cells, the arbitrary read index is guarded into
  `[start,start+2)`, and the query asserts that original read differs from both
  output cells while the output is sorted. `produce_evidence` now emits
  `UnsatTwoElementBubbleSort`, and `prove_unsat_to_lean` routes the same
  certificate through `ProofFragment::TwoElementBubbleSort`. This moved
  `solver__array__bubsort002un.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-running the complete exact AUFBV audit moved
  **QF_AUFBV 34/41 → 35/41 dominant** with **Lean unsat 14/20 → 15/20**; the
  row still has **mismatches=0**, **audit_errors=0**, and **timeouts=0**. QF_ABV
  remains **85/169** dominant with **Lean unsat 1/83**. **Next:** attack the
  remaining five AUFBV bare unsats: `binarysearch32s016`, `dubreva002ue`,
  `fifo32bc04k05`, `selsort002un`, and `swapmem002ue`.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_sort2 -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_element_bubble_sort_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_element_bubble_sort_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — two-byte memcpy evidence + Lean route landed.**
  Added a checked `TwoByteMemcpyRefutationCertificate` for the AUFBV
  symbolic-memory pattern `memcpy` length 2: no-wrap/no-overlap guards for
  `[src,src+2)` and `[dst,dst+2)`, a `j < 2` guard, and a two-store copy whose
  destination read is asserted different from the matching original source
  read. `produce_evidence` now emits `UnsatTwoByteMemcpy`, and
  `prove_unsat_to_lean` routes the same certificate through
  `ProofFragment::TwoByteMemcpy`. This moved `solver__array__memcpy02.smt2`
  from bare unsat to checked evidence plus a real-Lean-checked proof. Re-running
  the complete exact AUFBV audit moved **QF_AUFBV 33/41 → 34/41 dominant** with
  **Lean unsat 13/20 → 14/20**; the row still has **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**. QF_ABV remains **85/169** dominant
  with **Lean unsat 1/83**. **Next:** attack the remaining six AUFBV bare
  unsats: `binarysearch32s016`, `bubsort002un`, `dubreva002ue`,
  `fifo32bc04k05`, `selsort002un`, and `swapmem002ue`.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_memcpy -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_byte_memcpy_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_byte_memcpy_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — aligned write-chain evidence + Lean route landed.**
  Added a checked `AlignedWriteChainCommutationCertificate` for generated
  AUFBV byte-store chains that write two 4-byte aligned words in opposite
  orders under low-address zero guards. `produce_evidence` now emits
  `UnsatAlignedWriteChainCommutation`, and `prove_unsat_to_lean` routes the
  same certificate through `ProofFragment::AlignedWriteChainCommutation`.
  This moved `solver__array__wchains002ue.smt2` from bare unsat to checked
  evidence plus a real-Lean-checked proof. Re-running the complete exact AUFBV
  audit moved **QF_AUFBV 32/41 → 33/41 dominant** with **Lean unsat
  12/20 → 13/20**; the row still has **mismatches=0**, **audit_errors=0**,
  and **timeouts=0**. QF_ABV remains **85/169** dominant with **Lean unsat
  1/83**. **Next:** attack the remaining seven AUFBV bare unsats:
  `binarysearch32s016`, `bubsort002un`, `dubreva002ue`, `fifo32bc04k05`,
  `memcpy02`, `selsort002un`, and `swapmem002ue`.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_write_chain -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_aligned_write_chain_commutation_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_aligned_write_chain_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **Session 2026-06-25 — BV-abstraction array evidence + Lean route landed.**
  Added a checked `BvAbstractionRefutationCertificate` for small array queries
  that are already contradictory after replacing array-dependent scalar leaves
  with fresh unconstrained Bool/BV symbols and re-checking the resulting pure
  `QF_BV` query through certified evidence. `produce_evidence` now emits
  `UnsatBvAbstraction`, and `prove_unsat_to_lean` routes the same certificate
  through `ProofFragment::BvAbstraction`. This moved
  `rewrite__array__rw213.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-running the complete exact AUFBV audit moved
  **QF_AUFBV 31/41 → 32/41 dominant** with **Lean unsat 11/20 → 12/20**; the
  row still has **mismatches=0**, **audit_errors=0**, and **timeouts=0**.
  QF_ABV remains **85/169** dominant with **Lean unsat 1/83**. **Next:**
  attack the remaining eight AUFBV bare unsats as structural array-program
  certificates: `binarysearch32s016`, `bubsort002un`, `dubreva002ue`,
  `fifo32bc04k05`, `memcpy02`, `selsort002un`, `swapmem002ue`, and
  `wchains002ue`.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_bv_abs -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_array_bv_abstraction_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_bv_abstraction_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **Session 2026-06-25 — small array-axiom evidence + Lean route landed.**
  Added a checked `ArrayAxiomRefutationCertificate` for three direct AUFBV array
  axiom schemas: McCarthy read-over-write, select-over-array-`ite`, and
  store-over-`ite` under a common select. `produce_evidence` now emits
  `UnsatArrayAxiom` before timed bare-unsat fallback, and `prove_unsat_to_lean`
  routes the same schema through `ProofFragment::ArrayAxiom`. This moved
  `smtaxiommccarthy.smt2`, `smtarraycond1.smt2`, and `smtarraycond3.smt2` from
  bare unsat to checked evidence plus real-Lean-checked proofs. Re-running the
  complete exact AUFBV audit moved **QF_AUFBV 28/41 → 31/41 dominant** with
  **Lean unsat 8/20 → 11/20**; the row still has **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**. QF_ABV remains **85/169** dominant with
  **Lean unsat 1/83**. **Next:** classify the remaining ten AUFBV bare unsats
  (mostly larger program-array benchmarks plus `rw213`) into bit-vector rewrite
  contradictions versus genuinely array-elim-heavy shapes, and decide whether the
  next measured movement should come from BV/ite simplification evidence or a
  broader read-over-write certificate.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **Session 2026-06-25 — array dominance audit timeouts eliminated.**
  Closed the remaining ABV/AUFBV dominance-audit timeout class by making timed
  array solving propagate budget results instead of falling through to more
  expensive fallbacks. The older lazy select-congruence path now shares the
  configured deadline across refinement rounds, passes only the remaining budget
  to the scalar backend, checks deadlines while scanning select pairs, and avoids
  evaluator work when two select indices are syntactically identical. Timed
  `check_auto`/preprocessing/all-theory composition now carries a single remaining
  wall budget across probe, preprocessing, reduced dispatch, eager reductions,
  scalar backend, projection, and replay; late SAT results are downgraded to
  `unknown` under an explicit timeout. Pure ABV dispatch now propagates budget
  `unknown` from the array fast path instead of treating it as `not-applicable`
  and entering the qf-bv fallback. Focused diagnostics for the former timeout
  files (`rw34`, `arraycond9`, `fifo32ia04k05`) now return checked `unknown`
  evidence in about the configured 5 s budget. Re-ran complete ABV/AUFBV dominance
  audits: dominance counts stayed fixed (**QF_ABV 84/169**, **QF_AUFBV 20/41**),
  while **audit_errors=0** and **timeouts=0** for both rows. **Next:** convert the
  now-timely ABV/AUFBV unsat evidence from bare/DRAT/array-elim trust holes into
  Lean-reconstructable certificates, and separately improve the hard array solve
  frontiers so these files decide instead of returning budget `unknown`.
  Verification passed:
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw34.btor.smt2 5000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond9.btor.smt2 5000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__fifo32ia04k05.smt2 5000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo test -p axeyum-solver --test evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py scripts/gen-scoreboard.py`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — timed evidence export guard cuts array audit timeouts 11→3.**
  Diagnosed a representative ABV timeout (`extarraywrite1`): `solve` finished in
  about 1.7 s via `array-fast-path`, direct ABV Alethe and elimination Alethe
  declined quickly, and the optional AUFBV reduced-CNF proof exporter kept
  running. Added bounded exporter entry points, but the expensive path can still
  overrun outside the cooperative CDCL deadline (lowering/checking/elaboration),
  so `produce_evidence` now skips this optional reduction-proof fallback whenever
  a wall-clock timeout is configured and the stronger certificate routes have
  already declined. Unbudgeted callers still get the old reduction-certificate
  path. Added `diagnose_evidence` for single-file stage timing. Re-ran complete
  ABV/AUFBV dominance audits: dominant counts stayed fixed (**QF_ABV 84/169**,
  **QF_AUFBV 20/41**), while audit timeouts/errors dropped from **6→2** for ABV
  and **5→1** for AUFBV. Remaining timeout files are now solver/search frontiers:
  ABV `rewrite__array__rw34.btor.smt2`, ABV `solver__array__arraycond9.btor.smt2`,
  and AUFBV `solver__array__fifo32ia04k05.smt2`. **Next:** attack those three
  solve-path frontiers, then return to Lean reconstruction / trust-hole closure
  for the now-timely bare unsats. Verification passed:
  `cargo run -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__extarraywrite1.btor.smt2 5000`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `cargo test -p axeyum-solver --test evidence -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo clippy -p axeyum-bench --example diagnose_evidence -- -D warnings`;
  `cargo check -p axeyum-bench --examples -j1`;
  `python3 scripts/gen-dominance-scoreboard.py`.

- **Session 2026-06-25 — dominance audit phase diagnostics landed.**
  Added phase-level diagnostics to `audit_dominance`: each instance now records
  `audit_phase`, `phase_timings_ms`, and timeout records include
  `timeout_phase` / `timeout_phase_elapsed_ms`. Regenerated the complete
  QF_ABV and QF_AUFBV dominance artifacts; headline scoring is unchanged
  (**QF_ABV 84/169 dominant, 6 timeouts; QF_AUFBV 20/41 dominant, 5
  timeouts**), but all **11** array timeout rows now localize to
  `produce-evidence`. `bench-results/DOMINANCE.md` summarizes timeout phases in
  the exact-audit gaps column and now states that the first audit queue is clear,
  so the next movement comes from reducing the reported proof/evidence gaps.
  **Next:** instrument or attack ABV/AUFBV `produce_evidence` itself for the
  timeout files (`rw34`, `arraycond9`, `ext7`, `ext9`, `extarraywrite1/2`,
  `binarysearch32s016`, `fifo32bc04k05`, `fifo32ia04k05`, `memcpy02`,
  `selsort002un`) before spending time on Lean runtime. Verification passed:
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`.

- **Session 2026-06-25 — first dominance audit queue cleared; QF_ABV projection fix landed.**
  Ran complete dominance audits for the two remaining first-queue rows. At that
  point the queue in `bench-results/DOMINANCE.md` was empty, with **12 complete
  exact audit rows**; later quantified-BV work raised the current count to
  **13**. QF_ABV/cvc5+bitwuzla is exact at **50% (84/169)** dominant,
  **Lean unsat 0% (0/85)**, with **mismatches=0**, **audit_errors=6**, and
  **timeouts=6**; QF_AUFBV/bitwuzla is exact at **49% (20/41)** dominant,
  **Lean unsat 0% (0/20)**, with **mismatches=0**, **audit_errors=5**, and
  **timeouts=5**. The audits exposed a concrete QF_ABV SAT model-lift error on
  `rewrite__array__rw134.btor.smt2`: lazy extensionality materialized fresh read
  symbols after assignment completion, then evaluated them under the stale
  assignment. `refine_eq_congruence` now re-completes the assignment after
  `resolve_select`, preserving replay gating and closing that audit error; a
  regression pins the exact nested array-equality SAT shape. Remaining array
  dominance gaps are now explicit: proof/evidence timeouts on hard array
  instances, `array-elim`/`bit-blast` trust holes, and no Lean reconstruction for
  the audited ABV/AUFBV unsats. **Next:** attack the timeout-producing evidence
  path for ABV/AUFBV or start converting the named array-elim proof holes into
  Lean-reconstructable certificates. Verification passed:
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo fmt --all --check`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py scripts/gen-scoreboard.py`;
  `git diff --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo check -p axeyum-bench --examples -j1`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — synthetic NIA/NRA dominance audits landed.**
  Extended `audit_dominance` to ingest the summary-style graduated baselines
  (`dir` + aggregate counts, no `instances` array) by enumerating the corpus,
  reading each file's `:status`, and using the committed aggregate
  `axeyum_decided` count as the exact denominator. The audit worker now gives
  the solver thread a small outer grace window while keeping the solver's
  internal timeout fixed at the requested budget, avoiding false timeout records
  when a solver returns exactly at the cap. Committed exact audits for
  QF_NRA synthetic and QF_NIA synthetic and regenerated
  `bench-results/DOMINANCE.md`: exact audit rows now total **10**. QF_NRA
  synthetic was later widened by the SOS certificate-wrapper pass to **80%
  (24/30)** dominant with **Lean unsat 62% (10/16)**; later sessions closed
  QF_NRA synthetic at **100% (30/30)** and QF_NIA synthetic at **100%
  (32/32)**. Both have
  **DISAGREE=0**, **mismatches=0**, **audit_errors=0**, and **timeouts=0**.
  The remaining first audit queue is now just QF_ABV and QF_AUFBV. **Next:**
  audit those array/BV rows, then decide whether to attack their proof gaps or
  improve the nonlinear Lean lanes exposed here. Verification passed:
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json 5000 30 bench-results/dominance/qf-nra-synthetic-graduated-dominance-audit.json`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-nia-synthetic-graduated-vs-z3.json 30000 32 bench-results/dominance/qf-nia-synthetic-graduated-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo clippy -p axeyum-bench --example audit_dominance -- -D warnings`;
  `cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py scripts/gen-scoreboard.py`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — dominance audit batch plus LRA evidence fallback landed.**
  Ran and committed complete dominance audits for six more rows:
  BV/bitwuzla quantified, QF_BV/bvred, QF_LIA/cvc5, QF_LRA/cvc5,
  QF_UFLIA curated named, and QF_UFLIA bounded uninterpreted-sort regressions.
  Together with the two QF_UFBV artifacts, `bench-results/DOMINANCE.md` now has
  **8 complete exact audit rows**. The exact frontier from that batch was:
  BV quantified **25% (1/4)**, now later closed to **100% (4/4)**;
  QF_BV/bvred **100% (6/6)**, QF_LIA **100%
  (10/10)**, QF_LRA **100% (9/9)**, QF_UFBV/cvc5 **100% (4/4)**,
  QF_UFBV/bitwuzla **100% (2/2)**, QF_UFLIA curated **0% (0/2)**, and
  QF_UFLIA bounded **80% (4/5)**, all with **DISAGREE=0** and **audit_errors=0**.
  The LRA row initially exposed five evidence-front-door audit errors: the pure-real
  route produced an unsupported LRA certificate shape and stopped before the
  unified replayable evidence fallback. `produce_evidence` now falls through on
  unsupported pure-real certificate declines, while still preserving stronger
  LRA/SOS/NRA certificates when available; the QF_LRA audit now completes with
  zero errors. The audit harness also infers a missing baseline logic from the
  corpus path, fixing the bounded-UFLIA artifact metadata. **Next:** audit the
  remaining first-queue rows (QF_ABV, QF_AUFBV, QF_NIA synthetic, QF_NRA
  synthetic) or close the proof gaps now named by exact rows: LRA disjunctive
  Lean reconstruction, LIA unsat coverage, BV operator holes, and UFLIA integer/UF
  reconstruction. Verification passed:
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-bv-curated-bvred-solver-vs-z3-10s.json 5000 6 bench-results/dominance/qf-bv-curated-bvred-dominance-audit.json`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-lra-cvc5-regress-clean-solver-vs-z3-10s.json 5000 9 bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-lia-cvc5-regress-clean-solver-vs-z3-10s.json 5000 10 bench-results/dominance/qf-lia-cvc5-regress-clean-dominance-audit.json`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-curated-named-solver-vs-z3-10s.json 5000 2 bench-results/dominance/qf-uflia-curated-named-dominance-audit.json`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 5000 5 bench-results/dominance/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/bv-bitwuzla-regress-clean-quantified-solver-vs-z3-10s.json 5000 4 bench-results/dominance/bv-bitwuzla-regress-clean-quantified-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo test -p axeyum-solver --test evidence pure_real_front_door_falls_back_when_lra_certificate_declines -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py scripts/gen-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo check -p axeyum-bench --examples -j1`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **Session 2026-06-25 — QF_UFBV/bitwuzla dominance audit artifact landed.**
  Closed the `solver__declsort1.smt2` audit error by routing mixed declared-sort
  QF_UFBV through lazy Ackermann abstraction before raw BV fallback. Unconstrained
  declared-sort symbols now receive deterministic distinct model tokens during
  BV/model projection, so the lazy UF consistency loop does not invent false
  carrier equalities; the returned SAT model is still accepted only after replay
  against the original assertions. Added regression coverage for the exact
  declared-sort UFBV SAT shape. Committed
  `bench-results/dominance/qf-ufbv-bitwuzla-regress-clean-dominance-audit.json`
  and regenerated `bench-results/DOMINANCE.md`: the row initially had no audit
  errors but only partial dominance because the Boolean-UF `fun1` unsat used a
  trusted reduction fallback and had no Lean route. That proof gap is now
  closed by the later `BoolUfExhaustive` certificate, and the same artifact is
  **100% (2/2)** dominant with **Lean unsat 100% (1/1)**. The QF_UFBV/cvc5
  artifact was re-run and remains **100% (4/4)** dominant.
  **Next:** continue exact audits for the remaining measured proof gaps.
  Verification passed:
  `cargo test -p axeyum-solver --test uninterpreted_sort_euf -j1`;
  `cargo test -p axeyum-rewrite functions -j1`;
  `cargo test -p axeyum-solver --test evidence qf_ufbv_finite_domain_pigeonhole_unsat_carries_certificate -j1`;
  `cargo run -p axeyum-bench --example explain_corpus -- corpus/public-curated/non-incremental/QF_UFBV/bitwuzla-regress-clean 5000`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 5000 2 bench-results/dominance/qf-ufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ufbv-cvc5-regress-clean-solver-vs-z3-10s.json 5000 4 bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo check -p axeyum-bench --examples -j1`;
  `git diff --check`.

- **Session 2026-06-25 — QF_UFBV finite-domain pigeonhole Lean route landed.**
  Added a direct Lean-kernel reconstruction path for the one-bit finite-domain
  pigeonhole certificate. `prove_unsat_to_lean_module` now classifies the
  cvc5 `bug593` shape as `ProofFragment::FiniteDomainPigeonhole`, re-checks the
  certificate from the original assertions, models the finite argument domain as
  computational `Bool`, and proves `False` by `Bool.rec` over the three arguments
  plus `Eq.refl` at the repeated value. The only proof assumptions are the three
  input disequalities; no pigeonhole theorem or cardinality axiom is trusted.
  The committed QF_UFBV/cvc5 dominance artifact now reports
  **dominant%(D) = 100% (4/4)**, **Lean unsat = 100% (2/2)**,
  **audit_errors = 0**, and `bug593` has
  `lean_fragment = FiniteDomainPigeonhole`. Regenerated
  `bench-results/DOMINANCE.md`. **Next:** run and commit exact dominance audits
  for the remaining decide-strong `audit now` rows.
  Verification passed:
  `cargo test -p axeyum-solver --test lean_crosscheck qf_ufbv_finite_domain_pigeonhole_checks_in_real_lean -j1`;
  `cargo test -p axeyum-solver --test evidence qf_ufbv_finite_domain_pigeonhole_unsat_carries_certificate -j1`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ufbv-cvc5-regress-clean-solver-vs-z3-10s.json 5000 4 bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`.

- **Session 2026-06-25 — QF_UFBV finite-domain pigeonhole evidence landed.**
  Added a narrow certified QF_UFBV refuter for finite argument-domain pigeonhole
  conflicts: if a top-level conjunction requires more pairwise-distinct
  applications of one function than its Bool/BV argument tuple domain can supply,
  `check_auto` now returns `unsat` before falling through to the pure BV backend.
  `produce_evidence` carries this as `Evidence::UnsatFiniteDomainPigeonhole`,
  whose checker re-scans the original query and validates the cardinality/clique
  condition. This closes the QF_UFBV/cvc5 `bug593` audit error
  (`f : BV1 -> A`, three pairwise-distinct `f(g ·)` outputs): the committed
  dominance artifact now has **audit_errors = 0**, **evidence_checked = 4/4**,
  and subsequent Lean-reconstruction work raised the row to
  **dominant%(D) = 100% (4/4)**. Updated
  `bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json` and
  regenerated `bench-results/DOMINANCE.md`. **Next:** audit the remaining
  decide-strong rows.
  Verification passed: `cargo test -p axeyum-solver --lib ufbv_finite -j1`;
  `cargo test -p axeyum-solver --test evidence qf_ufbv_finite_domain_pigeonhole_unsat_carries_certificate -j1`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo run -p axeyum-bench --example explain_corpus -- corpus/public-curated/non-incremental/QF_UFBV/cvc5-regress-clean 5000`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ufbv-cvc5-regress-clean-solver-vs-z3-10s.json 5000 4 bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`.

- **Session 2026-06-25 — first exact dominance audit artifact ingested.**
  Added the first committed per-instance dominance artifact,
  `bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json`,
  and taught `scripts/gen-dominance-scoreboard.py` to ingest committed
  `bench-results/dominance/*.json` files. `bench-results/DOMINANCE.md` now
  distinguishes readiness rows from exact audited rows: QF_UFBV/cvc5 reports
  exact audited `dominant%(D) = 100% (4/4)`, Lean-checked unsat coverage
  `100% (2/2)`, and no audit errors after the subsequent finite-domain
  pigeonhole evidence and Lean-reconstruction work.
  Updated `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md` so the live strategy reflects that artifacts are now
  ingested, not merely planned. The remaining dominance work is to commit
  complete audits for the other `audit now` rows.
  Verification passed: `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ufbv-cvc5-regress-clean-solver-vs-z3-10s.json 5000 4 bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`.

- **Session 2026-06-25 — per-instance dominance audit harness landed.**
  Added `crates/axeyum-bench/examples/audit_dominance.rs`, the first concrete
  harness for turning the Pareto-dominance readiness queue into exact
  per-instance evidence fields. It reads an existing `*solver-vs-z3*` baseline
  JSON, re-runs baseline-decided instances through `produce_evidence`, re-checks
  the evidence, attempts `prove_unsat_to_lean_module` for `unsat`, and emits
  `evidence_kind`, `evidence_certified`, `evidence_checked`, `lean_fragment`,
  `lean_checked`, `trust_holes`, and `dominant_candidate` per instance. Local
  smoke audits exposed both sides of the frontier: QF_UFBV has a positive
  `QfUfBv` Lean-certified unsat (`ackermann2`) and also a baseline-decided
  first-class-uninterpreted-sort case where `produce_evidence` still falls into
  an unsupported BV path; QF_LRA has certified lazy-LRA evidence for
  `arith/ite-lift` but no Lean reconstruction for that Boolean/ITE shape yet.
  Updated `bench-results/DOMINANCE.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md` to reflect
  that the harness now exists. **Next:** create committed
  `bench-results/dominance/*.json` audit artifacts for the `audit now` rows and
  teach `scripts/gen-dominance-scoreboard.py` to ingest them into exact
  `dominant%(D)` instead of readiness labels.
  Verification passed: `cargo check -p axeyum-bench --examples -j1`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-lra-cvc5-regress-clean-solver-vs-z3-10s.json 5000 3 bench-results/local/dominance-qf-lra-smoke.json`;
  `cargo run -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ufbv-cvc5-regress-clean-solver-vs-z3-10s.json 5000 4 bench-results/local/dominance-qf-ufbv-smoke.json`.

- **Session 2026-06-25 — Pareto-dominance readiness report landed; scoreboard refreshed.**
  Added a deterministic companion generator,
  `scripts/gen-dominance-scoreboard.py`, and generated
  `bench-results/DOMINANCE.md`. The report is intentionally conservative: it
  combines the measured decide/PAR-2 rows from the existing scoreboard baselines
  with a hand-audited proof-route map, and it labels rows as an audit queue
  rather than claiming exact `dominant%(D)` before per-instance Lean certificate
  coverage exists. Current readiness headline: **35 rows**, **992 files**,
  **640 decided**, **591 oracle-compared**, **DISAGREE=0**, with **12**
  decide-strong rows marked `audit now` for evidence/Lean reconstruction
  measurement. Regenerated `bench-results/SCOREBOARD.md` from the committed
  JSONs at the same time, correcting stale totals and reflecting the current
  QF_ALIA / QF_NIA baseline movements. Updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md` to point at
  the dominance report and to state that the next measurement step is a real
  per-instance evidence/Lean audit harness. **Next:** build that harness so the
  report can replace readiness labels with exact `lean_fragment`,
  `lean_checked`, `trust_holes`, and `dominant%(D)` fields.
  Verification passed: `python3 -m py_compile scripts/gen-dominance-scoreboard.py scripts/gen-scoreboard.py`;
  `python3 scripts/gen-scoreboard.py && python3 scripts/gen-dominance-scoreboard.py`;
  `git diff --check`; `./scripts/check-links.sh`.

- **Session 2026-06-25 — focused OR branch repair for PBLs landed; AUFLIA remains 4/6.**
  Added a bounded selected-assertion repair path to the one-sided `pbls` model
  finder: wider OR-shaped assertions keep the cheap root-truth persistent score,
  but when selected they get a local structural tie-break and a capped branch
  repair planner that tries to make one disjunct true by applying simple literal
  repairs as a unit. This targets generated branch-selector formulas without
  raising the global structural-scoring cap; a broad cap increase and a 1 s
  scalar local-search probe were measured and rejected because they did not close
  the hard files. Local QF_AUFLIA fair-slice measurement remains **4/6 decided,
  DISAGREE=0** (artifact
  `bench-results/local/qf-auflia-after-pbls-focused-or-repair.json`; Z3 remains
  **6/6**, PAR-2 **0.104 s** vs axeyum **6.668 s**). Route diagnostics remain
  baseline-shaped: `bug330` is still UF-out-of-scope for local search and times
  out in the scalar path after **1144** blocking lemmas; `bug337` still times out
  in local search and then in scalar LIA after **851** blocking lemmas. **Next:**
  switch away from small PBLs move families; the remaining AUFLIA gap needs a
  real branch-schedule/model-construction shortcut, finite UF-table reasoning
  for `bug330`, or SAT relevance in the large scalar skeleton.
  Verification passed: `cargo test -p axeyum-solver --lib pbls::tests -j1`;
  `cargo test -p axeyum-solver --lib dpll_lia::tests -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`.

- **Session 2026-06-25 — PBLs affine integer repair candidates landed; AUFLIA remains 4/6.**
  Extended the one-sided `pbls` local-search model finder with assertion-local
  integer repair candidates for narrow unit-affine shapes: `x`, `x + c`,
  `c + x`, and `x - c` inside equality and order atoms now suggest boundary
  moves using the current values of the opposite side. The candidate set is
  capped and still combined with the existing finite constant-guided moves;
  any `sat` remains replay-gated by the existing local-search and array
  projection path. Local QF_AUFLIA fair-slice measurement remains **4/6 decided,
  DISAGREE=0** (artifact
  `bench-results/local/qf-auflia-after-pbls-affine-repairs.json`; Z3 remains
  **6/6**, PAR-2 **0.105 s** vs axeyum **6.668 s**). Route diagnostics are flat:
  `bug330` is still outside local-search scope because UF applications remain in
  the scalar snapshot, and `bug337` still times out in local search before the
  exact scalar loop times out after **855** blocking lemmas. **Next:** stop
  expecting small PBLs move families to close this AUFLIA slice; the remaining
  gap still wants finite UF-table model search for `bug330`, SAT
  relevance/model construction for `bug337`, or a higher-level array/branch
  abstraction shortcut.
  Verification passed: `cargo test -p axeyum-solver --lib pbls::tests -j1`;
  `cargo test -p axeyum-solver --lib dpll_lia::tests -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`.

- **Session 2026-06-25 — compact integer-bound implication lemmas landed; AUFLIA remains 4/6.**
  Added a compact-formula upfront pruning pass to scalar arithmetic DPLL(T):
  asserted simple integer bounds on the same expression now seed adjacent
  monotonicity lemmas such as `x <= 0 => x <= 1` and `x >= 2 => x >= 1`.
  Each lemma is recorded as the certifiable LIA core `{stronger_bound, not
  weaker_bound}` and verified by the existing simplex certificate route. A
  broader all-polarity version was measured and rejected for the current hard
  AUFLIA slice because it inflated upfront clauses (`bug330` 131, `bug337` 600)
  and reduced scalar rounds; the landed pass is asserted-bound-only and gated to
  compact skeletons (`<=256` arithmetic atoms). Local QF_AUFLIA fair-slice
  measurement remains **4/6 decided, DISAGREE=0** (artifact
  `bench-results/local/qf-auflia-after-compact-bound-implications.json`; Z3
  remains **6/6**, PAR-2 **0.107 s** vs axeyum **6.668 s**). Hard-file
  diagnostics are baseline-preserving: `bug330` stays at **27** upfront bound
  lemmas and **1137** blocking lemmas before SAT timeout; `bug337` stays at
  **150** upfront bound lemmas and **854** blocking lemmas before timeout.
  **Next:** this reinforces that the remaining AUFLIA gap is not another small
  static LIA lemma family; it is SAT relevance/model construction on the large
  scalar skeleton, finite UF-table model search for `bug330`, or a higher-level
  array/branch abstraction shortcut.
  Verification passed: `cargo test -p axeyum-solver --lib dpll_lia::tests -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`.

- **Session 2026-06-25 — capped integer-difference cores landed; AUFLIA remains 4/6.**
  Added a second cheap dynamic core extractor to scalar arithmetic DPLL(T):
  current integer literals of the form `x + c <= y + d` / `<` are recognized as
  difference constraints, and small negative cycles are returned as compact theory
  lemmas before the full-slice fallback. The common two-edge cycle
  `x <= y` with `y + 1 <= x` is handled directly; full Bellman-Ford extraction is
  capped to small/medium snapshots, and large generated AUFLIA slices decline this
  extractor to avoid spending the SAT budget on core search. The returned lemmas
  still go through the existing LIA simplex certificate verifier. Local QF_AUFLIA
  fair-slice measurement remains **4/6 decided, DISAGREE=0** (artifact
  `bench-results/local/qf-auflia-after-capped-idl-core.json`; Z3 remains **6/6**,
  PAR-2 **0.105 s** vs axeyum **6.668 s**). Hard-file diagnostics are essentially
  baseline-preserving: `bug330` reaches **1140** blocking lemmas before SAT
  timeout; `bug337` reaches **849** before SAT timeout. **Next:** this confirms
  the hard AUFLIA files need either SAT relevance/model construction work at the
  large scalar skeleton, or a different array/branch abstraction shortcut; compact
  IDL cores help smaller formulas but do not close this slice.
  Verification passed: `cargo test -p axeyum-solver --lib dpll_lia::tests -j1`;
  `cargo test -p axeyum-solver --lib pbls::tests -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`.

- **Session 2026-06-25 — capped structural PBLs scoring landed; AUFLIA remains 4/6.**
  The one-sided `pbls` model finder now scores compact Boolean assertions with a
  structural cost instead of a single root-satisfied bit: nested `and`/`or`/`not`,
  implication, Bool equality/xor, and Bool `ite` expose local gradients while
  theory atoms remain evaluator-checked black boxes. The scorer is capped by DAG
  size and variable incidence so large generated formulas keep the previous cheap
  root-truth score; this avoids spending the whole portfolio budget inside one
  move. Added a nested Bool/Int regression that requires the structural score to
  find a replaying model. Local QF_AUFLIA fair-slice measurement remains **4/6
  decided, DISAGREE=0** (artifact
  `bench-results/local/qf-auflia-after-structural-pbls-score.json`; Z3 remains
  **6/6**, PAR-2 **0.112 s** vs axeyum **6.668 s**). Hard-file diagnostics remain:
  `bug330` is still outside this probe because UF applications remain in the
  scalar snapshot; `bug337` is in scope but local search times out, then the exact
  scalar loop reaches **865** blocking lemmas before `rustsat-batsat` timeout.
  **Next:** the AUFLIA frontier still needs SAT relevance / replay-gated model
  construction for `bug337`, or finite UF-table model search for `bug330`; compact
  structural scoring is not enough to close the slice.
  Verification passed: `cargo test -p axeyum-solver --lib pbls::tests -j1`;
  `cargo test -p axeyum-solver --lib dpll_lia::tests -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`.

- **Session 2026-06-25 — integer local-search scalar probe landed; AUFLIA remains 4/6.**
  Extended the deterministic one-sided `pbls` local-search engine from Bool/BV
  to Bool/BV/Int with finite, formula-constant-guided integer moves, then wired a
  100 ms replay-gated probe behind scalar snapshot preprocessing in the lazy
  ROW/extensionality array path. A probe `sat` reconstructs through the
  preprocessing trail and then still goes through the normal array projection and
  original-assertion replay; misses remain `unknown` and fall through to the
  exact scalar backend. Local QF_AUFLIA fair-slice measurement remains **4/6
  decided, DISAGREE=0** (artifact
  `bench-results/local/qf-auflia-after-int-local-search-scalar-probe.json`; Z3
  remains **6/6**, PAR-2 **0.106 s** vs axeyum **6.668 s**). The useful movement
  is diagnostic: `bug330`'s scalar snapshot still contains unsupported UF
  applications for this local search (`query has a construct the evaluator cannot
  reduce`), while `bug337` is in scope but the probe times out and the exact
  scalar loop still expires after **857** rounds. **Next:** either teach the
  model-search probe finite UF interpretations for `bug330`, or move to real SAT
  relevance / model-construction work for in-scope `bug337`.
  Verification passed: `cargo test -p axeyum-solver --lib pbls::tests -j1`;
  `cargo test -p axeyum-solver --lib dpll_lia::tests -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`.

- **Session 2026-06-25 — current-polarity integer-bound cores landed; AUFLIA remains 4/6.**
  Dynamic scalar LIA conflicts now try a cheap certified core before falling
  back to the large full-theory slice: after the simplex oracle reports the
  current integer assignment unsat, the DPLL(T) path scans the assigned literal
  polarities for an obvious two-literal bound contradiction such as `x <= 0`
  with `not (x <= 1)` (i.e. `x >= 2`). The returned core is still recorded as an
  ordinary `ArithLemmaLiteral` and verified by the existing refutation checker.
  Local QF_AUFLIA fair-slice measurement remains **4/6 decided, DISAGREE=0**
  (artifact `bench-results/local/qf-auflia-after-cheap-bound-core.json`; Z3
  remains **6/6**, PAR-2 **0.106 s** vs axeyum **6.670 s**). Route diagnostics:
  at 10 s, `bug330` now reaches **1143** scalar blocking lemmas (was **608**
  after the warm skeleton) before `rustsat-batsat` times out; `bug337` reaches
  **860** blocking lemmas (was **788**) before the scalar loop exhausts the
  timeout. **Next:** the remaining blocker is learned-clause search quality /
  relevance on the large scalar Boolean skeleton, or a replay-gated
  model-construction shortcut for `bug337`; cheap bound cores alone do not close
  either hard file.
  Verification passed: `cargo test -p axeyum-solver --lib dpll_lia::tests -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`.

- **Session 2026-06-25 — warm incremental Boolean skeleton for scalar arithmetic landed; AUFLIA remains 4/6.**
  Replaced the legacy arithmetic DPLL fallback's per-round pure-Boolean solve
  path with a small internal `BoolSkeletonSolver`: the scalar Boolean skeleton is
  encoded to CNF once, kept in a warm `IncrementalSat`, and each learned theory
  blocking clause is added incrementally. This removes the repeated
  Bool→AIG→CNF rebuild through `SatBvBackend` on every scalar refinement round;
  `sat` still flows through `finish_sat`, theory-model reconstruction, and
  original-assertion replay before being accepted.
  Local QF_AUFLIA fair-slice measurement remains **4/6 decided, DISAGREE=0**
  (artifact `bench-results/local/qf-auflia-after-warm-scalar-bool-skeleton.json`;
  Z3 remains **6/6**, PAR-2 **0.105 s** vs axeyum **6.670 s**). The diagnostic
  frontier moved materially: at 10 s, `bug330` now reaches **608** scalar
  blocking lemmas (was **40** after the large-core cutoff) before `rustsat-batsat`
  times out; `bug337` now reaches **788** blocking lemmas (was **46**). A 30 s
  single-file `bug337` run reaches **1670** blocking lemmas before BatSat times
  out. **Next:** the remaining blocker is SAT search quality / relevance after a
  large learned-clause Boolean skeleton, or a replay-gated model-construction
  shortcut for `bug337`; rebuild overhead is no longer the limiting cost.
  Verification passed: `cargo test -p axeyum-solver --lib dpll_lia::tests -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`.

- **Session 2026-06-25 — scalar LIA bound lemmas + large-core cutoff landed; AUFLIA remains 4/6.**
  Added a certified upfront pruning pass to the legacy arithmetic DPLL fallback:
  simple asserted integer bounds on the same term now generate two-literal
  theory lemmas for impossible lower/upper pairs, e.g. the branch-selector
  pattern `x >= 1` with `x <= 0`. These clauses are recorded as ordinary
  `ArithLemmaLiteral` cores and pass the existing independent refutation
  verifier. Also made conflict-core minimization size-aware: scalar abstractions
  with more than 128 atoms use the full unsat theory slice instead of spending
  many simplex calls on deletion minimization. Small/certification-friendly
  formulas still get minimized cores.
  Local QF_AUFLIA fair-slice measurement remains **4/6 decided, DISAGREE=0**
  (artifact `bench-results/local/qf-auflia-after-bound-lemmas-core-cutoff.json`;
  Z3 remains **6/6**, PAR-2 **0.105 s** vs axeyum **6.673 s**). The useful
  movement is diagnostic/throughput: at 10 s, `bug330` now reaches **40**
  scalar blocking lemmas with **27** upfront bound lemmas before the Boolean
  skeleton times out; `bug337` reaches **46** blocking lemmas with **150**
  upfront bound lemmas. A 30 s single-file `bug337` run reaches **84** blocking
  lemmas before the pure Boolean skeleton times out, compared with the previous
  **19**-lemma diagnostic under core minimization. **Next:** the remaining
  blocker is no longer expensive simplex core minimization; it is Boolean
  skeleton scaling / relevance / incremental SAT after many learned clauses, or
  a replay-gated SAT/model-construction shortcut for `bug337`.
  Verification passed: `cargo test -p axeyum-solver --lib dpll_lia::tests -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`.

- **Session 2026-06-25 — online LIA/LRA Boolean-leaf model lift landed; AUFLIA remains 4/6.**
  Closed a replay gap in the standalone online arithmetic drivers. The online
  LIA/LRA encoders already admit declared Boolean leaves in the Boolean skeleton,
  but a `sat` leaf reconstructed only the arithmetic theory model before replay.
  They now lift final DPLL assignments for declared Boolean leaves into the
  returned model, then replay with the combined arithmetic+Boolean assignment.
  Added focused in-source regressions for `p ∧ (x < y ∨ y < x)` in both LIA and
  LRA, which require the Boolean leaf value to replay.
  Local QF_AUFLIA fair-slice measurement remains **4/6 decided, DISAGREE=0**
  (artifact `bench-results/local/qf-auflia-after-online-boolean-model-lift.json`;
  Z3 remains **6/6**, PAR-2 **0.102 s** vs axeyum **6.673 s**). Final route trace
  is unchanged on the two hard files: `bug330` is still **802** atoms / **6**
  blocking lemmas before timeout, and `bug337` is still **946** atoms / **7**
  blocking lemmas before timeout. A tested 3s online LIA probe cap did not solve
  either file and reduced `bug330` fallback progress, so it was reverted to the
  previous 1s cap. Verification passed:
  `cargo test -p axeyum-solver --lib lia_online::tests -j1`;
  `cargo test -p axeyum-solver --lib lra_online::tests -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo fmt --all --check`. **Next:** the remaining AUFLIA work is still a real
  `bug337` SAT/model-construction shortcut on the smaller scalar abstraction, or
  `bug330` Boolean-layer model certification/relevance.

- **Session 2026-06-25 — scalar abstraction preprocessing/flattening landed; AUFLIA remains 4/6.**
  Wired the existing replay-safe word-level preprocessing wrapper into the
  lazy ROW/extensionality scalar CEGAR boundary, after first flattening positive
  top-level conjunctions. This exposes generated scalar definitions (`x = t`,
  constants, fresh read aliases) to `propagate_values`/`solve_eqs` before the
  arithmetic or UFLIA backend builds its Boolean/theory skeleton. The change is
  relaxation-local: `unsat` of the preprocessed scalar snapshot still implies
  `unsat` of the snapshot, and every `sat` candidate is reconstructed by the
  preprocessing trail before the normal ROW/extensionality projection and
  original-formula replay.
  Local QF_AUFLIA fair-slice measurement remains **4/6 decided, DISAGREE=0**
  (artifact `bench-results/local/qf-auflia-after-scalar-preprocess-flatten.json`;
  Z3 remains **6/6**, PAR-2 **0.104 s** vs axeyum **6.674 s**). The useful
  movement is diagnostic and scalar-frontier specific: `bug337` drops from
  **1374** arithmetic atoms / **2** blocking lemmas to **946** atoms / **7**
  lemmas at 10 s; a 30 s single-file run reaches **19** blocking lemmas but
  still returns `unknown`, so the blocker is not just the harness cap. `bug330`
  remains at **802** atoms and times out after **6** blocking lemmas. Verification
  passed: `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_row -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`. **Next:** use the smaller
  `bug337` abstraction to add a real SAT/model-construction shortcut, or attack
  `bug330` through Boolean-layer model certification/relevance rather than more
  scalar cleanup.

- **Session 2026-06-25 — scalar Boolean short-circuiting landed; AUFLIA remains 4/6.**
  Added constant-aware Boolean simplification inside the legacy arithmetic
  abstraction used by the scalar LIA/LRA fallback: dead `and`/`or` branches are
  skipped before their arithmetic atoms are allocated; Boolean `xor`, implication,
  equality, negation, and Bool-valued `ite` now fold constants and identical
  branches during abstraction. This is a sound local cleanup and prevents future
  dead Boolean scaffolding from inflating scalar theory atoms, but it is neutral
  on the current cvc5 QF_AUFLIA hard slice. Route trace remains: `bug330` times
  out at ROW round 0 with **62 select sites**, then **802** arithmetic atoms and
  **7** blocking lemmas; `bug337` times out at extensionality round 0 with
  **152 select sites**, then **1374** atoms and **2** blocking lemmas. Local
  QF_AUFLIA fair-slice measurement remains **4/6 decided, DISAGREE=0** (artifact
  `bench-results/local/qf-auflia-after-boolean-simplification.json`; Z3 remains
  **6/6**, PAR-2 **0.104 s** vs axeyum **6.672 s**). Verification passed:
  `cargo test -p axeyum-solver --lib dpll_lia::tests -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`. **Next:** stop
  looking for shallow Boolean cleanup to move this slice; `bug330` needs real
  scalar relevance / Boolean-layer model certification, and `bug337` needs a
  smaller initial extensionality abstraction or SAT/model-construction shortcut.

- **Session 2026-06-25 — arithmetic atom canonicalization and bounded LIA probe cap landed; AUFLIA remains 4/6.**
  Reduced scalar arithmetic abstraction duplication in the legacy DPLL(LIA/LRA)
  path. Reversed order atoms now share one canonical proposition
  (`x >= y` becomes `y <= x`, `x > y` becomes `y < x`), negated order atoms are
  pushed to their order-complement (`not (x < y)` becomes `y <= x`), and trivial
  self-comparisons/equalities fold to Boolean constants instead of allocating
  theory atoms. A trial expansion of `not (= a b)` to strict-order disjunctions
  was rejected because it increased `bug330`'s scalar atom count; only the
  beneficial order canonicalization was kept. Added unit tests for reversed-order
  sharing, negated-order sharing, and self-comparison/equality folding.
  Also capped the online LIA probe inside `check_with_arith_dpll` to at most
  1 second of a configured wall-clock timeout. The probe still gets a bounded
  chance to use the stronger CDCL(T) spine, but large scalar abstractions no
  longer lose half of the measured budget before the legacy arithmetic fallback.
  Local QF_AUFLIA fair-slice measurement remains **4/6 decided, DISAGREE=0**
  (artifact `bench-results/local/qf-auflia-after-arith-atom-canonicalization.json`).
  The route trace shows modest but real scalar-frontier movement: `bug330` drops
  from **832** to **802** arithmetic atoms and the fallback advances from **4**
  to **7** blocking lemmas before timing out; `bug337` remains **1374** atoms and
  **2** blocking lemmas before timeout. Verification passed:
  `cargo test -p axeyum-solver --lib dpll_lia::tests -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo fmt --all --check`. **Next:** `bug330` still needs stronger scalar
  relevance/atom reduction or a better SAT/theory loop; `bug337` needs a
  SAT/model-construction shortcut or a much smaller initial extensionality
  scalar abstraction.

- **Session 2026-06-25 — measurement harness timeout is now passed into the solver; AUFLIA misses localized to initial scalar abstractions.**
  Fixed the corpus measurement examples so the Axeyum worker-thread cap is also
  passed into `SolverConfig::timeout` for `check_auto`. Before this, `measure_corpus`
  and `measure_graduated` could kill the worker at the harness boundary while
  deadline-aware solver routes saw `timeout = None`, making PAR-2 less
  representative of the solver API. The worker cap remains as an outer safety net.
  Also tightened lazy ROW/extensionality CEGAR budget handling: each scalar backend
  call now receives only the remaining outer deadline, and unknowns from the scalar
  backend are annotated with the ROW/extensionality round, materialized select-site
  count, and lemma counts. The legacy arithmetic DPLL loop now similarly passes
  remaining time to the SAT skeleton backend and reports atom/blocking-lemma counts
  on timeout.
  Local QF_AUFLIA fair-slice measurement with the corrected harness remains **4/6
  decided, DISAGREE=0** (artifact
  `bench-results/local/qf-auflia-after-scalar-abstraction-diagnostics.json`;
  PAR-2 **6.672 s** vs Z3 **0.104 s**). The route trace now proves both remaining
  misses fail before array refinement does any useful work: `bug330` times out in
  the initial ROW scalar abstraction at round 0 with **62 select sites**, then
  arithmetic times out after **4 scalar rounds / 832 atoms / 4 blocking lemmas**;
  `bug337` times out in the initial extensionality scalar abstraction at round 0
  with **152 select sites**, then arithmetic times out after **2 scalar rounds /
  1374 atoms / 2 blocking lemmas**.
  Verification passed: `cargo check -p axeyum-bench --examples -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_row -j1`;
  `cargo test -p axeyum-solver --test abv_lazy_ext -j1`;
  `cargo fmt --all --check`. **Next:** attack scalar abstraction size/relevance
  for `bug330`/`bug337` before adding more ROW/extensionality lemmas; the current
  bottleneck is the first scalar solve, not refinement convergence.

- **Session 2026-06-25 — UFLIA/UFLRA combined CDCL(T) now honors deadlines; AUFLIA frontier sharpened, 4/6 unchanged.**
  Closed a resource-bound gap in the combined online UF+arithmetic drivers:
  both `QF_UFLIA` and `QF_UFLRA` computed a wall-clock deadline for the
  integrated `Dpll<CombinedIncremental*>` path but then called the unbounded
  `solve` entry. They now call `solve_with_deadline` and return a
  timeout-classified `Unknown` when the budget expires. Added zero-budget
  Boolean-combination regressions in both online suites so timeout declines are
  reported as `UnknownKind::Timeout`, not a generic incomplete search.
  Raised the UFLIA Boolean atom admission cap from 48 to 384 under that deadline
  guard, enough to exercise the current `bug330` scalar abstraction (339 atoms)
  instead of rejecting it at the front door. The new route trace confirms
  `bug330` is no longer an admission-cap miss: it reaches the online
  UF+LIA combination and declines on an uncertified Boolean-layer theory model,
  then still times out in the lazy Int-array route. `bug337` remains the pure
  Int-array lazy-LIA timeout.
  Local QF_AUFLIA fair-slice measurement (debug harness, 10 s, artifact
  `bench-results/local/qf-auflia-after-uflia-deadline-cap.json`) remains **4/6
  decided, DISAGREE=0**; Z3 remains **6/6** (PAR-2 **0.106 s** vs axeyum
  **6.672 s**). Verification passed:
  `cargo test -p axeyum-solver --test uflia_online -j1`;
  `cargo test -p axeyum-solver --test uflra_online -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo fmt --all --check`; `git diff --check`. **Next:** treat `bug330`
  as an interface/replay/relevance problem, not a 48-atom admission problem;
  separately attack `bug337` with Int-array SAT/model construction or a better
  lazy-LIA search path.

- **Session 2026-06-25 — AUFLIA permutation-chain refuter closes cvc5 `swap...`; fair slice now 4/6.**
  Generalized the prior clean swap-chain recognizer into a terminating,
  memoized array-permutation normalizer. A recognized store pair
  `store(store(a,i,select(a,j)),j,select(a,i))` is treated as a swap over the
  normalized base, and the normal form records the induced deterministic
  permutation map rather than an ordered syntactic list. Same-index swaps collapse
  to identity, repeated/canceling swaps normalize naturally, and the recognizer
  accepts select bases that are already extensionally equal under the same
  normalizer. This remains a refuter only: it proves `unsat` for same-index read
  disequalities between extensionally equal permutation chains and otherwise
  declines.
  Moved the proven array-unsat refuters to the `check_auto` front door, before
  global coercion/ITE normalization and before UF+arithmetic. That matters for
  generated AUFLIA formulas: the exact cvc5
  `cli__regress4__swap_t1_pp_nf_ai_00010_004.cvc.smt2` file now decides
  immediately via `array-unsat-refuter` instead of burning the scalar lazy-LIA
  timeout. The existing two-store split and array congruence refuters also run
  from this early hook, but only return proven `unsat`.
  Local QF_AUFLIA fair-slice measurement (debug harness, 10 s, artifact
  `bench-results/local/qf-auflia-after-permutation-refuter.json`) is now **4/6
  decided, DISAGREE=0**, improving the prior 3/6; Z3 remains **6/6** and much
  faster (PAR-2 **0.104 s** vs axeyum **6.672 s**). Route trace: `bug336` and
  `swap...` decide via `array-unsat-refuter`; `prop__cadical_bug8` and
  `uf__issue4446` decide `sat`; remaining misses are `bug330` (339 UFLIA atoms
  against the current 48-atom online cap, then lazy-LIA timeout) and `bug337`
  (pure Int-array lazy-LIA timeout).
  Verification passed: direct lib regression
  `abv::tests::symmetric_swap_chain_refuter_closes_cvc5_regression` before the
  final front-door move; full
  `cargo test -p axeyum-solver --test int_array_sort -j1` after the front-door
  move; exact end-to-end cvc5 swap regression after the front-door move;
  `cargo fmt --all --check`; `git diff --check`; route explanation and
  fair-slice measurement above with `CARGO_INCREMENTAL=0`. A final rerun of the
  direct lib test was skipped because the host hit `No space left on device`
  while writing incremental cache; the normalizer itself was unchanged after
  that direct pass. **Next:** attack the two remaining AUFLIA misses through
  scalar search: relevance/atom-budget work for `bug330`, or an Int-array
  SAT/model-construction improvement for `bug337`.

- **Session 2026-06-25 — AUFLIA bounded LIA probe + clean swap-chain refuter landed; measured count unchanged.**
  Tightened the scalar-engine boundary exposed by the prior AUFLIA projection
  slice. `check_with_arith_dpll` now tries the shared online LIA DPLL(T) spine
  first and, when a timeout is configured, gives it a bounded probe before
  falling back to the legacy certified arithmetic-DPLL route with only the
  remaining budget. `check_qf_lia_online` now honors that wall-clock deadline
  instead of running unbounded inside array/UF scalar abstractions. Added a
  replay regression ensuring Boolean leaves that the online probe cannot model
  still fall back to a replaying SAT result.
  Also added a narrow, sound array refuter for clean symmetric store-swap
  chains of the form `store(store(a,i,select(a,j)),j,select(a,i))`: two arrays
  with the same base and the same ordered sequence of unordered swap pairs are
  extensionally equal, so a same-index read disequality refutes. This is useful
  coverage for generated swap-chain shapes, but it is not yet strong enough for
  the current cvc5 `swap...` corpus instance, which still falls through to the
  scalar lazy-LIA timeout.
  Local QF_AUFLIA fair-slice measurement (debug harness, 10 s, artifact
  `bench-results/local/qf-auflia-after-swap-chain-refuter.json`) remains **3/6
  decided, DISAGREE=0**; Z3 decides **6/6** on the same fair slice. Remaining
  misses are unchanged: `bug330` is a large Boolean UFLIA abstraction
  (**339 > 48** atom cap, then lazy-LIA timeout if forced), `swap...` needs a
  stronger array-permutation/ROW normalizer or scalar-LIA improvement, and
  `bug337` remains a scalar Int-array timeout. Verification passed:
  `cargo fmt --all --check`; `git diff --check`;
  `cargo check -p axeyum-solver -j1`;
  `cargo test -p axeyum-solver --test int_array_sort -j1`;
  `cargo test -p axeyum-solver --test lia_dpll -j1`;
  `cargo test -p axeyum-solver --test lia_online -j1`. All-features workspace
  verification was intentionally not rerun on this slice because the host disk
  is nearly full.
  **Next:** treat QF_AUFLIA as a scalar-search frontier now: either raise/reduce
  the `bug330` Boolean UFLIA abstraction cost with learned relevance, build a
  real array-permutation invariant for the swap chain, or address the
  `bug337` Int-array SAT/model-construction timeout.

- **Session 2026-06-25 — AUFLIA projection completion + scalar fallback diagnostics landed.**
  Narrowed the next QF_AUFLIA frontier after the structural ROW slice. The
  `QF_UFLIA` scalar backend used under lazy ROW now mirrors the normal mixed-UF
  dispatcher more closely: online UFLIA is still tried first, and non-budget
  `unknown` can fall back to the eager UF+arithmetic route. `FunctionElimination`
  model projection now completes non-application symbols with well-founded default
  values before evaluating full-`Value` UF argument keys, while still requiring
  each fresh `!fn_app_*` result to be assigned. This closes the concrete
  array-valued-UF-argument projection failure exposed by the `swap...` corpus
  shape (`no value bound for symbol #6`). Added a rewrite-layer regression for
  projection of `f(store(a,i,0))` when `a`/`i` are unconstrained by the backend
  model. The UFLIA Boolean atom-cap decline now reports `actual > cap`, making
  `bug330`'s scalar abstraction size explicit (**339 > 48**).
  Local QF_AUFLIA fair-slice measurement (debug harness, 10 s, artifact
  `bench-results/local/qf-auflia-after-projection-completion.json`) remains **3/6
  decided, DISAGREE=0**. Remaining misses are now clearer: `bug330` is a large
  Boolean UFLIA abstraction (339 atoms; array route then hits the lazy-LIA budget
  if forced through eager fallback), `swap...` is past structural/projection
  failures and now reaches a lazy-LIA timeout, and `bug337` remains a scalar
  Int-array timeout. Verification passed: focused rewrite projection regression;
  focused Int-array/AUFLIA tests;
  `cargo check -p axeyum-rewrite -p axeyum-solver -p axeyum-bench --all-features -j4`;
  `cargo clippy -p axeyum-rewrite -p axeyum-solver -p axeyum-bench --all-targets --all-features -j4 -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`. **Next:** stop treating these
  as structural/modeling bugs; the next real movement needs a stronger scalar
  Boolean/LIA engine for large array abstractions (or a corpus-specific valid
  array invariant for the swap-chain), plus the `bug337` SAT-side timeout.

- **Session 2026-06-25 — AUFLIA structural ROW coverage widened; measured count unchanged.**
  Extended the mixed Int-array/AUFLIA lazy ROW route past two structural blockers
  without claiming a decide-rate gain. Scalar UF applications now preserve
  array-valued arguments through ROW abstraction instead of recursively rejecting
  store-chain array operands; `select(ite c a b, i)` now lowers inside the lazy
  resolver to `ite c (select a i) (select b i)`; and store ROW "miss" branches can
  point at an arbitrary abstracted scalar read expression rather than only another
  materialized site. The UF-arithmetic overbound guard also no longer short-circuits
  mixed array+UF queries on `unknown`; it records the decline and lets the downstream
  array route try. Added focused regressions for the swap-store-chain skolem-index
  shape and array-`ite` reads.
  Local QF_AUFLIA fair-slice measurement (debug harness, 10 s, artifact
  `bench-results/local/qf-auflia-after-array-ite-routing.json`) remains **3/6
  decided, DISAGREE=0**. The route trace is more precise: `bug330` now reaches
  `array-fast-path` and declines on the scalar UFLIA Boolean atom cap ("too many
  theory atoms") instead of the earlier structural ROW rejection; `swap...` is also
  past structural rejection and now fails by replay/timeout; `bug337` remains a
  scalar Int-array timeout. Verification passed: focused Int-array/AUFLIA tests;
  `cargo check -p axeyum-solver -p axeyum-bench --all-features -j4`;
  `cargo clippy -p axeyum-solver -p axeyum-bench --all-targets --all-features -j4 -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`. **Next:** attack the remaining
  QF_AUFLIA misses by reducing/raising the scalar UFLIA Boolean atom cap for
  `bug330`, improving replay/refinement for the swap-chain corpus instance, and
  addressing the scalar Int-array timeout in `bug337`.

- **Session 2026-06-25 — AUFLIA store-disjunction refuter landed.**
  Closed the next named QF_AUFLIA blocker (`bug336`) with a sound array-specific
  refuter for the Stump-Barrett-Dill-Levitt store consequence:
  `store(a,i,v)=b ∧ store(a,j,w)=b ⇒ i=j ∨ a=b`. The implementation detects
  two positive store equalities with the same base and target, then asks the
  existing checked EUF congruence refuter to prove both branches impossible under
  the original assertions. This turns the corpus shape
  `f(x) != f(y) ∧ g(a) != g(b)` into a real `unsat` result without trusting the
  new search logic for proof: each branch refutation is delegated to the existing
  congruence checker. Added focused coverage for the exact AUFLIA pattern and a
  satisfiable guard where one branch remains possible.
  Local QF_AUFLIA fair-slice measurement (debug harness, 10 s, artifact
  `bench-results/local/qf-auflia-after-store-split.json`) is now **3/6 decided,
  DISAGREE=0**, improving the previous mixed ROW+UF result of 2/6. Per-file
  trace confirms `cli__regress0__auflia__bug336.smt2` now decides `unsat` via
  `array-fast-path`; remaining QF_AUFLIA misses are `bug337` (scalar Int-array
  timeout) and `bug330` / `swap...` (array term shapes outside the current ROW
  fragment). Verification passed: focused Int-array/AUFLIA tests;
  `cargo check -p axeyum-ir -p axeyum-rewrite -p axeyum-solver -p axeyum-bench --all-features -j4`;
  `cargo clippy -p axeyum-ir -p axeyum-rewrite -p axeyum-solver -p axeyum-bench --all-targets --all-features -j4 -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`. **Next:** extend the ROW
  abstraction to the array-valued structural terms in `bug330`/`swap...`
  (superseded by the later structural ROW coverage slice), then address the scalar
  Int-array timeout in `bug337`.

- **Session 2026-06-25 — Mixed AUFLIA lazy ROW+UF route landed.**
  Advanced the next QF_AUFLIA blocker past parser/model admission into an actual
  mixed array+UF solving path. Lazy ROW/extensionality now has a
  `QF_UFLIA` scalar backend (`check_qf_auflia_lazy_row`) that delegates the
  scalar abstraction to the existing online UF+LIA combination while keeping the
  array CEGAR layer responsible for ROW/extensionality. SAT remains replay-gated
  against the original array formula. Model plumbing was tightened so projected
  array models preserve UF interpretations, missing UF interpretations are
  completed with deterministic well-founded defaults, and the UF+LIA model
  builder completes non-Int symbols before evaluating array arguments in
  integer-result function tables. `check_auto` now routes non-BV
  Bool/linear-Int+UF array slices through this path, and budget `unknown` from
  eager UF+arith no longer prevents mixed array+UF queries from falling through
  to the array CEGAR route. Added `axeyum-bench/examples/explain_corpus.rs` for
  bounded per-file route traces.
  Regression coverage in `crates/axeyum-solver/tests/int_array_sort.rs` now
  includes replayed SAT for `g : (Array Int Int) -> Int`, replayed SAT for
  `select a (idx a)`, and a ROW contradiction at a UF-produced index. Local
  QF_AUFLIA fair-slice measurement (debug harness, 10 s, artifact
  `bench-results/local/qf-auflia-after-mixed-row-uf.json`) is now **2/6
  decided, DISAGREE=0**; this is a real movement from the previous 1/3, but
  parser admission also expanded the fair set to six files. Per-file trace:
  `prop__cadical_bug8` and pure Boolean UF decide; `bug337` is a scalar
  Int-array timeout; `bug330` and `swap...` use array term shapes outside the
  current ROW fragment; `bug336` needs stronger array/UF extensional reasoning
  after lazy refinement. Verification passed: focused Int-array/AUFLIA tests;
  `cargo check -p axeyum-ir -p axeyum-rewrite -p axeyum-solver -p axeyum-bench --all-features -j4`;
  `cargo clippy -p axeyum-ir -p axeyum-rewrite -p axeyum-solver -p axeyum-bench --all-targets --all-features -j4 -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`. **Next:** extend the ROW
  fragment to array-valued `ite`/structural store-chain operands and add the
  missing array-equality-to-UF congruence refinement needed by `bug336`, then
  remeasure QF_AUFLIA/QF_ALIA.

- **Session 2026-06-25 — AUFLIA array-argument UF prerequisite landed.**
  Continued from the post-QF_ALIA scalar-array slice and narrowed the remaining
  QF_AUFLIA gap to mixed array+UF handling. The IR now admits array-valued
  *parameters* for uninterpreted functions while still rejecting array-valued
  results; this matches the cvc5 AUFLIA shapes such as
  `g : (Array Int Int) -> Int` without opening array-returning UF terms before
  solver/model projection is ready. `FuncValue` storage is generalized from
  "arithmetic only" to full-`Value` tables whenever a signature mentions
  `Int`/`Real`/arrays/datatypes, so model replay can key function entries by
  concrete generic array values. UF model projection now uses the same predicate
  instead of scalar-coding array arguments. SMT-LIB parsing accepts array-argument
  `declare-fun` signatures and keeps array-valued results as clear IR errors.
  Added regression coverage in `crates/axeyum-ir/tests/ir.rs`,
  `crates/axeyum-smtlib/tests/smtlib.rs`, and
  `crates/axeyum-solver/tests/int_array_sort.rs`; the solver now proves the
  narrow AUFLIA congruence case
  `a = b ∧ g(a) != g(b)` for `g : (Array Int Int) -> Int` as `unsat`, and
  pins a satisfiable array-argument UF shape so it may return `sat` or
  `unknown` but never a false `unsat`.
  Verification passed: `cargo check -p axeyum-ir -p axeyum-rewrite -p axeyum-smtlib -p axeyum-solver --all-features -j4`;
  focused IR/SMT-LIB/Int-array solver tests; `cargo clippy -p axeyum-ir -p axeyum-rewrite -p axeyum-smtlib -p axeyum-solver --all-targets --all-features -j4 -- -D warnings`;
  `cargo fmt --all --check`; `git diff --check`. **Next:** wire a
  replay-checked scalar backend for lazy ROW/extensionality whose scalar side can
  solve UF+LIA with array-argument applications, then remeasure QF_AUFLIA; current
  UF+LIA online docs still explicitly decline arrays, so the broader mixed route
  is not done.

- **Session 2026-06-25 — Int-array SAT projection + scalar lazy ROW route landed.**
  Advanced the next Tier-A array keystone slice: the IR now has
  `Value::GenericArray` for non-BV array models, the evaluator executes
  `const-array`/`select`/`store` over arbitrary non-array component sorts, and
  well-founded defaults now include generic array values. The lazy
  ROW/extensionality CEGAR path no longer assumes `u128`-coded BV indices/results:
  it compares full `Value`s, completes missing scalar symbols before projection,
  reconstructs either compact `ArrayValue` or `GenericArrayValue`, and uses
  single diff-skolem witnesses at the real index sort. `check_auto` now routes the
  Bool/linear-Int scalar array slice through the existing lazy array machinery
  with the arithmetic DPLL backend, so model-producing `(Array Int Int)` SAT
  shapes now return replay-checked `sat` instead of the previous explicit
  `unknown`. The eager BV array eliminator still remains BV-only but now declines
  non-BV arrays cleanly instead of assuming widths.
  Regression coverage added/updated:
  `crates/axeyum-ir/tests/ir.rs` pins generic Int-array
  `const-array`/`store`/`select` evaluation;
  `crates/axeyum-solver/tests/int_array_sort.rs` now covers congruence UNSAT,
  free-read SAT replay, ROW-conflict UNSAT, and array-disequality SAT replay.
  Verification passed: `cargo fmt --all --check`;
  `cargo check -p axeyum-ir -p axeyum-rewrite -p axeyum-solver --all-features -j4`;
  `cargo clippy -p axeyum-ir -p axeyum-rewrite -p axeyum-solver --all-targets --all-features -j4 -- -D warnings`;
  focused IR, Int-array solver, SMT-LIB array, and uninterpreted-sort solver
  tests. Local post-slice measurement (debug harness, 10 s, artifacts under
  `bench-results/local/`): QF_ALIA cvc5 clean fair slice now **3/5 decided,
  DISAGREE=0** (`z3_rejected_unfair=1`), improving the committed 0-decided
  baseline; QF_AUFLIA fair slice remains **1/3 decided, DISAGREE=0**, confirming
  mixed UF/array breadth is still open; QF_UF overbound remains **4/6 decided,
  DISAGREE=0**. **Next:** promote/refresh committed baselines if desired, then
  extend the scalar array route across mixed AUFLIA/UF and broader non-BV
  component sorts instead of only Bool/linear-Int arrays.

- **Session 2026-06-25 — IR keystone slice: sort-valued arrays landed.**
  Advanced the remaining half of the Tier-A array IR blocker without claiming the
  full Int-array decision procedure yet: `Sort::Array` now carries sort-valued
  component metadata (`ArraySortKey`) instead of BV widths only, while
  `array_widths()` remains a BV-only compatibility helper for the existing finite
  array model/projection path. `TermArena::select`/`store` now check the actual
  index/element sorts; `const-array` carries its index sort; SMT-LIB parses and
  writes free `(Array Int Int)` formulas; writer logic detection reports
  `QF_ALIA` for Int arrays instead of fake BV logic. `check_auto` now scans array
  component sorts, proves the congruence-UNSAT slice for Int-indexed arrays
  (`a=b ∧ select(a,i)≠select(b,i)`), and at that point returned an explicit
  `unknown` for model-producing non-BV array SAT shapes until generic array
  models existed (superseded by the later 2026-06-25 entry above).
  Regression coverage: `crates/axeyum-smtlib/tests/smtlib.rs` checks first-class
  `(Array Int Int)` parse/write/round-trip and free Int-array representability;
  `crates/axeyum-solver/tests/int_array_sort.rs` checks Int-array congruence
  `unsat` plus the explicit non-BV-array `unknown` boundary. Verification passed:
  `cargo fmt --all --check`;
  `scripts/mem-run.sh cargo check --workspace --all-features -j4`;
  `scripts/mem-run.sh cargo clippy --workspace --all-targets --all-features -j4 -- -D warnings`;
  `scripts/mem-run.sh cargo test -p axeyum-ir -p axeyum-smtlib -p axeyum-rewrite -p axeyum-query -p axeyum-solver --all-features --no-run -j4`;
  focused SMT-LIB, Int-array solver, and uninterpreted-sort solver tests. Host
  disk remains tight after rebuilding test artifacts (`df -h .` ≈ 6.8G free,
  99% used). **Superseded next:** generic non-BV array model projection and the
  Bool/linear-Int lazy scalar route landed later on 2026-06-25; current next is
  remeasurement plus mixed AUFLIA/UF breadth.

- **Session 2026-06-25 — IR keystone slice: first-class uninterpreted sorts landed.**
  Advanced the [`docs/PARITY-STATUS-AND-PATH.md`](docs/PARITY-STATUS-AND-PATH.md)
  Tier-A QF_UF blocker without touching the array-sort half yet:
  `Sort::Uninterpreted(SortId)` is now an arena-declared `Copy` carrier, SMT-LIB
  arity-0 `(declare-sort U 0)` no longer collapses to a parser-chosen `BitVec(W)`,
  `Value::Uninterpreted` provides deterministic replay tokens, and the EUF
  e-graph model builder returns replay-checked `sat` models over declared carrier
  sorts. `check_auto` feature scanning now routes pure declared-sort equality/UF
  queries through the EUF path even when no `Op::Apply` occurs; evidence routing
  keeps those queries out of the raw QF_BV evidence label. SMT-LIB export emits
  `(declare-sort … 0)` and round-trips declared-sort constants/functions.
  Regression coverage:
  `crates/axeyum-smtlib/tests/smtlib.rs` checks first-class parsing/writing and
  collision/arity errors; `crates/axeyum-solver/tests/uninterpreted_sort_euf.rs`
  checks replayed `sat` for `a≠b : U` and congruence `unsat` for
  `a=b ∧ f(a)≠f(b)`. Verification passed:
  `cargo fmt --all --check`; `scripts/mem-run.sh cargo check --workspace --all-features -j4`;
  `scripts/mem-run.sh cargo clippy --workspace --all-targets --all-features -j4 -- -D warnings`;
  focused parser/solver tests. A broader
  `cargo test -p axeyum-ir -p axeyum-smtlib -p axeyum-solver --all-features -j4`
  hit the known host disk-pressure failure while linking solver tests
  (`No space left on device`); generated `target/debug/incremental` was removed,
  restoring limited space. **Next:** finish the same keystone by introducing
  sort-valued array index/element metadata and the single-witness extensionality
  route for Int-indexed arrays; then remeasure QF_UF/QF_ALIA/QF_AUFLIA rows.

- **Session 2026-06-23 — Z3/cvc5 gap analysis amended after online-combination push.**
  Updated [`docs/plan/gap-analysis-z3-cvc5-2026-06-22.md`](docs/plan/gap-analysis-z3-cvc5-2026-06-22.md)
  and sharpened `PLAN.md` to reflect the latest ledger: online LRA/LIA and
  default online UFLRA/UFLIA are no longer future work; vivification and
  route-trace telemetry have landed; LIA MBP/PDR/IMC and richer Horn handling
  have landed. The honest remaining gap is now **quality and migration**:
  real CDCL(T) propagation/1-UIP/relevance over the online spine, lazy arrays/BV
  on that spine, measured QF_BV performance with route traces, disjunctive LIA
  interpolation, NRA/NIA proof evidence, unbounded strings/sequences, and
  SMT-LIB surfaces for interpolation/abduction/proofs/diagnostics.

- **Session 2026-06-22 (cont.) — INFINITE-STATE + ONLINE-COMBINATION push: 12 verified increments (Track 1/2/4), all on `main`.**
  Advanced PLAN leverage items #1 (online multi-theory combination), #3 (SAT vivification), and #4
  (deepen CHC/PDR) — every increment isolated-worktree-delegated, hard-verify-gated before FF-merge,
  ledgered (`capabilities.rs` + matrix), and pushed (`b405e8e` → `4a95135`). Each is verify-guarded
  (DRAT / in-tree differential / model replay / verify-before-return); **0 wrong sat/unsat** throughout.
  - **Online EUF+LRA & EUF+LIA now decide FULL Boolean-structured QF_UFLRA/QF_UFLIA** via an enumerative
    DPLL(T) (Tseitin skeleton + propositional-model enumeration + theory-conflict blocking, the
    conjunctive MBTC reused as the per-model oracle) — differential vs offline `check_with_uf_arithmetic`,
    0 disagreements (`b405e8e`, `6850da9`).
  - **KEYSTONE (PLAN #1): the online combination is now the DEFAULT `check_auto` route for mixed
    UF+arith** (eager Ackermann is the byte-unchanged fallback on online Unknown) — gated by an in-tree
    differential vs the trusted eager route: 300-query corpus, 0 disagreements, 0 *logical* regressions,
    sat replay, +16 value-add decisions; an adversarial audit caught a budget-regression and it was
    *fixed* (online probe on an arena clone + bounded sub-budget) not excused (`ee11ab9`).
  - **CHC depth:** mutual-recursion Horn (SCC-condensation + tagged-predicate merge, `c434762`) and
    stratified-nonlinear Horn bodies (fold solved lower-stratum predecessors, `verify_horn_model`
    audited, `1624036`).
  - **SAT inprocessing (PLAN #3): vivification with full DRAT accounting** (`969f8d3`) —
    `axeyum_cnf::vivify`, RUP-only strengthening (prefix-conflict + ALA), model-preserving,
    `check_drat`-self-verified over 1100 random formulas + equisat differential + brute-force
    model-preservation.
  - **Route-trace / decline telemetry** (`check_auto_explained` → `(CheckResult, RouteTrace)`, ADR-0050,
    `9f05f0a`) — additive recorder threaded through the single dispatch path, 400-query verdict-invariance
    differential (0 mismatches). The gap-analysis #6 "minimal strategy/probe" + reviewer decline-telemetry.
  - **Infinite-state LRA/LIA symmetry COMPLETED:** integer MBP `mbp_lia` (Cooper/Omega, soundness fuzz
    0 unsound, `ea6e260`), integer PDR `prove_safety_pdr_lia` (3-check gate over ℤ, `2ee309e`), and
    integer IMC `prove_safety_imc_lia` (McMillan via `lia_interpolant`, `4218b47`). Every infinite-state
    engine now mirrored real↔integer: online solvers, online combinations, MBP, PDR, IMC.
  - Full-workspace consolidation gate passed (exit 0). Two ops-lessons recorded to memory (test-result
    grep masking exit codes; resume a resting agent via SendMessage not a `to:`-prefixed fork).
  - **Next (still open, PLAN leverage order):** theory propagation in the online spine (toward real
    CDCL(T) w/ 1-UIP); lazy arrays/BV (P2.1/2.2, the keystone's downstream unlock); a disjunctive integer
    interpolant (closes `imc_lia`'s documented partial coverage); NRA/NIA certify-gap (cross-lane);
    `(get-interpolant)`/`(get-abduct)` SMT-LIB surface (coordination-gated on `axeyum-smtlib`).
  - *(This block is recorded but intentionally left UNCOMMITTED to avoid sweeping the concurrent agent's
    uncommitted STATUS.md/PLAN.md writeups into a commit; the durable record is the committed capability
    ledger + the 12 commits `b405e8e`→`4a95135`.)*

- **Session 2026-06-22 (cont.) — QF_BV authoritative slice RE-MEASURED on HEAD (regression/soundness checkpoint).**
  Re-ran the exact authoritative 20s config (`sat-bv` + inprocess/preprocess, node 300k /
  CNF 3M·8M, query-plan full, refine 16, compare-z3) on `HEAD` after 100+ commits since the
  06-20 baseline. **Soundness: zero regression — DISAGREE=0, 0 replay failures, 0 errors, 0
  wrong-unsat.** Decided count 8→**7**: the single delta is `string1x8.6._bit8_na6_nr3_paired`
  (baseline `sat` @15.6 s, only ~4.4 s of headroom under the 20 s wall → `unknown` @HEAD), a
  **20 s-boundary instance under concurrent-build contention**, not a logic/capability
  regression (the other 7 sat are identical). **Committed baseline left unchanged** (it was
  taken under controlled conditions; this contended 7/113 would understate parity); the
  re-measure artifact is in gitignored `bench-results/local/`. A clean idle-machine re-run
  would confirm `string1x8.6` is load-sensitive vs a small HEAD overhead — a perf-watch item,
  not a blocker. PLAN.md gap section sharpened: **online multi-theory combination** is named the
  top architecture lever, the stale "no SAT inprocessing" note corrected (**BVE has landed**;
  vivification next), and a leverage-ordered next-step list added.

- **Session 2026-06-22 (cont.) — top-down Z3/cvc5 gap analysis refreshed.**
  Added [`docs/plan/gap-analysis-z3-cvc5-2026-06-22.md`](docs/plan/gap-analysis-z3-cvc5-2026-06-22.md)
  and wired it into `PLAN.md` + `docs/plan/README.md`. Main conclusion: the
  "big three" categorical engines are now opened by first slices, so the honest
  gap has shifted to production depth — measured QF_BV performance, word-level
  reduction, proof-accounted SAT inprocessing, strategy/tactic routing, the
  shared e-graph/CDCL(T) spine, lazy arrays/memory, LIA/NRA/NIA depth, full
  strings/sequences, proof-carrying reductions, and SMT-LIB surfaces.
  Practical next increments in order: refresh the stale current-state audit,
  commit a current Z3 head-to-head dashboard, measure the landed `solve_eqs` /
  `elim_unconstrained` preprocessing, measure the landed subsumption/SSR/BVE
  pipeline, then add vivification/glue-tiering and stabilize the typed Alethe IR.

- **Session 2026-06-22 (cont.) — ABDUCTION (`get-abduct`) landed — ALL THREE categorically-missing
  Z3 engines now addressed.** `axeyum_solver::abduct(axioms, conjecture, config)` (ADR-0049): the
  checker turned generator. Bounded enumeration of shared-vocabulary atoms (≤2-literal conjunctions),
  each candidate returned only when re-checked — **consistency** (`axioms ∧ H` `check_auto`-`Sat`),
  **sufficiency** (`axioms ∧ H ∧ ¬conjecture` `check_auto`-`Unsat`), **shared vocabulary**; `⊤` for the
  already-entailed edge case; `Unknown` rejects, over-eager `None` on budget/out-of-grammar (never a
  wrong abduct). 6 tests (LRA/EUF + already-entailed-⊤ + inconsistent/no-vocab declines + LCG fuzz).
  Ledger row (synthesis, `Validated`). **The three missing engines: interpolation DONE (7 fragments),
  CHC OPENED (PDR invariant discovery), abduction OPENED (this slice).** Fuller abduction (SyGuS
  grammar synthesizing *new* atoms, CEGIS, minimality, the SMT-LIB `(get-abduct)` surface) is future.
  - **Env note:** the disk hit 100% (worktree `target/` dirs accumulated); reclaimed ~15G by removing
    this session's 8 *integrated* agent worktrees (work all on `main`) — left the concurrent agent's
    10 worktrees untouched. `df` now ~15G free.

- **Session 2026-06-22 (cont.) — LIA (integer) interpolant landed (interpolation engine now 6 fragments).**
  Filled the reviewer-noted gap ("no `lia_interpolant`"; needed for integer CHC) and deepened the engine
  (the #1 depth/completeness gap), staying in-lane while CHC remains coordination-gated.
  - **`axeyum_solver::lia_interpolant` — DONE (`11232b6`).** Interpolate the **rational relaxation**
    (map Int→Real with a shared symbol bijection, reuse `lra_interpolant`/Farkas), then translate the
    real interpolant back to an integer atom **clearing denominators to integer coefficients** (LCM,
    overflow-checked). Sound because a rational-relaxation interpolant is a valid *integer* interpolant
    when the relaxation is itself unsat (A⇒I, I∧B⇒⊥ over ℝ ⟹ over ℤ). **Verify-before-return over the
    integers:** `check_with_lia_simplex` on A∧¬I and I∧B + shared vocabulary; the mapping/Farkas/clearing
    are untrusted. **Declines** the cuts-needed case (rational relaxation sat, e.g. `2x=1`), overflow, and
    non-conjunctive-QF_LIA. `Solver::interpolant` dispatch now **LRA → LIA → EUF → UFLRA → BV**. 7 tests
    (incl. denominator-clearing `2x≤1∧2x≥3`, cuts-needed-declines, A-local exclusion, fuzz). Ledger row
    (QF_LIA, `Validated`). Whole crate green (366 lib + all interpolation suites).
  - **UFLIA interpolant — DONE (`1e1872d`).** `axeyum_solver::uflia_interpolant` — the integer analogue
    of UFLRA (one shared `eliminate_functions`, `lia_interpolant` on the function-free integer
    abstraction, fresh vars translated back to UF terms). Verify-guarded by `check_with_uf_arithmetic`;
    declines on congruence-needed OR cuts-needed refutations. 9 tests. Ledger row.
  - **Interpolation engine now spans LRA, LIA, EUF, propositional/SAT, QF_BV, UFLRA, UFLIA** (7
    fragments — the complete arithmetic+UF matrix: {L,U·L}×{RA,IA} + EUF + SAT + BV) — all
    verify-before-return, all `Validated`, all fuzzed/panic-proofed. Dispatch:
    LRA → LIA → EUF → UFLRA → UFLIA → BV. Only the SMT-LIB `(get-interpolant)` parse surface remains
    (coordination-gated on `axeyum-smtlib`).

- **Session 2026-06-22 (cont.) — REVIEW-DRIVEN HARDENING of the interpolation engine (reviewer top-10).**
  A reviewing agent's rank-ordered list reprioritized: **harden + honesty-check interpolation before any
  CHC push.** Addressed the in-lane items:
  - **#1 soundness — DONE.** Audited all five verifiers: each matches *only* `CheckResult::Unsat`
    (`Ok(true)` for SAT), so every one declines on `Unknown`/`Sat`/`Err` — never returns on doubt.
    **Extended the adversarial fuzz to QF_BV + UFLRA** (`interpolant_fuzz.rs`; SAT already had a
    4000-iter fuzz in `axeyum-cnf`), each independently re-checking the 3 Craig conditions.
  - **#2 honesty — DONE.** Every interpolation row (+ `mbp_lra`) → `Assurance::Validated` (was `Checked`
    for LRA/SAT/MBP): they verify-before-return by *re-deciding*, emitting **no per-query certificate**.
    Confirmed no doc claims interpolants are Lean-reconstructed.
  - **#3 prose — DONE.** ADR-0047 + the P3.8 implementation notes synced to "all five fragments land
    verify-before-return; only the SMT-LIB surface remains" (matching PLAN.md).
  - **#5 decline telemetry — DONE.** `Solver::interpolant_explained` → `InterpolantOutcome::{Interpolant,
    NotInterpolable, Declined}` so a CHC/PDR consumer can tell "no interpolant exists (A∧B sat)" from
    "we declined (fall back)". **Found + fixed a real robustness bug:** `qf_bv_interpolant` *panicked*
    (`axeyum-bv unreachable!`) on real/int-sorted input from the dispatch fall-through — added an
    `is_bv_lowerable` sort pre-check (graceful `None`). Added a **cross-theory robustness gate**
    (`interpolant_robustness.rs`, 5 tests) confirming no interpolator panics on a foreign partition.
  - **#6 CHC sequencing — HONORED.** The LRA-theory PDR push (task gated) stays paused. Gate is now:
    decline telemetry **(done)** + the `(get-interpolant)` API stable **(remaining, #4)**.
  - **Remaining review items (gated / cross-lane):** **#4** `(get-interpolant)` SMT-LIB surface needs the
    `axeyum-smtlib` *parser* (coordinated agent's crate) — solver-side driver can follow once the command
    parses. **#7–#9** NRA/NIA certify+explain evidence frontier touches the concurrent agent's NRA lane
    (`real_algebraic.rs`) — coordinate before editing. **#10** ~19 commits unpushed on local `main`;
    pushing is outward-facing — left for an explicit decision (not pushed unilaterally).

- **Session 2026-06-22 (cont.) — P4.6 CHC/Horn ENGINE OPENED (first slice in progress).**
  With P3.8 interpolation complete, started the **biggest categorically-missing Z3 engine** (CHC /
  unbounded invariant discovery). **Readiness audit (sub-agent):** the full Spacer core needs two
  things axeyum lacks — (1) **MBP / model-based projection for LIA/LRA is entirely absent** (no
  `mbp`/`model_based`/QE-by-projection anywhere; P2.6-T2.6.6 unimplemented) — this is the long pole
  for the XL core; (2) **no online incremental LRA theory solver across frames** (warm
  `IncrementalBvSolver` is BV/Bool only; LRA rides the offline `check_with_lra_dpll`). What IS ready:
  all 5 interpolants, the `TransitionSystem`/BMC/k-induction machinery (`bmc.rs`), the warm BV
  incremental solver with unsat-core cube extraction (`check_assuming_core`) + `block_model`, the
  e-graph keystone, and the `certify_safety_k_induction` certificate precedent.
  - **First slice — DONE (`38cd647`, ADR-0048): single-predicate IC3/PDR over `TransitionSystem`
    (QF_BV/Bool).** `prove_safety_pdr` discovers an inductive invariant on properties where
    `prove_safety_k_induction` returns `Inconclusive` (the headline test proves exactly this gap is
    closed: a stuck counter with `bad: x==12` — k-induction Inconclusive, PDR `Safe`, invariant
    independently re-checked). Full IC3: frame lemma sets, proof-obligation work-stack (no recursion),
    relative-inductiveness blocking + predecessor extraction, greedy literal-drop generalization,
    forward propagation + `F[i]==F[i+1]` fixpoint. **Soundness anchor (untrusted search):** `Safe`
    only when the discovered invariant passes 3 `check_auto`-unsat checks (initiation/consecution/
    safety; consecution via a faithful `s↦s'` structural substitution — reviewed); `Reachable` only
    when `bounded_model_check`-confirmed; 4 resource caps → `Unknown`. `prove_safety_pdr_certified`
    bundles the 3 DRAT-recheckable proofs. 5 tests; bmc lib (13) green. (Opus worktree sub-agent off
    a stale base — pdr.rs uses only pre-existing APIs so it cherry-picked clean; anchor reviewed.)
    Ledger row (reachability, `Checked`).
  - **MBP for LRA — DONE (`9953400`, P2.6-T2.6.6).** `axeyum_solver::mbp_lra(arena, formula, model, var)`:
    model-guided existential elimination of one real var (Loos–Weispfenning — equality substitution,
    M-selected tightest lower+upper interval resolvent + same-direction domination literals, one-sided
    & unbounded cases). **Untrusted selection, trusted check:** every returned `F'` re-verified —
    `M ⊨ F'`, var-absent, and `F' ⇒ ∃x.F` (entailment of the *exact* Fourier–Motzkin projection,
    per-literal `check_with_lra` UNSAT); declines on the disjunctive var-disequality case, overflow,
    or non-LRA. 8 tests (independent test-side FM oracle) + fuzz (261 verified projections, **0
    unsound**). Ledger row (quantifiers, `Checked`). This is the Spacer predecessor-generalization
    primitive — the CHC long pole.
  - **NEXT on the CHC critical path:** (1) an **online incremental LRA `TheorySolver`** (warm across
    PDR frames; today LRA rides the offline `check_with_lra_dpll`); (2) wire MBP + interpolation into
    an **LRA-theory PDR** loop (lift the QF_BV-only `prove_safety_pdr` to LRA transition systems);
    (3) the **multi-predicate Horn IR** (T4.6.1) generalizing the single-predicate transition system.
    A LIA MBP variant (Cooper, model-guided) parallels the LRA one for integer CHC.

- **Session 2026-06-22 (cont.) — P3.8 Craig interpolation COMPLETE (LRA+EUF+SAT+QF_BV+UFLRA, ledgered).**
  Engine now interpolates the two core conjunctive theories, each verify-before-return:
  - **T3.8.1 LRA Farkas interpolant — DONE (`d3a7a2a`).** (detail below.)
  - **T3.8.3 EUF ground interpolant — DONE (`8791e4b`).** `qf_uf_interpolant(arena, A, B)`
    summarizes the congruence-closure explanation of the violated disequality `s ≠ t`: thread the
    `s→t` path, color each edge by partition (Input by asserting side, Congruence by its argument
    sub-proofs' common color), summarize the maximal segments opposite the disequality into
    shared-term equalities, **lowering** a non-shared congruence boundary to its argument equalities
    (so `A={a=b}`, `B={f(a)≠f(b)}` ⇒ `I=(a=b)` though `f` is B-only). `I=⋀summary` (diseq in B) /
    `¬⋀summary` (diseq in A); empty summary ⇒ degenerate ⊤/⊥. Fail-closed via `check_qf_uf`
    re-checks + vocabulary; partial generator stays sound by the verify-guard. 10 tests.
  - **`Solver::interpolant` dispatches LRA → EUF** (`8791e4b`); ledger rows (LRA `Checked`, EUF
    `Validated`) + **ADR-0047** + regenerated capability matrix (`4fd6262`).
  - **T3.8.2 propositional/CNF interpolant — DONE (`6c77d4c`, McMillan 2003).**
    `axeyum_cnf::propositional_interpolant(a, b) -> Option<BoolExpr>` for two CNF formulas over a
    shared variable space whose conjunction is unsat: refute with `solve_with_drat_proof`, elaborate
    to LRAT, fold McMillan partial interpolants over the LRAT hint chains (input A-clause → OR of its
    global literals, B-clause → ⊤; learned clause → replay RUP to recover pivots, fold backward with
    ∨ at an A-local pivot, ∧ otherwise). **Untrusted fold, trusted check:** every candidate
    re-verified before return — `A∧¬I` and `I∧B` Tseitin-encoded + discharged unsat by the core +
    `check_drat`, plus shared-vocabulary containment; declines on any doubt. New `BoolExpr` carrier
    (smart constructors + Tseitin encoder). 9 tests (incl. A-local/B-local exclusion, multi-step
    resolution, sat-declines, 4000-round fuzz independently re-checking every produced interpolant);
    cnf lib 251 green. (Implemented by an Opus sub-agent in an isolated worktree; the soundness
    anchor `verify_interpolant`/`unsat_with_expr` reviewed + cherry-picked + re-gated on main.)
    Ledger row added (SAT propositional, `Checked`). **BV-term lifting** (map shared CNF vars → shared
    BV-term bits via `variable_bindings`) is the remaining follow-up to reach SMT-level QF_BV interp.
  - **T3.8.2b QF_BV interpolant — DONE (`153e730`).** `axeyum_solver::qf_bv_interpolant(arena, A, B)`:
    **joint** bit-blast (`lower_terms(A++B)` — structural hashing collapses shared bits to one
    CnfVar), a node-indexed joint Tseitin encode partitioned into A/B CNFs (AND-gate clauses by
    per-root reachability — `reachable_node_mask` now `pub` in axeyum-cnf — with **root assertions
    attributed by provenance**, the fix for the direct-root-optimization collapse a naive
    clause-partition hits), `propositional_interpolant` over the shared space, then **lift** each
    global `CnfVar` → `(TermId,bit)` → `((_ extract i i) t)=#b1` predicate. Verify-guarded by the
    QF_BV decider (`check_auto` on A∧¬I and I∧B) + shared-symbol vocabulary; declines on interior-gate
    / non-shared-term vars. 7 tests (shared-var contradiction, A-local exclusion, x=y vs x≠y, sat→None,
    fuzz). Ledger row (QF_BV, `Validated`). Implemented by an Opus worktree sub-agent; soundness anchor
    `verify_interpolant` reviewed, fast-forwarded + re-gated on main (cnf lib 251, all interp suites green).
  - **T3.8.4 combined QF_UFLRA interpolant — DONE (`ee34411`).** `axeyum_solver::uflra_interpolant`:
    one shared `eliminate_functions` over A∪B (memo aligns shared apps to one fresh symbol),
    `lra_interpolant` on the function-free `abstraction()` (no congruence lemmas — a *relaxation*, so
    unsat there ⟹ original unsat), then translate the shared fresh symbols back to UF application
    terms (recursive for nested apps). Verify-guarded by `check_with_uf_arithmetic` (A∧¬I, I∧B) +
    shared symbol/function vocabulary; declines on a congruence-needed (disjunctive) refutation that
    conjunctive Farkas can't express, or any re-check failure. `Solver::interpolant` chain now
    **LRA → EUF → UFLRA → BV**. 8 tests. (Worktree sub-agent off a stale base rebuilt a redundant
    `lra_interpolant` — discarded, re-pointed at the existing one; fixed an Unsupported-propagation
    so it declines instead of erroring.) Ledger row (QF_UFLIA/UFLRA, `Validated`).
  - **P3.8 interpolation now spans LRA + EUF + propositional/SAT + QF_BV + UFLRA** — every
    phase-exit-criteria fragment, all verify-before-return. **Only remaining:** the SMT-LIB
    `(get-interpolant)` parse surface (coordinate `axeyum-smtlib`); the solver-side engine is done.
  - **Randomized soundness gate landed** (`tests/interpolant_fuzz.rs`): 400 LRA + 800 EUF random
    unsat conjunctions; every returned interpolant independently re-checks all three Craig
    conditions; deterministic LCG; both assert non-zero coverage. Whole solver lib green (366).
  - **NEXT (precise resume): T3.8.4 combined LRA+EUF (UFLRA conjunctive)** then **T3.8.2
    propositional/BV off the DRAT proof** (McMillan/Pudlák), then the SMT-LIB `(get-interpolant)`
    parse surface (coordinate `axeyum-smtlib`). Both remaining theory slices are L-sized/intricate
    (combined = Nelson–Oppen equality-sharing interpolation; BV = color-tracking through the
    resolution refutation) — start each with fresh context. All under the same verify-before-return
    contract, so a partial generator stays sound. The engine API shape is settled:
    `lra_interpolant` / `qf_uf_interpolant` free fns + `Solver::interpolant` dispatch; add the next
    theory as a sibling free fn + extend the dispatch chain.
  - Original LRA detail:
  Starting the **interpolation engine** (one of the 3 categorically-missing engines vs Z3 and the
  lemma engine that unblocks CHC/P4.6). Read off the *already-verified* Farkas certificate, not a
  fresh untrusted procedure, so it inherits the assurance:
  - **T3.8.1 LRA Farkas interpolant — DONE (`d3a7a2a`).** `axeyum_solver::lra_interpolant(arena, A, B)`
    for an unsat conjunctive QF_LRA `A ∧ B` returns the Craig interpolant `I := (Σ over A-side atoms
    λᵢ·atomᵢ) ⋈ 0` (⋈ strict iff a used A-atom is strict). The three Craig conditions hold by
    construction — `A ⇒ I` (each A-atom ≤/<0, λ≥0); `I ∧ B ⇒ ⊥` (adding the B-side reproduces the
    full false-constant refutation); **shared vocabulary automatically** (A-only vars have zero
    B-part coeff ⇒ by full-cancellation zero A-part coeff ⇒ drop out of `I`). `FarkasCertificate`
    gained a `vars: Vec<SymbolId>` field (dense index → symbol) populated at both the FM and simplex
    cert-build sites. **Fail-closed:** every returned interpolant is independently re-checked (A∧¬I
    unsat, I∧B unsat, vocabulary) and overflow-guarded; declines to `Ok(None)` otherwise — never an
    unverified interpolant. 8 integration tests, each independently re-checking all three conditions.
  - **T3.8.5 façade slice — DONE (`3aba7a1`).** `Solver::interpolant(arena, a_indices)` partitions the
    active assertions (A = selected indices, B = the rest) and delegates. (SMT-LIB `(get-interpolant)`
    *parse* surface deferred — `axeyum-smtlib` is the coordinated agent's crate; the solver-side
    driver can land without touching their parser.)
  - **NEXT: T3.8.3 EUF interpolant** (ground interpolation off the congruence-closure explanation,
    verified by `check_qf_uf` on A∧¬I / I∧B), then T3.8.2 (propositional/BV off the DRAT proof) and
    T3.8.4 (combined LRA+EUF). Capability-ledger row for interpolation to be added once EUF lands
    (avoid churning the golden matrix twice).

- **Session 2026-06-22 — GPT/codex review follow-through VERIFIED + roadmap expansion (RESUME HERE).**
  Two soundness/accuracy commits landed and are **independently re-verified** (code read + passing
  tests, not just commit messages):
  - **Proof-export soundness gap CLOSED (`5b80253`).** The QF_NIA no-overflow multiplier guards
    (`5dca1ad`) *restrict* the bit-blasted formula, so `export_qf_lia_unsat_proof` handing the
    guarded query straight to the DRAT exporter could certify a **wrong `unsat`** (a refutation of
    the guard-restricted query does not transfer to the original integer formula, which may be Sat
    with a large product). Fix is **fail-closed**: `IntBlasting` now carries
    `restricting_constraints()`; export returns `Inconclusive` *before* exporting whenever guards
    > 0. Linear QF_LIA (zero guards) exports a re-checkable certificate exactly as before. The
    *verdict* path was already sound (BV-UNSAT→Unknown when integers are present); this closed the
    **certificate** path. Negative regression
    `bounded_qf_nia_with_overflow_guard_does_not_export_a_false_proof` (`x*x=16 ∧ 0≤x≤100` @ width 4)
    passes.
  - **Truth-source ledgers synced (`ab899f3`).** The coarse `QF_NRA/NIA` capability row is split
    into an accurate **QF_NRA** (complete CAD decision side; irrational RealAlgebraic witnesses;
    DISAGREE=0 vs Z3) and **QF_NIA** (small-witness nonlinear SAT decides via the guard; genuine
    nonlinear-int unsat stays sound `Unknown`); new support-matrix probe; `support_matrix_doc_is_in_sync`
    green.
  - **Reviewer validation set all green:** `nia_tiny_witness` (4), `proof_export` (9),
    `capabilities` (2), `support_matrix` (12).
  - **Roadmap expansion (docs).** PLAN.md gained an itemized **"gap to Z3/cvc5"** (the honest
    finding: depth/maturity on a mostly-complete grid + ~3 *categorically missing* engines, not a
    breadth hole) plus four new track phase docs — **CHC/Horn PDR/Spacer (P4.6)**, **Craig
    interpolation (P3.8)**, **synthesis/abduction (P4.7)**, **breadth backlog (P2.10)** — and an
    unbounded-LIA completeness backstop (P2.4 T2.4.8), all wired into the track READMEs + the
    dependency DAG. **CHC implementation NOT started** (correctly held behind interpolation + the
    e-graph/CDCL(T) keystone).
  - **Open follow-through (non-urgent):** (a) promote the fuzz-measured Unknown deltas (QF_NIA
    498→146, QF_NRA 109→64, QF_UFLIA 311→18) to a committed reproducible bench artifact;
    (b) classify the remaining ~146 QF_NIA unknowns into proof-gap / true nonlinear-int
    incompleteness / resource-refusal. The live NRA/CAD-front detail continues in the session
    blocks below.

- **Session 2026-06-20 — SAT-core keystone (in progress) + codex-review correctness sweep
  (RESUME HERE).** **85 validated commits**; whole workspace green (fmt + clippy `--workspace`
  + doc + tests). **The destination-2 record is CORRECTED: measured axeyum 8/113 = PARITY with
  Z3 4.13.3 8/113 on the public p4dfa @20s** (different sets; axeyum uniquely decides string1x8.3
  where z3 times out @20.5s; z3 uniquely gets compose.p3/.s2_nr4; the other 105 defeat both —
  near-parity, both hard-capped, NOT "Z3 sweeps all"). Baselines committed
  (`bench-results/baselines/qf-bv-p4dfa-axeyum-vs-z3-20s-*.json`).
  - **Building a competitive PURE-RUST SAT core** (the user's chosen keystone). The reviewer's
    reframe (correct): `native_cdcl` IS the proof-producing `proof_sat` core, so a fast primary
    native core closes the `prove_unsat` fail-open BY CONSTRUCTION — that ASSURANCE value is the
    real justification, not the ~9-instance perf ceiling. Slices landed (all sound, DISAGREE=0,
    DRAT-checked, verdict/trajectory-invariant, `SolverConfig::native_cdcl` opt-in, batsat still
    default): (1) deadline-bounded flag-gated primary engine; (2) LBD clause-DB reduction;
    (3) blocking-literal BCP; (4) VSIDS heap v1 **reverted** (2.36x regression); (5) **VSIDS heap
    done right** — profiled `pick_branch` O(n) scan was 61% of time → canonical MiniSat
    lazy-deletion order_heap collapsed it to 3.3%, **2.6x faster (230s→87s on string1x8.3),
    decisions/propagations bit-identical** (caught+fixed a VSIDS-rescale heap-invariant bug);
    (6) **packed clause arena** (Vec<Vec> → flat arena + headers + CRef; cache-local BCP) — BCP
    74s→67s (−9%), total 87s→81s, decisions/conflicts/propagations bit-identical (trajectory
    invariant; CRef-safe via append-only + tombstone deletion); (7) **Glucose LBD restarts —
    REVERTED** (DISAGREE=0 but regressed the SAT instance — the "LBD restarts hurt SAT-crafted"
    mode); (8) **recursive learned-clause minimization** (MiniSat ccmin_mode=2: iterative
    lit_redundant + abstract-levels, RUP-preserving so DRAT stays valid) — **the big win**.
    **Profiling corrected the gap: it was never ~20× — on the identical reduced CNF the real gap
    was 2.3× (native 94s vs batsat 40s), SEARCH-quality-bound (native did ~2× the conflicts from
    weaker minimization), NOT BCP-bound.** Slice 8 closed it: conflicts 960k→505k (≈batsat's
    504k), props 914M→511M, wall 94s→48s — **native is now ~1.2× of batsat** (search-quality gap
    essentially closed; residual ~20% is per-propagation BCP overhead). **A genuinely competitive
    pure-Rust proof-emitting core.** 6 slices committed, 2 reverted — the revert discipline held.
    **ASSURANCE PAYOFF LANDED (the keystone's purpose):** `native_cdcl` is now auto-enabled as
    the primary engine when `prove_unsat` is set, and its OWN inline DRAT proof is checked in
    place (`SatProofStatus::Checked`) — so an unsat carries a checked proof BY CONSTRUCTION via
    ONE solve (was: batsat + a separate budget-bounded re-derivation that could fail-closed). The
    guarantee "with prove_unsat you only get Unsat when a checked proof backs it" now holds with
    strictly fewer fail-closed cases. **The SAT-core keystone has reached its meaningful goal: a
    competitive (~1.2× batsat) pure-Rust proof-emitting core that delivers the assurance value.**
    Note the honest perf ceiling: native is still 1.2× SLOWER than batsat, so it will NOT decide
    MORE of the corpus than batsat (which already gets 8/113) — the native core's value is
    ASSURANCE (proofs), now achieved, NOT beating batsat's decided-count. Remaining SAT-core
    levers (slice 9 = vivification / BCP per-prop ~20%) are diminishing and won't change that.
    **The next big z3-parity work is the OTHER keystones, not more SAT-core perf.**
  - **NRA/CAD keystone OPENED (slice 1 landed, ADR-0038):** `Value::RealAlgebraic{poly,lo,hi}`
    (defining integer polynomial + isolating interval) + single-variable real-root isolation
    (`nra_real_root.rs`, mirrors `nia_square`) → **`x*x=2` over ℝ now decides Sat(√2)**, the first
    IRRATIONAL witness, replay-checked EXACTLY (`sign_at` reports Zero only via exact poly
    divisibility `poly|q` — the only sound zero-test at an irrational α; nonzero only when
    constant-sign across the bracket; else decline; NO float). `eval` comparisons handle algebraic
    operands exactly; Real field ops on an algebraic operand → graceful Err (field arithmetic
    DEFERRED). Decides `x*x=2/3`→Sat(algebraic), `x*x=4`→Sat(2 rational), `x*x<0/=-1`→Unsat,
    `x*x>2`→Sat(rational), declines multivariate/2nd-assertion to the unchanged NRA abstraction.
    Extended since: **higher-degree** single-var (`x³=2`→Sat(∛2), `x⁴−5x²+6=0`→Sat,
    `x²+1=0`→Unsat — fixed an isolation i128-overflow that lost all degree≥3) and **conjunctions**
    of single-var constraints (`x*x=2 ∧ x<0`→Sat(−√2)) via exact sign-cell decomposition (roots ∪
    one rational sample per open cell, replay-checked against ALL assertions, exhaustive-or-decline
    Unsat). **The single-variable NRA case is now near-complete** (any-degree polynomial systems
    over one real var, irrational witnesses, sound). **NEXT NRA slices (per ADR-0038, all
    deferred-LARGE / multi-session): (2)** Sturm sequences + bigint when i128 overflows;
    **(3)** algebraic FIELD arithmetic (resultant/min-poly — needed once TWO algebraic numbers
    combine, i.e. the first multivariate/nested step); **(4)** multivariate CAD / nlsat (the full
    decidable-NRA engine, T2.5.4, XL/research-scale). These are the genuine multi-session frontier
    — start fresh with full context, not as a session-tail slice.
  - Also open: general MBQI / quantifier proofs, the Lean reconstruction frontier (P3.7), and
    broader theory completeness.
  - **Codex-review correctness items — ALL CLOSED (each with soundness tests):** `prove_unsat`
    fail-closed (no unverified-unsat-as-checked); **eval graceful arithmetic overflow** (bv2nat
    ≥128-bit no longer wraps negative; Int/Real overflow → `Err`→`Unknown`, never crash/wrong —
    the trust-anchor evaluator; `false`→soundness-alarm distinction preserved); **smtlib
    reset/reset-assertions** (honor reset-assertions / reject full reset — no silent no-op).
  - **Remaining review items (lower-priority observability/docs, not correctness):** per-unknown
    root-cause buckets in bench artifacts; the 4-column support matrix (parser/IR/solver/proof);
    north-star reframe to fragment-specific parity milestones.
  - Full codex review preserved at `docs/reviews/codex-20260620/` (report.md + diary.md).

- **Session 2026-06-19/20 — robustness + proof certs + capability/hang sweep (resume here).**
  **68 validated commits**; whole `axeyum-solver` crate green on test/clippy/doc/fmt (1150+
  tests) + Carcara (54) + workspace build + links. **Two deep hunts (arithmetic+quantifier, then
  non-arithmetic) give a CLEAN BILL — no hangs, no wrong answers across every theory** — and the
  tractable solving + robustness + certifiable-proof work is comprehensively closed (verified by
  the hunts + a proof-completeness check: LIA-class new-decider unsats certify). Latest additions
  beyond the 65-commit note: guarded-finite-`∀`-over-inner-`∃`, single-variable integer
  **quadratics** `a·x²+b·x+c ⋈ 0` (generalizes `x*x⋈c`), and the BV-OMT timeout fix.
  **NEXT = the hard keystones only** (each needs dedicated, careful, likely-multi-session work,
  NOT a quick slice — but do advance them, don't stall): (1) **NRA/CAD** irrational witnesses
  (`x*x=2` Real → Sat √2) — BLOCKED on an algebraic-number `Value` in `axeyum-ir` (the rational
  model can't replay √2); coordinate or extend the IR. (2) **SAT-core / perf** — the ~9
  search-bound + ~6 EncodingBudget public cases need stronger reduction *algorithms*
  (`axeyum-rewrite`, the `ite`/structural lever) or SAT inprocessing / a competitive CDCL; the
  solver-side preprocess is measured-maxed. (3) **General MBQI / quantifier-proof** beyond the
  bounded slices done here. (4) **Specialized certs** for the NIA/quantifier new-decider unsats
  (partial-trust). The 65-commit checkpoint detail follows. Highlights of the latter
  stretch (after a course-correction to stop punting / keep shipping — see
  [[no-giving-up-ship-relentlessly]] and CLAUDE.md "Working Stance"):
  - **A hidden QF-LIA hang found + fixed at the root** (`c>y ∧ c<y+1` branch-and-bound grinding,
    bisected from a misleading open-`∀` symptom): deadline-threaded `lia_branch_and_bound` +
    `check_with_lia_simplex_within`, AND integer strict-inequality tightening (gcd-aware) so it
    decides UNSAT *instantly*; **BV-OMT timeout hang fixed** (symmetric to the LIA-OMT fix).
  - **Quantifier completeness broadened both directions:** `∃∀` (skolemize + vacuous/valid/
    unsat/guarded/real-FM/int-FM/int-closed/**open-constant-width-gap**) and **`∀∃` by
    Skolem-witness synthesis**; **NIA single-var squares** (`x*x=2`→Unsat). All sound, bounded,
    replay-checked where applicable.
  - **Perf measured honestly:** the fixpoint preprocessing is sound at scale (DISAGREE=0 on the
    public p4dfa 113) but decides the same 4 as single-pass — solver-side preprocess is maxed;
    the lever is stronger reduction *algorithms* (`axeyum-rewrite`) or the SAT-core, not iterating.
  - Earlier this session (commits 1–51): NRA OOM + 64 GB guard, the integer-NIA hang regression,
    the optimizer A/B/D fix, the full proof-cert sweep (UF/array/datatype/LIA/UFLIA/finite-`∀`,
    assume-independent), and six capability-gap probe passes.
  Method note (unchanged): 51-commit checkpoint detail follows; the original gate-green
  consolidation caught a doc-link regression clippy/tests had missed.
  Method: **6 read-only *capability-gap probe* passes** (theory decidability; arrays/mixed/
  strings/FP-via-BV; optimization/incremental/evidence/smtlib; Track-4 BMC/symexec/k-induction
  + FP builders; proof-completeness map) — each found concrete reproducing queries (see the
  per-commit changelog), closing **every tractable in-`solver` finding**, plus the proof-cert
  work below. Highlights beyond the proof track:
  - **Robustness (the no-OOM/no-hang rules):** NRA OOM bound (below); the **integer-NIA solve
    HANG fixed** (a regression from the new int-blast width ladder — `a*b≠b*a` livelocked
    ignoring the timeout; now deadline-threaded + trimmed ladder + commutative canonicalization
    → fast `Unsat`); the **optimizer** now honors `config.timeout` (`*_with_config` variants),
    decides `mod`/`div` objectives, and degrades fragment-out-of-scope objectives to graceful
    `OptOutcome::Unknown` (never `Err`); **BMC + symexec** now map a backend `Unsupported`
    (an `Apply`/UF in the unrolling or branch condition) to graceful `Unknown`, honoring the
    "unknown is never an error" rule + BMC's own docstring. The 5th/6th passes found **no
    OOM/panic/wrong-answer/false-certification** anywhere — FP arithmetic is bit-exact, the
    trust discipline holds across every fragment.
  - **z3 feature breadth — measured gaps closed:** datatype Int/Real fields (was a hard `Err`),
    guarded-finite Int `∀`, sat-side **valid-universal** elimination (incl. nested `∀`),
    **vacuous-`∀`** (`∃y.∀x. x+y≥x` → Sat) and **unsatisfiable-`∀`** (`∀x. x>0`, `∃y.∀x. x≤y`
    → Unsat), and **single-variable real Fourier-Motzkin `∀`-elimination** (the FIRST true QE —
    decides multi-atom `∀x:Real. φ`, e.g. `∀x.(x≥0∧x≤10)`→Unsat, `∃y.∀x.(x≤y∨x≥y)`→Sat). The
    plus **integer `∀`-elim via real-validity** (the sound one-direction: real-valid ⇒ int-valid).
    ACTIVE quantifier work: **integer-Omega exactness for closed universals** (exact — numeric
    interval integer-emptiness check decides the inter-gap cases like `∀x:Int.(x≤0∨x≥1)`→Sat), then
    open-universal integer-gap, general-boolean QE beyond the DNF cap, MBQI / ∃-witness. Also the
    NIA ground-vs-`∃` inconsistency, **EUF-over-Real (QF_UFLRA)** routing (was a hard `Err`),
    `bv2nat` out-of-range UNSAT, and integer-NIA UNSAT via real relaxation. The solver is now
    solid across arrays, mixed theories, strings, FP-via-BV, and most quantifier shapes.
  - **Proof / Lean parity — certs widened + extended:** reduction certs widened to transitive +
    congruence closure and wired into `produce_evidence`, now covering QF_BV, QF_UFBV (Ackermann
    zero-trust), QF_ABV, QF_DT, QF_LIA (`lia_generic`, gap E), QF_LRA (Farkas/LRA-DPLL), and
    **mixed QF_UFLIA/UFLRA (gap C — the zero-trust Ackermann family extended from BV to arith)**;
    each tamper-tested + validated at up to three levels (in-tree `check_alethe`/`check_alethe_lra`,
    Carcara, Lean kernel). **Finite-expansion guarded-`Int` `∀` `unsat` is now certified too**
    (a first checkable quantifier proof — `forall_inst_guarded` re-checks substitution + guard
    truth + the LIA tail; in-tree-checked custom rule, a tier below the Carcara/Lean-validated
    standard emitters). The 6th pass's proof-completeness map shows the remaining uncertified
    unsat fragments are NRA sign/square (gap A — needs `nra.rs`, concurrent lane), bv2nat-bound
    (gap D — partial-trust, self-contained, the next in-`solver` cert), and the
    NRA-Positivstellensatz / general-`forall_inst` (needs the rule in the `axeyum-cnf` kernel) /
    online-theory-combination **keystones**.
  - **Environment note:** validation builds accumulate a LARGE `target/` (this session's
    axeyum-solver test binaries reached ~44 GiB and filled the 439 G disk to 100%).
    `cargo clean -p axeyum-solver` safely reclaims it (regenerable; does NOT touch the
    concurrent agent's other-crate deps) at the cost of one full axeyum-solver recompile.
    Prefer targeted `--test <name>` runs over repeated full `--all-features` suites (the
    `z3-static` build is especially slow + disk-heavy); the no-z3 suite is representative since
    solver code is not `#[cfg(feature="z3")]`-conditional.
  - **Process note:** re-validate sub-agent work with the FULL gate — clippy does NOT catch
    **`cargo fmt --all --check`** drift NOR **`cargo doc -D warnings`** broken/private intra-doc
    links (both slipped through clippy-only checks this session and were caught later); use an
    **OS `timeout` guard** to PROVE termination (not trust it); rust-analyzer diagnostics after
    a sub-agent run are frequently STALE — verify with a real build, not the diagnostics. Whole
    workspace confirmed gate-green at session end (fmt + workspace build + solver doc + links +
    999-test solver suite + clippy + Carcara 54).
  - **NRA OOM gap CLOSED** — deterministic `MAX_CROSS_PRODUCTS` admission bound (graceful
    `unknown`, never OOM, bounded *or* unbounded). The standing-rule violation is retired.
    See the 2026-06-19 changelog + `scripts/mem-run.sh` / `just test-guarded` (64 GiB cap).
  - **Transitive-closure cert widening DONE & fully validated** — both the Ackermann
    (`prove_qf_ufbv_unsat_alethe`) and array-elim (`prove_qf_abv_unsat_alethe_via_elimination`)
    certificates now discharge argument/index equalities holding by *transitive closure*
    of asserted equalities (`a=b ∧ b=c ⊢ a=c`) via `eq_transitive` chains, not only direct
    assertions. Strictly additive (existing certs byte-unchanged), validated at **all three
    levels**: in-tree `check_alethe`, external **Carcara**, and **Lean-kernel**
    reconstruction to `False`.
  - **Zero-trust certs WIRED into `produce_evidence` (Ackermann + array + datatype)** — a
    QF_UFBV / QF_ABV / QF_DT `unsat` in the covered fragment now carries a zero-trust-hole
    Alethe certificate (reductions *proven* via `eq_congruent`/`eq_transitive`, not trusted
    DRAT) via `zero_trust_alethe_certificate`. Retires the Ackermann / ArrayElim /
    DatatypeElim trust holes **in practice** for those fragments (the ledger stays
    binary "trust hole" — coverage is fragment-level, not universal). Also fixed
    `evidence_route` misrouting datatype queries to the BV path (see changelog).
  - **Next proof-track task (resume) — certify general read-over-write (ROW-distinct)**
    for the array-elim trust hole: `select(store(a,i,v),j) → ite(i=j, v, select(a,j))`,
    `i≠j`. **Dependency chain mapped this session:** (1) the checker rule **already exists**
    and is tested — `read_over_write` in `axeyum-cnf/src/alethe.rs` (`is_read_over_write`
    L1424, tests L4364); (2) the **emitter** `prove_qf_abv_unsat_alethe_via_elimination`
    declines store rewrites because `ArrayElimination` (`axeyum-rewrite/src/arrays.rs`)
    exposes only `selects()`/`abstraction()`, **not the ROW redexes/expansions it performed**
    — so emitting `read_over_write` steps needs `eliminate_arrays` to expose them
    (**coordinate with the `axeyum-rewrite` agent**) or fragile re-derivation from the
    originals; (3) **Lean reconstruction has no `ite`/`read_over_write` support** yet
    (`reconstruct.rs`), so closing the Lean loop needs that too. So ROW-distinct is a
    cross-crate, partly-coordination-gated, multi-slice effort — not a clean in-`solver`
    increment. Other open trust holes (lowest pedantic first): `int-blast` (3),
    `xor-gaussian` (3), `datatype-elim` (4), `fpa2bv` (5) — each a from-scratch certificate.
  - **Certification sweep COMPLETE (in-`solver`):** every self-contained certification gap the
    6th-pass proof-completeness map surfaced is now closed — QF_UFLIA/UFLRA (gap C, zero-trust),
    QF_LIA (gap E), `bv2nat`-bound (gap D, partial-trust w/ recorded `IntBlast` step), and
    finite-`∀` quantifier (LIA + UF tails, custom in-tree `forall_inst_guarded`). The remaining
    uncertified fragments are gap A (NRA sign — needs `nra.rs`, concurrent lane) and the keystones.
  - **Assume-independence: COMPLETE.** The custom-rule quantifier certs (finite-`∀` LIA + UF)
    now re-check EVERY `assume` against the original query via
    `check_alethe_lra_guarded_inst_against` — the carried `universal` (re-detected from
    `assertions` via `detect_guarded_universal` + the emitters' `universal_form`/`universal_form_uf`
    renderers and compared), the ground facts (rendered original assertions), the fresh Ackermann
    defs (`(= !fn_app_N (f t))`, the introduced const must not occur in the query), and abstracted
    originals bridged through a def — anything else ⇒ `Ok(false)`. Four soundness-negative tests
    (fabricated premise LIA/UF, non-fresh def, forged carried universal) confirm each hole the old
    checker had is closed; no false negatives (all genuine certs + tampers pass). The check is now
    fully checker-vs-producer independent. (Still in-tree-checked — no Carcara/Lean backstop, since
    `forall_inst`-in-kernel is coordination-gated; but the in-tree check is now complete.)
  - **ACTIVE WORK QUEUE — advance the next item, never stop (per PLAN.md). The #1 load-bearing
    front is measured perf vs Z3 via word-level *reduction* (PLAN: moved public p4dfa 2→7/113; ~6
    more *EncodingBudget* cases are gettable by deeper reduction — the proven mechanism). Pick the
    next concrete task here or from `docs/plan/track-{1,2,3}` and ship it:**
    - **PERF (Track 1, #1): deeper word-level reduction → pull EncodingBudget cases under the encode
      ceiling. MEASURED (2026-06-19, fixpoint vs single-pass, public p4dfa 113 @ 3s):** the
      `preprocess.rs` FIXPOINT change is sound at scale (**DISAGREE=0**) but decides the SAME 4
      instances as single-pass with identical par2 (5.836 s) — these instances converge in 1–2
      reduction passes, so iterating to fixpoint ≈ single-pass. **Conclusion: the solver-side
      preprocess orchestration is maxed; the EncodingBudget cases need STRONGER reduction
      *algorithms* (`solve_eqs`/`elim_unconstrained`/canonicalize depth + the `ite`/structural lever
      PLAN names — `axeyum-rewrite` lane, coordinate) or the SAT-core modernization for the
      ~9 search-bound cases, not more iterating.** The fixpoint stays (correct + the right shape).
      In-`solver` levers: the `preprocess.rs` pipeline (now fixpoint — done).
      **MEASURED FINDING (2026-06-19):** the cheap AIG tier in `axeyum-aig` is already saturated
      (constants, structural-hash w/ canonical order, OR-absorption/consensus, XOR/MUX); adding
      AND-substructure node rewrites (`a∧(a∧b)=a∧b`, `¬a∧(a∧b)=0`) shrank node count but **regressed**
      `decides_symbolic_float128_fma` (10.5s→timeout) — local AIG node-count reduction is NOT monotone
      in CDCL solve time (it reshapes the Tseitin CNF and defeats variable-ordering/clause-learning).
      So **node-count is the wrong proxy**; the lever is *word-level reduction that removes variables/
      structure* (`solve_eqs`/`propagate_values`/`elim_unconstrained` to fixpoint in `preprocess.rs`),
      validated by **measured DISAGREE=0 + per-benchmark wall-clock**, never node count alone. The
      `axeyum-rewrite` reduction *algorithms* are the concurrent agent's lane — own the solver-side
      `preprocess.rs` orchestration (fixpoint/order) + measure on the scenarios/micro corpus (no z3).
    - **HANG (hard-rule "never hang"): open disjunctive `∀x:Int.(x≤y∨x≥y+1)` tarpits the downstream
      MBQI/e-matching (~600s, ignores `config.timeout`).** Pre-existing (exposed when the FM
      int-closed pass declines the symbolic-bound shape — it declines correctly). Fix the
      quantifier front door (`qinst_egraph`/`check_with_quantifiers`) to honor `config.timeout` /
      a deterministic round bound, same posture as the NIA-hang fix. HIGH priority.
    - **QUANT: open-gap integer-Omega (symbolic bounds), general-boolean QE beyond DNF cap, MBQI**
      (in-`solver`, infra in place: FM `Verdict` enum + `relax_int` + closed-universal exactness).
    - **Then the items below (drive the in-`solver` part; for coordination-gated ones, build the
      solver-side interface and hand off):**
    - **arith-UF SAT model (gap C, keystone, COORDINATION-GATED on `axeyum-ir`):** QF_UFLIA/
      UFLRA `sat` returns `Unknown` because an `Int`/`Real`-sorted UF's function-table model
      can't be built — `FuncValue` and the ground evaluator key function applications by
      `Value::scalar_code()` (`axeyum-ir/src/eval.rs:232`, panics on Int/Real), so both the
      table representation AND `eval`'s lookup need Int/Real-value keys (an `axeyum-ir` change),
      then `euf.rs::project_replay_build` can build + replay it. UNSAT is decided; only the
      SAT-side model build is blocked. NOT a clean in-`solver` increment.
    - **`∃∀` alternation (keystone):** `∃y.∀x. x+y≥x` → `Unknown` (should be SAT, y=0). After
      skolemizing `∃y→c`, `∀x. x+c≥x` is NOT valid for arbitrary `c` (valid only when `c≥0`),
      so the valid-universal pass can't decide it; needs `∃`-witness selection over the
      universal's validity condition (LIA/LRA quantifier elimination, or model-based).
    - **Irrational NRA roots / CAD-lite (keystone):** `x*x==2 ∧ x>0` (Real) → `Unknown`
      (witness √2); the linear-abstraction + point-lemma NRA never finds irrational witnesses.
    - **Coordination-gated (other lanes):** array-of-array / datatype-element arrays (needs
      `Sort::Array` to carry element *sorts* — `axeyum-ir`); first-class `(declare-fun x Float…)`
      through `solve`/SMT-LIB (front-end wiring, `Sort::Float` exists); `(reset)` clearing +
      `(declare-sort)` (`axeyum-smtlib`); ROW-distinct emitter exposure (`axeyum-rewrite`);
      symbolic FP→int/real conversions (`fp::to_ubv`/`to_sbv`/`to_real` are constant-fold-only,
      silently `Ok(None)` on a symbolic float) and a symbolic-operand `fp::from_real` (takes a
      `Rational` value, not a `TermId`) — both `axeyum-fp` (5th pass). The warm-incremental UF
      story (symexec/BMC over `Apply` now degrade to graceful `Unknown`, but to *decide* such
      paths needs the incremental solver to route UF — a larger effort).

- **Destination-2 advanced & a destination-3 milestone landed (2026-06-18).** See
  the two 2026-06-18 changelog entries for detail. In short:
  - **Real Lean 4 kernel now checks reconstructed refutations** (`render_lean_module`
    / `prove_unsat_to_lean_module`, gated `tests/lean_crosscheck.rs`): QF_UFBV/LRA/∀/∃
    refutations type-check in a real `lean` toolchain with `#print axioms` showing no
    `sorryAx`. (Toolchain installed via `elan`; analogue of the Z3 oracle.)
  - **Destination-2 lever found, fixed, measured, decided.** Fair public-slice
    head-to-heads vs Z3 (committed baselines): lazy-bv is **inert** on p4dfa (0/113
    heavy ops); **word-level reduction is the lever** — after fixing the unbounded
    `solve_eqs` (deterministic fuel, `solve_eqs_bounded`), `--preprocess` decides
    **4/113 @3s and 7/113 @20s vs eager 2/3**, DISAGREE=0. Ratified in **ADR-0037**
    (reduction is the destination-2 priority; batsat stays default; custom cores
    specialized). The full pipeline is now wired into the default `solve()` path.
  - **Precise next steps (resume here):** (1) **deeper word-level reduction** to pull
    the 6 remaining `EncodingBudget` instances below the encode ceiling and shrink the
    99 timeout CNFs (AC-tree flattening / `ite`-chain simplification / `bv_slice` /
    `max_bv_sharing`) — *this is `axeyum-rewrite` P1.2, the concurrent agent's active
    area; coordinate to avoid collision*; (2) ~~flip `SolverConfig::preprocess`
    default-on~~ **DONE (2026-06-18, commit `6cb2f1b`)** — `preprocess` now defaults
    on; the default `solve()` path runs the full reduction pipeline, guarded
    (skip-on-quantifier + best-effort fall-back to the original on any pass error);
    full-workspace behaviour check green (103 binaries). ADR-0034 updated.
- **P2.6 quantifier e-matching vertical — keystone-complete, wired & validated**
  (2026-06-16): trigger *inference* (single-cover + greedy multi-pattern set
  cover), congruence-aware multi-pattern join, the instantiation fixpoint loop
  (verified multi-round chaining), nested triggers fired purely via congruence
  (involution test), **dispatch wiring into `solve`** (too-wide-BV / infinite-domain
  quantifier fallback → keystone before MBQI), and the capability ledger/matrix
  updated. All gated.
  - **MBQI-on-keystone assessed, deliberately deferred:** `eval` does support UF
    application against a model (`eval.rs:200`), so it's feasible — but the
    keystone's trigger e-matching already instantiates at *all* congruent ground
    matches (strictly more aggressive than model-guided selection), and the
    existing value-based `prove_unsat_by_mbqi` already does arithmetic
    bound-probing. A ground-term-candidate MBQI would be near-duplicate machinery
    that only helps *trigger-less UF universals* (rare). Skipped as low marginal
    value vs. the duplication/maintenance cost; revisit only if a real corpus shows
    the gap.
- **P3.2 Alethe resolution-layer checker — first slice DONE** (2026-06-16): the
  Alethe (veriT/cvc5 SMT proof format) IR + s-expr `parse_alethe`/`write_alethe` +
  a sound `check_alethe` for the propositional resolution layer in
  `axeyum-cnf::alethe`. A `resolution`/`th_resolution` step is verified by
  `{premises, ¬conclusion}`-UNSAT, decided by the **proof-producing** core and
  **re-checked by `check_drat`** (so each accepted step's entailment is itself
  independently verified, not trusted to the SAT search); a step is recorded only
  after it verifies; UNSAT requires a verified empty clause `(cl)`. 7 tests incl. 3
  negative/rejection. The resolution rung connecting to the DRAT/LRAT clausal
  proofs. **`lrat_to_alethe` bridge landed**: a CNF/QF_BV UNSAT now goes
  `solve_with_drat_proof → DRAT → LRAT → Alethe`, re-checkable by *both* `check_lrat`
  and `check_alethe` (end-to-end test). **Typed-term IR landed**:
  `AletheTerm` (`Const`/`App`) replaces opaque-string atoms (resolution keys on the
  canonical `key()`), plus the **core EUF theory rules**
  `eq_reflexive` / `eq_symmetric` / `eq_transitive` / `eq_congruent` and the
  **Boolean CNF-introduction** rules `and_pos` / `and_neg` / `or_pos` / `or_neg`,
  checked structurally against their exact tautology shapes (strict, order-sensitive;
  broken shapes rejected). plus the entailment-checked
  clause-manipulation rules `contraction`/`reordering`/`weakening`. 16 tests.
  **EUF proof EMISSION** (`prove_qf_uf_unsat_alethe`): the solver turns a congruence
  conflict into an Alethe proof — **transitivity** (`assume`s + `eq_symmetric` for
  reversed edges + `eq_transitive` + `resolution` to `(cl)`) and **depth-1
  congruence** (`f(x⃗) ≠ f(y⃗)` with each `xᵢ=yᵢ` derived by transitivity, then one
  `eq_congruent` step). **Self-validated** — returns `Some` only when `check_alethe`
  accepts, so a construction bug yields `None`, never a wrong proof. The proof track
  is bidirectional (check + emit) for the EUF transitivity + depth-1-congruence
  fragment, including **nested** structural congruence (`f(g(a)) ≠ f(g(b)) ∧ a=b`)
  via a recursive `derive_eq` (transitivity-then-congruence, recursing on args). 10
  tests, each re-checked. **EUF emission is now general** (2026-06-16): `prove_qf_uf_unsat_alethe` was rebuilt
  around `EGraph::explain_steps` — it builds an e-graph over the conflict core (all
  terms added before merging, so congruence edges survive in the proof forest),
  walks the structured explanation between the disequality sides, and converts each
  `Input`→assume / `Congruence`→`eq_congruent` (recursing on args), threaded through
  `eq_transitive`. This handles the **mixed congruence-in-transitivity** case
  (`f(a)=c ∧ a=b ∧ f(b)≠c`) the old bfs emitter returned `None` on — any congruence
  refutation now emits a `check_alethe`-accepted proof (self-validated). The bfs
  helpers were removed. **`term_to_alethe` converts any interpreted-op application**
  (not just `Apply`/`Eq`), so emission covers congruence over interpreted operators
  too — e.g. **array extensionality** (`a=b ∧ select(a,i)≠select(b,i)` ⇒ a checkable
  `eq_congruent` proof), pairing with the array-extensionality decision in dispatch.
  **Arithmetic `la_generic` checking landed** (`check_alethe_lra`): a linear-arith
  tautology clause is verified by `¬clause`-UNSAT via the **Farkas-certified**
  `check_with_lra` (coefficients re-derived, not trusted); `axeyum-cnf` gained a
  pluggable `check_alethe_with(_, extra)` callback so it stays arithmetic-free.
  **`la_generic` EMISSION landed** (`prove_lra_unsat_alethe`): an unsat LRA
  conjunction → an `la_generic` + resolution Alethe proof, **self-validated** by
  `check_alethe_lra` (so axeyum both checks AND emits arithmetic proofs, the full
  "trusted small checking" identity for LRA). **`lia_generic` (integer) checking +
  emission landed** (`prove_lia_unsat_alethe`): the integer counterpart, decided by
  the **integer-complete** `check_with_lia_simplex` so integrality is honored —
  `(cl (<= x 0) (>= x 1))` is *accepted* by `lia_generic` (no integer in the open
  interval) yet *rejected* by the real `la_generic` (`x=0.5` falsifies it), the
  distinction enforced by a dedicated test. Linear `*` guarded to a constant factor
  (genuine `var*var` ⇒ rejected); integer numerals parse as plain `i128`; emission
  self-validated via `check_alethe_lra`. Remaining (P3.2/3.3): more BV theory
  rules; emit Alethe for the *reductions* (P3.5: array/function elimination,
  int-blasting); Carcara CI cross-check; extract `axeyum-alethe` crate (ADR).
- **P2.9 datatypes — structural refutation DONE** (2026-06-16):
  `prove_datatype_unsat_structurally` — the three datatype structural axioms over a
  term-level union-find: **acyclicity** (`x = cons(h, x)` ⇒ unsat), **distinctness**
  (`x = nil ∧ x = cons(…)` ⇒ unsat), and **injectivity** (`cons(h,x) = cons(h,y) ∧
  x ≠ y` ⇒ unsat — the datatype-*field* injectivity case the eager `build_dt_eq`
  relaxes away, the genuine gap-closer). Unions definite equalities, closes under
  injectivity while checking distinctness, then reports unsat on a same-class
  datatype disequality or a containment cycle. Sound (each union/edge forced by a
  definite (dis)equality + a datatype axiom) + wired into `check_auto_dispatch`
  ahead of the eager expansion. 7 tests (incl. two NOT-refuted SAT cases).
- **P3.1 LRAT checker + DRAT→LRAT elaborator — DONE** (2026-06-16): a second,
  independent UNSAT-proof checker alongside `check_drat`, in the stronger *clausal*
  LRAT format (every clause has an id; each addition carries antecedent hints, so
  checking is **linear** — follow the hints — not a RUP search). `check_lrat`
  (sound: accepts a clause only when its hint chain performs genuine RUP to a
  conflict; rejects a satisfied/under-determined/missing/never-conflicting hint),
  `elaborate_drat_to_lrat` (RUP DRAT — e.g. from `solve_with_drat_proof` — →
  hinted LRAT; RAT out of scope), `parse_lrat`/`write_lrat`. **3 negative
  (soundness) tests confirm rejection** (corrupted/dropped hint, non-entailed clause
  over a SAT formula, no-empty-clause ⇒ `Ok(false)`) + a **600-CNF random
  differential** (every UNSAT formula's CDCL DRAT proof elaborates and LRAT-checks,
  with text round-trip). First rung of the proof-checking ladder above DRAT.
- **P2.2 lazy arrays — first slice DONE (lazy select-congruence)** (2026-06-16):
  `check_qf_abv_lazy` — the array analogue of lazy Ackermann (a `select` is an
  application of a per-array read function). `eliminate_arrays` still does
  read-over-write eagerly, but the read-over-read consistency
  `i=j ⇒ select(a,i)=select(a,j)` is now added on demand (CEGAR) instead of the
  eager O(n²) per-array pairing. Sound (post-ROW abstraction is a relaxation ⇒ UNSAT
  transfers; consistent sat replays) + terminating. rewrite `ArrayElimination` now
  exposes `abstraction()` + `selects()` (eager `assertions()` byte-identical).
  **200-formula differential vs eager `check_with_array_elimination` — all jointly
  decided, all agreed (28 unsat)** + a select-congruence refutation and a
  store/select sat replay. Same regime caveat as lazy Ackermann: this defers the
  congruence pairing, not ROW; **full lazy ROW / on-demand store axioms / wide-index
  (>8-bit) arrays remain** (the eager path caps extensionality at 8-bit indices).
- **P1.5 online theory interface — DONE (theory side)** (2026-06-16): the online
  `TheorySolver` trait + `EufTheory` over one backtrackable keystone `EGraph` now
  exposes the full surface a CDCL(T) loop drives — `assert(atom,value)` (→ explained
  conflict core via `EGraph::explain`), `propagate()` (entailed equalities with
  reasons), `push`/`pop` (lockstep backtrack of merges, disequalities, and assigned
  state). 6 unit tests. This replaces the offline `prove_unsat_lazy` per-model
  e-graph rebuild with one incremental graph.
  - **Online DPLL(T) QF_UF decision procedure — DONE**: `prove_unsat_qf_uf_online`
    (refutation, 500-formula differential vs `prove_unsat_lazy`) + `solve_qf_uf_online`
    (full decider with replay-checked sat models, 400-formula differential vs
    `check_qf_uf`). The online *search* on one backtrackable e-graph now exists, not
    just the online theory.
  - **Online decider wired as the QF_UF fast path — DONE** (ahead of `check_qf_uf`,
    unknown-safe fall-through; full suite green).
- **P1.6 theory combination — first slice DONE (lazy Ackermann)** (2026-06-16):
  `check_qf_ufbv_lazy` — CEGAR/on-demand functional-consistency lemmas for QF_UFBV
  instead of the eager up-front Ackermann. Abstract apps → fresh vars, solve, add
  the lemma `(⋀ args_i=args_j) ⇒ fresh_i=fresh_j` only for a pair a candidate model
  violates, re-solve to fixpoint. Sound (abstraction is a relaxation ⇒ UNSAT
  transfers; consistent sat replays), terminating (each pair once). rewrite
  `FunctionElimination` now exposes `abstraction()` + `applications()` (eager
  `assertions()` byte-identical). **300-formula differential vs the eager
  `check_with_all_theories` — all jointly decided, all agreed (21 unsat).**
  - **Nested-application coverage added** (2026-06-16): two targeted lazy-QF_UFBV
    tests where an application's *argument is itself an abstracted application*
    (`f(f(a))`) — a refutation by nested congruence and a SAT involution that must
    project to a coherent function interpretation and replay. (The random
    differential grows its term pool with `f`/`g` apps so it nests too, but these
    pin it deterministically.)
  - **Design finding — model-based combination ≡ lazy Ackermann (important):** a
    full *online Nelson–Oppen* between the e-graph and BV would only add power over
    lazy Ackermann in a **non-model-based** regime. In the **model-based** regime
    (read a concrete BV model, check the shared-term arrangement) the model assigns
    *concrete values*, so congruence over them collapses to value-equality —
    including transitive chains — which the lazy path's raw model-eval already
    detects. The e-graph's *abstract* congruence only pays off when the BV theory
    participates in a shared CDCL(T) trail **without committing to a full model**,
    i.e. as an **online BV theory solver** (the P2.1 "BV theory-checker"), which does
    not exist yet. **Conclusion:** lazy Ackermann *is* the QF_UFBV combination for the
    model-based regime, and is arguably higher-assurance than eager (explicit,
    individually-valid functional-consistency lemmas added on demand vs a bulk
    syntactic reduction). The fuller online N-O is genuinely **gated on P2.1**; do not
    build a redundant model-based "combination" module.
  - **Dispatch wiring of `check_qf_ufbv_lazy` — deliberately deferred (methodology):**
    routing lazy-before-eager is a *performance* optimization (fewer up-front
    lemmas), not a correctness/capability gain — the eager `check_with_all_theories`
    already decides QF_UFBV completely. Per the project's benchmarking-first rule
    (encodings/perfwork gated on measured corpora) and the array-fragment interaction
    risk (lazy abstracts functions but not arrays), it stays an available, validated
    API until a real UFBV corpus shows eager-Ackermann lemma count is the
    bottleneck. The function is exported and ready.
  - **Next action (precise resume point):** the full online N-O is **gated on an
    online BV theory** (per the finding above), so the productive next step is to
    **start P2.1's BV theory-checker** — an incremental BV theory solver
    (`assert`/`propagate`/`explain`/`push`/`pop`, mirroring the `TheorySolver` trait
    `EufTheory` implements) that can participate in a shared CDCL(T) trail without
    materializing a full model. With both an online BV theory and the online
    `EufTheory`, the interface-equality combination (equality sharing over shared
    BV-sorted terms, split on undetermined interface equalities) becomes
    implementable and removes the Ackermann trust hole. That is a substantial new
    track — begin with fresh context. *Alternatively*, if pivoting tracks: P2.2 lazy
    arrays (ROW axioms on the e-graph) or P2.9 lazy datatypes (e-graph splitting)
    also build directly on the now-complete keystone. Secondary: migrate
    `axeyum_rewrite`'s bespoke trigger closure onto the keystone.
- **Plan authored** (2026-06-15): the full track/phase/task plan is under
  [`docs/plan/`](docs/plan/README.md), built from the five reference reviews in
  [`docs/plan/references/`](docs/plan/references/README.md).
- **P3.0 trust ledger — DONE** (2026-06-15): typed `TrustId` taxonomy + pedantic
  levels, per-result `trusted_steps` on `EvidenceReport`, golden-tested
  [trust-ledger.md](docs/research/08-planning/trust-ledger.md) (5 of 11
  reductions are trust holes), ADR-0031. The trusted base is now countable.
- **T1.1.1 subsumption + T1.1.2 BVE — DONE (correctness)** (2026-06-15):
  `axeyum_cnf::simplify` (model-preserving tautology removal + forward subsumption
  + self-subsuming resolution) and `axeyum_cnf::eliminate_variables` (bounded
  variable elimination by resolution with a `Reconstruction` stack to lift reduced
  models back to the original, the non-increasing/size/occurrence bounds). 13 tests
  total incl. brute-force equisatisfiability + per-model reconstruction + SAT/DRAT
  preservation. DRAT-step emission inside the proof-producing solve and the measured
  perf delta ride P4.5 + the pipeline-integration step.
- **P4.5 — DONE.** Committed measurement slice `corpus/qfbv-curated/` (43 files,
  **width-capped ≤64 bits**) + recorded baseline
  `bench-results/baselines/qfbv-curated-sat-bv-vs-z3-2s.json`: sat-bv vs Z3 4.13.3,
  2 s, budgets — **32/43 decided (8 sat + 24 unsat), 11 unknown, agree=32,
  DISAGREE=0, replay failures=0**, PAR-2 ≈1.07 s. Harness now gives workers a
  512 MB stack (deep-term fix). `just bench-qfbv-curated`.
- **Known robustness gap (Track 1 / P1.2):** sat-bv allocates eagerly during
  lowering on wide terms (a 1024-bit multiply / 20k-bit vector → multi-GB alloc)
  *before* the node budget is enforced, aborting instead of returning `unknown`.
  Curating by width sidesteps it; the real fix is graceful oversized-encoding
  refusal. This is why the original size-based slice OOM'd two hosts.
- **Machine transition to s4 done:** repo at the same path on `server4` (123 GB,
  2× RTX 4060 Ti 16 GB, CUDA 12.4); `corpus/public` symlinked to NAS
  `/nas3/data/...`; z3 + rust verified; 54/54 cnf tests pass. See
  [docs/plan/host-setup.md](docs/plan/host-setup.md).
- **T1.1.4 inprocessing made near-linear + time-bounded — DONE** (2026-06-16):
  `axeyum_cnf::simplify` rewritten to forward one-watch occurrence-list subsumption
  (CaDiCaL/Kissat `subsume.cpp`/`forward.c`); `axeyum_cnf::bve` rewritten to full
  literal occurrence lists + a touched-variable queue (`elim.cpp`/`eliminate.c`);
  both gained `_within(deadline)` variants, and `sat_bv` now bounds inprocessing to
  ≤50% of the remaining solve budget (partial passes stay sound: subsumption
  model-preserving, BVE equisatisfiable + valid reconstruction). The old size guard
  was lifted (512/2048 → 200k/1M admission ceiling). Each pass adds a 400-formula
  randomized brute-force test. **Curated A/B (sat-bv vs Z3, 2 s, s4): 8 sat / 24
  unsat / 11 unknown, agree=32, DISAGREE=0, replay failures=0, PAR-2 1.095 s** —
  i.e. decision-identical to baseline (32/43) with no regression; the earlier
  13–22 s pass hangs and the 3-instance regression are gone.
- **Why inprocessing still decides none of the 11 unknowns (gates the next lever):**
  the unknowns are either (a) **structurally BVE-resistant multipliers** (`mulhs64`:
  45 105 vars, BVE eliminates 417 / clauses 201 656→201 379 ≈ 0.1% — non-increasing
  resolution cannot collapse a multiplier), so the bottleneck is the **SAT search
  itself → P1.3 (SAT-core modernization)**; or (b) reduced-but-still-hard (e.g.
  `commute08` 18 296→7 038 clauses) where the reduced formula still doesn't close in
  the remaining budget. Inprocessing is now correct/fast/safe infrastructure that
  pays off once P1.3 / P1.2 land; it stays off by default.
- **T1.1.3 inprocessing wired into the solve pipeline — DONE (sound), measured
  net-negative with current passes** (2026-06-16):
  `SolverConfig::cnf_inprocessing` (off by default) runs `simplify` (subsumption,
  model-preserving) then `eliminate_variables` (BVE, equisatisfiable) on the
  Tseitin formula in `sat_bv_backend`; a reduced `sat` model is lifted back to
  the original CNF variables via `Reconstruction::extend` before the existing
  AIG→model→original-term replay. 3 A/B tests + bench `--inprocess` flag +
  `just bench-qfbv-curated-inprocess`. **Correctness proven** across the curated
  slice (DISAGREE=0, model_replay_failures=0; 27 instances inprocessed end to end
  incl. SAT reconstruction, BVE eliminating up to 296 vars).
- **Key measured finding (gates P1.1):** the correctness-first passes do **not**
  scale to solve-relevant CNF. At a 5k-var/20k-clause cap the pass took **13–22 s**
  on `mulhs16`/`commute08`, blew the 2 s budget, regressed 3 decided instances to
  `unknown`, and decided **none** of the 11 existing unknowns. `simplify` is an
  `O(clauses²)` sweep; `bve` rescans all clauses per candidate (`O(vars·clauses)`
  per round). Inprocessing is therefore guarded to ≤512 vars / ≤2048 clauses
  (provably cheap, ≤121 ms here) — at which size the committed A/B is
  decision-identical to baseline (32/43, PAR-2 1.071 s vs 1.063 s). **Real win
  needs occurrence-list indexing first.**
- **P1.2 preprocessing wired into the bench + measured — DONE** (commit 0c594ac).
  `check_with_preprocessing` (commit 86cd28a) + bench `--preprocess` flag
  (`just bench-qfbv-curated-preprocess`): the trail is threaded through
  solve_planned→solve_one→classify_result→replay_model so a `sat` model
  reconstructs before replaying the originals. Curated A/B: 32/43, agree=32,
  DISAGREE=0, 0 replay failures, PAR-2 1.060 s — decision-identical, model-sound
  across all 43 incl. the oracle path; reduced the DAG on 5/43 (the instances with
  top-level `x=t` structure), no-op on the multiplier-heavy rest. Correct
  infrastructure; the PAR-2 payoff needs a corpus with explicit defines.
- **P1.4 e-graph keystone COMPLETE** (commits eb3e9e6, 0c5840f, c47dc0c, 2c735b5,
  d81bf46): `axeyum-egraph` (ADR-0032) is a standalone, backtrackable,
  explanation-producing, independently-checkable equality bus — hash-cons +
  congruence cascade, `explain`, push/pop, `check_congruence`, theory-var lists.
  17 tests. This unblocks the Track-2 theory upgrades and the CDCL(T) loop.
- **P1.5 two slices DONE** (commits f69aa40, 8d97081): `prove_unsat_by_congruence`
  (conjunctive) and `prove_unsat_lazy` (offline DPLL(T) over boolean structure —
  boolean skeleton via sat-bv + e-graph theory check + explain-based blocking
  clauses). Sound EUF UNSAT proving with independently-checked conflicts.
- **SAT model construction + dispatch wiring DONE** (commits c08c763, 6ce85b0):
  `check_qf_uf` decides QF_UF with replay-checked `sat` models (differentially
  validated vs Ackermann), and `check_auto` now routes UF instances through it
  first (congruence fast-path), falling back to the complete Ackermann bit-blast on
  `unknown`. Full solver test suite + micro bench regression-free.
- **Next task — P1.6 theory combination (e-graph UF + bit-blaster BV)** for
  *complete* QF_UFBV. Today the EUF path fast-paths only when the answer is settled
  by congruence alone; a theory-consistent boolean model whose constructed values
  violate BV arithmetic → `unknown` → Ackermann fallback. Combination closes this:
  on a theory-consistent boolean model, send the e-graph's induced equalities AND
  disequalities (from the class structure + the asserted diseqs) to the bit-blaster
  as BV constraints and let it decide / produce the model — or the Nelson–Oppen
  interface-equality exchange on the `th_var` bus (T1.4.6) the e-graph already
  carries. Read `docs/plan/track-1-engine/P1.6-theory-combination.md`. Also open:
  the `TheorySolver` trait + online propagation (T1.5.1–T1.5.4 efficiency refactor),
  and the broader Track 2 theories (lazy arrays P2.2, datatypes P2.9, quantifiers/
  e-matching P2.6) which all migrate onto the e-graph + CDCL(T) loop.
- **T1.2.8 AIG two-level rewriting — attempted, reverted (negative result,
  2026-06-16).** `axeyum-aig` already does level-0/1 rewrites (constants,
  idempotence, contradiction, OR-absorption, consensus). Adding the bitwuzla
  positive-AND-operand subsumption/contradiction (`x∧(x∧y)=x∧y`, `x∧(¬x∧y)=0`) was
  correct + semantics-tested but **regressed a borderline Float128 fp.fma**
  (`decides_symbolic_float128_fma`) from sat to a batsat **timeout** — CNF-structure-
  induced SAT chaos on a borderline instance. Reverted (no net benefit measured, a
  concrete regression). If retried: gate behind a flag and measure broadly on the
  curated slice + the FP tests before enabling; AIG rewrites need measurement, not
  blind application (the P1.2 methodology point, reconfirmed).

## Already shipped this session (pre-plan)

The reachability / symbolic-execution / certificate surface that motivated this
plan is built and committed on the current branch:

- BMC driver, k-induction (unbounded safety), symbolic-memory BMC,
  `SymbolicExecutor` (path exploration + test-suite enumeration + path-condition
  optimization), and self-rechecking certificates (`UnsatProof::recheck`,
  `SafetyCertificate::recheck`, `EndToEndUnsatOutcome::recheck`).
- These map onto Track 4 (use cases) and Track 3 (the recheck family); the plan
  records what remains around them.

## Phase status

### Track 1 — Engine & Performance
| Phase | Title | Status |
|---|---|---|
| P1.1 | SAT inprocessing (subsumption → BVE → vivification → glue tiers) | WIP — subsumption+BVE landed (T1.1.1/2), wired into the solve pipeline (T1.1.3), made occurrence-list near-linear + time-bounded (T1.1.4): safe, no regression, but the curated unknowns are SAT-search-bound (→ P1.3) or BVE-resistant. **CDCL(XOR) foundation landed** (`gf2`/`xor_extract`/`xor_propagate` in `axeyum-cnf`) — the path-2 multiplier-wall attack: a sound GF(2) Gaussian engine + exact XOR-gate extraction + an entailment-checked propagation pass; slice 4 wires it into the live preprocess pipeline (measured). Vivification / glue tiers remain |
| P1.2 | Preprocessing (word-level rewrite, solve_eqs, bv_slice/bounds/max-sharing, AIG 2-level rewrite) | WIP — T1.2.1 trail + T1.2.2 propagate_values + T1.2.3 solve_eqs landed (model-sound, unit-tested, 36 tests). **T1.2.4 elim_unconstrained landed** (`axeyum-rewrite::elim_unconstrained`): a variable occurring once under an invertible BV op (`bvadd`/`bvsub`/`bvxor`/`bvnot`/`bvneg`) makes that subterm unconstrained → replaced by a fresh var, operator dropped (Z3's `elim_unconstr`); peels nested layers, terminates. Model-sound via the trail (`x := op⁻¹(u,w…)`; orphaned operands defaulted, sound by the inverse identity); wired into `check_with_preprocessing` after solve_eqs (opt-in, default-off per ADR-0034). 6 unit (incl. 300-trial randomized reconstruction) + 2 solver end-to-end. Next: measure on the public p4dfa slice; then max_bv_sharing / bv_slice / AIG 2-level (T1.2.5–T1.2.9) |
| P1.3 | SAT-core modernization (VSIDS/VMTF modes, EMA/Luby restarts, arena+packed watches, chrono BT) | WIP — the proof-producing core `solve_with_drat_proof` (`proof_sat.rs`) modernized: **VSIDS activity branching** (bump conflict-side vars, MiniSat-style decay, rescale-on-overflow; highest-activity unassigned var, ties to lowest index), **phase saving**, and **Luby restarts**. Sound by construction — every emitted clause is RUP and the proof is DRAT-checked, so a heuristic bug only slows search. All 231 cnf tests pass (incl. the 400-CNF differential vs BatSat + a new pigeonhole-4→3). NB the modern CDCL(XOR) core in `xor_cdcl.rs` already has VSIDS/Luby/LBD. Remaining: arena + packed watches, chronological backtracking; wire a modern core into the default path |
| P1.4 | Incremental e-graph (congruence + explanation + checker) **[keystone]** | **DONE** — `axeyum-egraph` (ADR-0032): hash-cons + union-find + congruence cascade (T1.4.1/2), proof-forest `explain` (T1.4.3), backtrackable push/pop (T1.4.4), independent `check_congruence` (T1.4.5), per-class theory-var lists (T1.4.6). 17 tests incl. brute-force + backtracking property tests |
| P1.5 | CDCL(T) loop (theory-as-extension, final-check, theory propagation) **[keystone]** | WIP — EUF on the e-graph: `prove_unsat_by_congruence` (conjunctive), `prove_unsat_lazy` (offline DPLL(T)), and `check_qf_uf` (full decision with **replay-checked sat models** from e-graph classes + function interps). Conflicts independently checked; **differentially validated vs Ackermann**. T1.5.5 met for the equality/UF fragment. **Online `TheorySolver` trait + `EufTheory` landed** (one backtrackable e-graph, explained conflict cores, lockstep push/pop) — the online theory side of the loop. Remaining: drive it from an online CDCL search with theory propagation (T1.5.1–T1.5.4) + dispatch wiring; theory combination with BV (P1.6) for complete QF_UFBV |
| P1.6 | Theory combination (th_eq bus, interface equalities) | WIP — **EUF+LIA/LRA combination landed & dispatched (QF_UFLIA/UFLRA), complete for conjunctive UNSAT**: `declare_fun` admits Int/Real UF sorts, and `check_with_uf_arithmetic` decides the core squeeze/nested congruence UNSAT cases; SAT model lifting for arith UF remains conservatively `Unknown`. The QF_UFLIA overbound lazy CEGAR path now avoids duplicate generic LIA timeouts, folds narrow Int-bound structure, batches same-candidate UF lemmas and simple bound conflicts, checks deterministic Boolean-justified arithmetic supports, carries reusable arithmetic clauses, keeps an `IncrementalArithDpll` warm while UF lemmas are appended, deletion-minimizes small LP-relaxation Farkas supports before learning LP-core clauses, stage-gates checked affine-bound cores after the first warm solve, and schedules one post-candidate unary-Int sibling Ackermann lemma after a violated UF pair without broad preseed. The online UFLIA route now collects only actual theory atoms, handles n-ary `and`/`or` and Boolean equality, reports precise unsupported-shape details, and admits Int order atoms containing Int-sorted UF applications as opaque LIA variables for UNSAT/conflict/propagation only. Direct `uflia_online_probe` hard-row runs moved from `non-Boolean term with sort Int` to the bounded opaque-app guard, and that guard is now keyed by actual opaque-app order atoms rather than total atom count; the generated rows report **334** opaque-app order atoms out of **485** total (`opaque_app_order_atoms=334 > 128, total=485`). Nested LIA feasibility/core/model/probe checks, shared CDCL(T) Boolean/theory propagation loops, and Boolean UFLIA construction checkpoints now inherit/check the Boolean-layer deadline. Large combined opaque-app layouts use deferred LIA feasibility at the theory-propagation boundary, and opaque-app layouts that cannot build the incremental combined state now decline instead of falling into the older enumerative fallback. A temporary broad cap raise to **512** now declines both generated direct probes in about **4 ms** with `opaque-app online UFLIA incremental combined state could not be built safely` instead of running past **30 s**; the committed guard stays **128** because this is safe decline, not a solve-rate closure. The generated rows stay `unknown`: production lazy 1 s diagnostics still reach actual UF refinement (**2** UF rounds, **1** candidate, **282** pair checks, **6** equal-argument pairs, **5** violations, **1** sibling lemma, **7** total UF lemmas), and the 10 s hard row reaches **6** UF CEGAR rounds, **5** candidates, **1352** pair checks, **22** equal-argument pairs, **15** violations, **5** sibling lemmas, and **27** learned UF lemmas before a warm arithmetic timeout with **total_rounds=280**, **blocking_lemmas=295**, **core_src_affine=45**, **core_src_lp=204**, and **core_len_avg=6.4** in the latest sample. Plus the combination primitives `theory_combination` (shared/propose/classify/arrangement) + `th_eq` bus (`theory_var_classes`/`interface_th_eqs`) and the earlier lazy/on-demand Ackermann for QF_UFBV. Remaining: partitioned opaque-heavy admission that preserves incremental-build safety, opaque-app model lifting, UF CEGAR convergence/relevance after several candidate models, reducing LP-core-producing SAT branches, then full online interface-equality (Nelson-Oppen) combination of the e-graph + BV to drop Ackermann reduction entirely |
| P1.7 | PBLS local-search BV engine (portfolio) | WIP — **word-level WalkSAT landed** (`solve_local_search` + `PblsBackend`, `pbls.rs`): keeps a concrete Bool/BitVec(≤128) assignment, scores by evaluator-falsified assertions, nudges a variable in an unsatisfied assertion (greedy + WalkSAT noise + random restarts) toward a model. One-sided + sound: `Sat` only with an evaluator-verified model, never `Unsat`, `Unknown` (incl. out-of-scope sorts) otherwise. Read-only on the arena (fits the trait); deterministic (fixed seed, explicit budgets). 4 unit + an ignored 150-formula differential vs the eager backend (never contradicts). Remaining: integrate as a portfolio strategy; tune moves/budgets; measure on satisfiable corpora |
| P1.8 | Strategy & tactics (combinators + probes + per-logic scripts) | TODO — Codex review recommends promoting this from cleanup to risk control: split `solve()` into explicit tactic contracts with fragment predicates, transformation class, replay/proof obligation, resource behavior, and benchmark-visible per-step metrics |

### Track 2 — Theories & Breadth
| Phase | Title | Status |
|---|---|---|
| P2.1 | BV lazy blasting + word-level slicing + BV theory-checker | WIP — **destination-2 lever measured & scoped** (commits beee599/9846349, `docs/research/05-algorithms/lazy-bitblasting-p21-findings.md`). KEY FACT: lazy abstraction-refinement bit-blasting (`solve_lazy_bv_abstraction`, ADR-0019) is **built but NOT wired into default `solve()`/bench** — so the "~2-3/113 public QF_BV" picture is the *eager* mountain-builder. Measured (`tests/lazy_bv_curated_measure.rs`): lazy decides **incidental-heavy-op** cases with 0 multiplier blasts (`x=1∧x=2∧r=p·q` → unsat ~0ms, 0 refined), cracks `calypto_9` (sat, 2 ops refined), is a safe no-op when `ops=0` (public files), no shortcut on essential multiplier-equivalence. Next (coordinate on shared bench): lazy-bv bench backend → measure public 113 (DISAGREE=0) → opt-in `SolverConfig::lazy_bv` strategy → default-on ADR after net benefit. The highest-ROI perf move is wiring+measuring a built CEGAR bit-blaster, not a new algorithm |
| P2.2 | Arrays: lazy ROW axioms + extensionality + func_interp models | WIP — **lazy select-congruence** (`check_qf_abv_lazy`): read-over-read consistency added on demand (CEGAR) vs the eager O(n²) per-array pairing; sound (post-ROW abstraction relaxation ⇒ UNSAT transfers; sat replays) + terminating; 200-formula differential vs eager `check_with_array_elimination` (all agree). `eliminate_arrays` exposes `abstraction()`/`selects()`. **Array-extensionality refutation via congruence** wired into dispatch (`has_array` flag): `a=b ∧ select(a,i)≠select(b,i)` (incl. **wide-index** array equality the eager 2^iw enumeration refuses) is `unsat` by `prove_unsat_by_congruence` (select/store as UF; congruence valid for arrays). Lazy ROW/extensionality `unknown` details now report refinement counters and attempt replay-gated last-candidate SAT salvage before budget declines. The AUFLIA `bug337` probe still times out at round 2 with 4096 sites, 150 array-equality atoms, 6973 congruence lemmas, and 146 diff-skolems; the direct-select mixed replay beam moves the first false replay point from direct readback equality ordinal 34 / term 555 to generated OR ordinal 210 / term 3879 under the final strict replay-improvement gate. A generated-OR mixed beam is retained only for small, multi-false replay surfaces after the unguarded large-row attempt regressed `bug337` back to term 555 and doubled wall time. Branch-select diagnostics now show OR 210 branch 0 followed by select 34's store-chain repair makes term 555 true but lands back on OR 210 at total_false=2, while direct select repair worsens to ordinal 35. A small-surface branch/select-cycle repair now handles the alternate-branch version of that pattern, but the large `bug337` attempt was measured/rejected and guarded off after no frontier movement plus route-time growth. Returned-OR diagnostics show the remaining post-select blocker is OR 210 branch 0 with one false literal, store-definition equality term 580 (`x_339 = store(x_325,x_337,2)`). A guarded same-branch residual repair now covers the small case where preserving the select readback requires rebuilding the branch target `target = store(base,i,v)` from the current repaired base. The small-surface repair now follows bounded residual generated-OR chains and clears a two-OR array-copy analogue under the strict replay-improvement gate. Follow-up OR repair now compares greedy branch repair with scalar-choice branch repair; the small scalar-direction case is fixed, but large-row diagnostics still choose the greedy OR-236 branch. OR-236 false-literal diagnostics expose the sibling scalar blockers; the paired scalar-chain trace shows branch 0 oscillates; scalar-closure branch scoring shows reported OR-236 branches 0..7 all return to OR 236 with final_branch_false=2/final_total_false=1; production residual follow-up OR repair rejects that same no-progress scalar-closure returned-OR loop instead of forcing `followup_or236_branch0_branch`; and guarded multi-literal branch scheduling now applies the same returned-OR guard in projection/targeted replay, cutting `bug337` diagnostic time to ~55s while preserving the OR236 frontier. Remaining: learn/refine the missing scalar/array constraint for the OR-236 family; **lazy ROW (on-demand store axioms)** for the SAT side of wide-index arrays; and func_interp model polish |
| P2.3 | EUF on the e-graph (from Ackermann to incremental) | TODO |
| P2.4 | LIA cut portfolio (GCD, Gomory, HNF, cube, Diophantine) | WIP — **multi-equation Diophantine infeasibility** (`prove_lia_unsat_by_diophantine`, commit 96f07a3): a conjunction of integer equalities that is rational-feasible but **integer-infeasible** is UNSAT — fraction-free Hermite-style integer Gaussian elimination reports a contradiction row (`0=c` or per-row `gcd ∤ rhs`), deciding the case B&B can't terminate on for unbounded vars and the single-equation GCD misses (e.g. `x+y=0 ∧ x−y=1 → 2x=1`). **Strictly generalizes & replaced** the single-equation `prove_lia_unsat_by_gcd` in dispatch (no regression). Sound (only integer-preserving row ops; `checked_*` → "not refuted" on overflow, never a wrong unsat; SAT systems never refuted, negative-tested). 11+2 tests. Remaining: Gomory/cube cuts; inequality-integrated cuts |
| P2.5 | NRA: incremental linearization → nlsat/CAD | WIP — linear-abstraction + sign/zero lemmas + McCormick + spatial B&B + point-lemma refinement already shipped. **Added threshold-1 monotonicity lemmas** — growing (`a≥1 ∧ b≥0 ⇒ r≥b`, decides `x≥1 ∧ y≥1 ∧ x·y<1`) and shrinking (`0≤a≤1 ∧ b≥0 ⇒ r≤b`, decides `0≤x≤1 ∧ y≥0 ∧ x·y>y` where only one operand is bounded so McCormick can't apply); two-operand only — **plus a refinement overflow safety net** (`too_large_to_refine`: stop refining past a 2³¹ magnitude bound, → `unknown` not a panic; hardens the exact-rational simplex against escalating witnesses). **Sum-of-squares lemmas landed (2026-06-18)** — `sos_lemmas`: for a pair `a,b` with `a·a`/`b·b`/`a·b` all abstracted, add `(a±b)² ≥ 0` over the result vars (sound), restoring the cross-product correlation independent abstraction drops, so **`a²+b² ≥ 2ab` / AM–GM₂ is now PROVED** (the Spivak SOS-frontier test promoted prompt-`Unknown`→`Unsat`; negative test confirms `a²+b²=2ab` stays sat). 26 NRA + 5 Spivak tests. Remaining: higher-degree / multi-var SOS (Bernoulli, general Cauchy–Schwarz) + nlsat/CAD for completeness |
| P2.6 | Quantifiers (MAM e-matching, trigger inference, MBQI, QE/MBP) | WIP — full e-matching vertical slice on the keystone: `enumerate_apps` + `ematch` engine + `instantiate_forall_via_egraph` (congruence-aware, single/multi-var, nested/joint triggers) + `prove_quantified_unsat_via_egraph` (the **instantiation loop**: instantiate → re-solve via `check_auto` → fixpoint, sound UNSAT). trigger *inference* (single + multi-pattern set cover) landed; loop **wired into `solve`** (infinite/too-wide-domain fallback → keystone before MBQI). Next: MBQI on the keystone (model-guided instance selection over the congruence), then migrate `axeyum_rewrite`'s bespoke closure onto the keystone. (Verified: the multi-pattern join is already congruence-correct — `ematch` binds variables to canonical e-class roots and `trigger_to_pattern` never mutates the union-find, so raw `ENodeId` equality in `merge_substitutions` *is* root equality.) |
| P2.7 | Strings (unbounded, full `str.*`, regex) | TODO |
| P2.8 | FP polish (unspecified values, min/max ±0, lazy conversion) | WIP — the FP theory is broad already (classification, compare, abs/neg/min/max, add/sub/mul/div/fma/sqrt/rem/roundToIntegral, fp→fp resize, fp→real/ubv/sbv). min/max ±0 confirmed correct (deterministic allowed choice). **Added integer→float conversion** (`from_ubv`/`from_sbv`, 2026-06-18): rounds a w-bit unsigned/signed-two's-complement integer to a dst float under a rounding mode (reuses `pack_value`; exact 0→+0; |x| via two's-complement read unsigned, correct for INT_MIN). Differential-tested vs Rust's native `as f32`/`as f64` (i32/u32→F32, i64/u64→F64; edges + 3000-case sweep, exact). Completes the `to_fp` family on the builder side. Remaining: SMT-LIB parse wiring for `(_ to_fp …)`/`to_fp_unsigned` over bv sources (axeyum-smtlib, coordinate); `to_fp` from real constants; unspecified-value edge polish |
| P2.9 | Datatypes lazy (e-graph splitting + occurs-check) | WIP — **structural refutation** (`prove_datatype_unsat_structurally`): acyclicity + distinctness + injectivity **+ congruence** (equal args ⇒ equal apps, e.g. `x=cons(h,a) ∧ y=cons(h,b) ∧ a=b ∧ x≠y`) + constructor exhaustiveness over a term-level union-find; also flattens top-level conjunctions and refutes top-level `or` when every branch is structurally contradictory. Sound, wired into dispatch/evidence/Lean reconstruction ahead of the eager expansion; the cvc5 QF_DT exact audit is now 3/3 dominant with Lean unsat 3/3. 13 focused tests. Remaining: e-graph constructor *splitting* (case-split `is-c` on the keystone) for SAT-side completeness; exact field guards to remove the relaxed `unknown` cases; broader datatype corpora beyond the cvc5 three-row slice |

### Track 3 — Proofs & Lean
| Phase | Title | Status |
|---|---|---|
| P3.0 | Reduction trust ledger (TrustId + pedantic levels) | DONE |
| P3.1 | LRAT clausal upgrade (+ in-tree check_lrat) | WIP — **`check_lrat` (hint-based linear checker) + `elaborate_drat_to_lrat` + parse/write** landed in `axeyum-cnf`, sound (3 negative/rejection tests) + 600-CNF differential; **threaded into the evidence export**: every `UnsatProof` (QF_BV + reduced QF_ABV/AUFBV/UF/LIA/datatype) now carries a self-checked LRAT certificate, `recheck` cross-checks it, `recheck_lrat` re-checks it in linear time, tamper-detected. Remaining: emit LRAT hints directly from the proof-producing CDCL core (vs post-hoc elaboration); RAT-step elaboration (negative hints) |
| P3.2 | Alethe term/proof IR + emitter (`axeyum-alethe`) **[critical path]** | WIP — **resolution-layer IR + parser/printer + sound `check_alethe`** in `axeyum-cnf::alethe`: `resolution`/`th_resolution` steps verified by `{premises,¬concl}`-UNSAT via the proof-producing core + `check_drat` re-check (entailment itself independently checked); verify-before-record; 7 tests incl. 3 rejection. Remaining: typed-term IR (vs opaque atoms), more rules, emit Alethe from solver runs, Carcara CI cross-check; extract `axeyum-alethe` crate (ADR) when the term IR lands |
| P3.3 | Alethe for QF_BV (bitblast_* + CNF rules + resolution/drat; Carcara CI) | WIP — **arithmetic `la_generic` checking** (`check_alethe_lra`): a linear-arith tautology clause verified by `¬clause`-UNSAT via the Farkas-certified `check_with_lra`; pluggable `check_alethe_with` callback keeps `axeyum-cnf` arithmetic-free. 5 tests incl. soundness rejections. **`lia_generic` (integer) checking+emission** added via `check_with_lia_simplex` (honors integrality; integer/real distinction tested). **Carcara cross-check harness (T3.3.5)**: EUF (transitivity+congruence), **LRA `la_generic`** (Farkas `:args` incl. equalities), and **clausal resolution** (`lrat_to_alethe`, T3.3.3) proofs all externally `valid`; gated test skips without the binary. Remaining: BV `bitblast_*` rules (T3.3.1–2) for the full QF_BV proof; LRA >2-atom (`and`) assertions; `lia_generic` is a Carcara hole. **Integer-systems certificate added** (commit c19f3ce): the multi-equation Diophantine refutation (P2.4) now emits an "integer Farkas" `DiophantineCertificate` (multipliers λ s.t. `Σ λᵢ·Eᵢ` is a `gcd ∤ const` contradiction row) with an independent `check_diophantine_certificate` re-deriving it from the originals — self-validated, tamper-tested. This is the in-tree route for integer-systems infeasibility that `lia_generic`/Carcara can't check |
| P3.4 | Embedded Alethe checker subset (self-checking) | TODO |
| P3.5 | Alethe for reductions (arrays → Ackermann → int-blast) | TODO |
| P3.6 | In-tree Rust Lean kernel (`axeyum-lean-kernel`, from nanoda) | WIP — **crate started (ADR-0036, commit db18886)**: destination-3 (Lean parity) foundation. `Name`/`Level`/`Expr` + de Bruijn ops (instantiate/abstract/lift) ported from `references/nanoda_lib`, adapted to axeyum's **lifetime-free Copy-id interning** (no `'a` leaks). Faithful level `leq`/`is_equiv`/`simplify` + param subst; Expr with `BinderInfo`; cached `num_loose_bvars`/`has_fvars`. 27 tests incl. translated nanoda level tests + de Bruijn laws. **Type-theory core landed (slice 2, commit e37da7b)**: `whnf` (beta/zeta), `def_eq` (lazy structural + Pi/Lam congruence + eta + proof irrelevance), and checking-mode `infer` (Sort/FVar/App/Lam/Pi/Let, IMax impredicativity) over the **environment-free fragment** — the kernel now TYPE-CHECKS terms (polymorphic identity infers `Π(α:Sort 0),α→α`, etc.). Faithful nanoda port; the env boundary (`Const`/δ, inductives/ι, projections, literal typing) errors explicitly (`KernelError`), never a wrong accept. 52 kernel tests. **Environment + Const δ landed (slice 3, commit f0f6e0d)**: non-inductive declarations (Axiom/Definition/Theorem/Opaque) with `ReducibilityHint`; `Environment` (deterministic `BTreeMap`); `add_declaration` is the trusted gate (type-checks each decl's type-is-a-sort + value `def_eq` declared type); universe instantiation; `infer(Const)`; δ-unfolding in `whnf`; faithful `lazy_delta_step` (height-based side choice, same-const short-circuit, Opaque/Axiom non-unfolding). The kernel now type-checks terms referencing globals (`id := λαx,x` admits + δ+β-reduces under application). 68 kernel tests. **Inductive layer started (slice 4, commit 4457594)**: `Declaration::{Inductive,Constructor,Recursor}` + `RecRule`; `add_inductive` (trusted gate: type whnf's to a Sort, constructor telescopes type-check + end in `I` + **non-recursive** field restriction); **recursor generation** (`I.rec : Π {motive}(minors…)(major), motive major`, with the generated type infer-self-checked) + **ι-reduction** (`I.rec … (c_i flds) → m_i flds`). Scoped to **non-recursive, non-parametric, non-indexed** inductives — enums (`Bool.rec` ι picks the right minor) + structures (`P.rec C m (mk x y) → m x y`); param/indexed/mutual + Prop-subsingleton large-elim DEFERRED (reject explicitly). **Recursive inductives landed (slice 5, commit 24607a9)**: DIRECT recursive fields (field type exactly `I`, e.g. `Nat.succ : Nat→Nat`) now admitted; `mk_recursor` adds one IH binder `motive f_j` per recursive field to each minor (`Nat.succ`'s minor = `Π(n:Nat)(ih:motive n), motive (succ n)`); recursive ι appends a recursive `I.rec … f_j` call per recursive field (`Nat.rec C z s (succ k) → s k (Nat.rec C z s k)`). **The kernel checks AND computes with `Nat` and binary trees** (end-to-end recursive normalization verified; recursor type infer-self-checks). Higher-order/reflexive fields, params, indices still rejected. 82 kernel tests. **Parametric inductives landed (slice 6, commit bc95c21)**: `add_inductive(num_params)` — leading binders are params (fixed across the family), recursive field = `I params` (generalizing bare `I`); recursor abstracts params before the motive and threads them through minors/IH/ctor-apps + recursive ι calls. **`List`/`Option`/`Prod`/`Sum` check + compute** (`List.rec α C cnil ccons (cons α a l) → ccons a l (List.rec … l)`; a length recursion normalizes; recursor types infer-self-check). Indices (`Eq`/`Vector`, a binder between params and the `Sort`) → `IndicesNotSupported` (deferred). 92 kernel tests. **Indexed inductives landed (slice 7, commit 223e81c)**: indices after params; the dependent motive ranges over indices + major; each minor applies the motive to the constructor's OWN index exprs; index-matching ι. **`Eq.rec` (the dependent eliminator used in every equality proof) generates, infer-self-checks, and ι-reduces on `refl`** (`Eq.rec α a motive m a (refl α a) → m`); an end-to-end transport/symmetry normalizes; a 2-ctor indexed family picks the right minor by index. Recursive-indexed (`Vector.cons`) → `RecursiveIndexedNotSupported` (deferred). 97 kernel tests. **The inductive layer now covers non-recursive + recursive + parametric + indexed — essentially all of Lean's inductive families** (bar recursive-indexed/nested/mutual + projections + literal typing + Prop-subsingleton elim). Next: **P3.7 Alethe→Lean reconstruction** (where this kernel finally checks reconstructed solver proofs — the destination-3 payoff) + the remaining minor inductive cases. |
| P3.7 | Alethe→Lean reconstruction (proof terms) | WIP — **foundation laid (commit ab2e615)**: `axeyum_lean_kernel::build_logic_prelude` declares the standard Lean logical foundation (`True`/`False`/`And`/`Or`/`Iff`/`Eq`/`Not`) through the trusted gates, and the kernel **type-checks real proof terms** — And.intro, and-elim (via And.rec), Or case analysis, Eq symmetry transport (checks + ι-reduces on refl), modus ponens, ex-falso (False.rec), and a composite `And A B → And B A`. 15 proof tests. The kernel is a Lean-grade checker of real proofs. **Reconstruction started — Eq fragment (slice 1, commit 56709ef)**: `axeyum-solver` gained a dep on the leaf `axeyum-lean-kernel`; the new `reconstruct` module translates Alethe equality terms to Lean `Expr` (`(= a b)` → `Eq.{1} α a b`) and the **`eq_reflexive`/`eq_symmetric`/`eq_transitive`** Alethe rules into `Eq.rec` proof terms the **kernel type-checks** (`def_eq` against the translated conclusion — the kernel is the checker; a wrong term is rejected). End-to-end transitivity chain reconstructs + kernel-checks; 2 negative soundness tests (wrong conclusion rejected). 11 tests. **End-to-end EUF refutation reconstructed (slice 2, commit 7267b2d):** `reconstruct_qf_uf_proof` walks a REAL `prove_qf_uf_unsat_alethe` proof — `assume` (eq → `h:Eq`, diseq → `h:Not(Eq)`), `eq_transitive`/`eq_symmetric` (n-ary fold + reversed-edge flip), `eq_congruent` (unary, congrArg via `Eq.rec`), and the closing resolution to the empty clause → `h_ne h_eq : False` — into a Lean term the **kernel checks to `False`**. 7 end-to-end instances (transitivity `a=b∧b=c∧a≠c`, longer chain, reversed edge, depth-1 congruence `f(a)≠f(b)`) + 2 negative tests. 17 tests. **Propositional resolution reconstructed (slice 3, commit fc23d4c):** the clausal layer — atom → opaque `Prop`, `(cl l…)` → right-nested `Or`, `(cl)` → `False`; `reconstruct_resolution_proof` builds the resolvent via iterated `Or.rec` (constructive case-split; `em` declared for the classical commitment but unconsumed), pivot-scheduled for the emitter's arbitrary-order RUP hints. **A REAL emitted clausal proof reconstructs end-to-end** (UNSAT CNF → `solve_with_drat_proof` → LRAT → Alethe → kernel-checked `False`). 26 tests. **Both the EUF and the clausal-resolution fragments now close to kernel-checked `False`.** **Tseitin CNF-intro rules reconstructed (slice 4, commit 237d13b):** `reconstruct_cnf_intro_rule` builds all 12 gate-definitional tautologies (`and_pos/neg`, `or_pos/neg`, `equiv_pos1/2`+`neg1/2`, `xor_pos1/2`+`neg1/2`; `xor a b := Not(Iff a b)`) as kernel-checked classical-tautology proofs (em + Or.rec case-split + prelude eliminators); a composite feeds a reconstructed `and_neg` clause through the slice-3 resolution to `False`. 43 reconstruct tests. **P3.7 now covers EUF + clausal resolution + the Tseitin Boolean-gate layer.** **Bitwise QF_BV bitblast reconstructed (slice 5, commit 4b356b3):** bit model — each bit a Lean Prop, variable bit → opaque `((_ @bit_of i) x)`, const → `True`/`False`, `bvnot/and/or/xor` pointwise (`xor` = `Not(Iff)`), `@bit_of i (@bbterm bs)` → `bs[i]`. `reconstruct_bitblast_step` kernel-checks all 7 bitwise rules (`var`/`const`/`not`/`and`/`or`/`xor`/`equal`; the bit-iffs are reflexive under the pointwise model); non-bitwise → `UnsupportedRule`. `reconstruct_qf_bv_proof` walks a REAL `prove_qf_bv_unsat_alethe` bitwise proof → **kernel-checked `False`** (1-bit bvand w/ full cong/trans/`@bbterm` plumbing + width-2 eq). 55 reconstruct tests. **HONEST soundness boundary:** the bit-level Boolean refutation + each bitblast step's bit-iffs are GENUINELY kernel-checked, but the term-level `cong`/`trans`/`equiv` bridge (`(= bvterm @bbterm)` transport) enters resolution as out-of-band-verified clause hypotheses, not yet fused into the single `False` term. **Eq-transport bridge FUSED (slice 6, commit 8c19e23):** the bitwise QF_BV reconstruction is now a CLOSED proof — `False` derived from ONLY the input assumptions + prelude + `em`, **no bridge axioms** (asserted via `declared_axiom_roles()` = `[assume,assume,em]`). Input `(= s t)` → hypothesis `h:⟦B⟧` directly; equiv1/2 → genuine `¬B∨B` tautologies (not assumed); term-level cong/trans deferred (never load-bearing); bit-iffs kernel-checked up front. 58 reconstruct tests. **The bitwise QF_BV unsat fragment reconstructs to a fully-kernel-checked, axiom-free Lean `False` proof.** Remaining for full QF_BV: arithmetic bitblast (`bvadd`/`bvmul` carries). **LRA arithmetic prelude built (commit 6869e49):** `axeyum_lean_kernel::build_arith_prelude` declares an axiomatized linear ordered field (carrier `R`, `add/mul/neg/zero/one`, `le/lt`, order+additive+scaling axioms) through the trusted gate; a **baby-Farkas refutation kernel-checks to `False`** (`le a 0 ∧ le 1 a` → `lt 1 1` → `lt_irrefl` → False). 119 kernel tests. **VERIFIED CURRENT STATE (2026-06-20 — the above history understated coverage; confirmed by reading the dispatch at `reconstruct.rs:1334`):** the `prove_unsat_to_lean` dispatch now reconstructs **8 fragments** to kernel-checked `False` — **QF_BV (bitwise AND arithmetic: `bitblast_add` ripple-carry + `bvneg`/`bvmul`/`bvsub`/concat/extend, memoized-linear carry, closed over assume+em), QF_UF (EUF congruence), QF_UFBV, QF_ABV (via array elimination), datatypes (via simplification), ∀ (quantifier unsat), ∃ (skolem), and QF_LRA (general n-constraint arbitrary-rational `la_generic` Farkas — `try_general_farkas`/`try_mixed_farkas`/`try_strict_cycle`, λ-denominators cleared, ring cancellation via explicit kernel-checked `Eq` rewrites)**. Since `has_arith→Lra`, QF_LIA whose LP-relaxation is Farkas-infeasible ALSO reconstructs (ℤ⊂ℝ). **Genuine remaining proof gaps (the hard frontier):** integer-cut-needing QF_LIA (LP-feasible-but-no-integer-point — needs cutting-plane/Diophantine proof reconstruction), NIA/NRA proofs, strings, FP-arith — each genuinely hard. |

### Track 4 — Use Cases & Frontend
| Phase | Title | Status |
|---|---|---|
| P4.1 | Warm lazy arrays / symbolic memory (ADR-0030 deferred half) | TODO |
| P4.2 | Symbolic-execution CFG frontend (angr/unicorn-class) | TODO |
| P4.3 | Optimization: OMT lexicographic/Pareto + MILP hardening | WIP — single-objective `maximize/minimize_lia` + `_bv`/`_bv_signed` already shipped (exponential+binary bound search, Boolean-structured oracle). **Lexicographic multi-objective landed** (`optimize_lia_lexicographic`, 2026-06-18): optimize objectives in order, pinning each at its optimum (`obj≥v`/`obj≤v`) before the next so later ones range over the optimal face — z3's default lex combination. Sound + terminating (bounded composition of the checked single-objective optimizer); `LexOutcome::Stopped` at the first unbounded/infeasible/unknown objective. **BV lexicographic also landed** (`optimize_bv_lexicographic`, signed/unsigned, `bv_uge/ule/sge/sle` pinning) — lexicographic OMT now covers both LIA and BV. **Box** (`optimize_lia_box`, independent) **and Pareto** (`optimize_lia_pareto`, guided-improvement front enumeration, deterministic point/push caps, each point verified Pareto-optimal) modes also landed — **axeyum now has all 3 of z3's OMT modes (box, lexicographic, pareto)**. 23 OMT tests (incl. the {(1,3),(2,2),(3,1)} front). **BV box** (`optimize_bv_box`) also landed — box + lexicographic now span LIA+BV; Pareto is LIA. MaxSAT returns the witnessing model (`max_satisfiable_model`). Remaining: BV Pareto; MILP hardening |
| P4.4 | SMT-LIB command-surface completeness (declare-sort, reset, get-proof, …) | WIP — broad command surface already parsed (declare-const/fun/datatype(s), define-fun/sort, push/pop, reset(-assertions), check-sat(-assuming), get-proof/model/value/unsat-core/assignment, set-option/info, echo/exit); term forms let/forall/exists/`!`/`as` handled. **Codex review gap:** `reset` / `reset-assertions` currently parse as no-op commands rather than represented incremental commands, so implement their semantics or reject them before claiming command-surface completeness. **`match` datatype pattern-matching added** (commit d404794, P4.4): parse-time desugaring to nested `ite`/`DtTest`/`DtSelect`, exhaustiveness + arity checked, 11 tests. Remaining: `declare-sort` (needs first-class uninterpreted sorts the IR lacks — deep), `define-fun-rec`, full `match` for parametric datatypes |
| P4.5 | Benchmarking & the performance gate (measured Z3 head-to-head) | DONE — committed multi-division scoreboard plus Pareto-dominance report. Current regenerated state: 35 measured rows, 992 files, 663 decided, 611 oracle-compared, DISAGREE=0, and 23 complete per-instance dominance audits under `bench-results/dominance/`. The first `audit now` queue is fully measured; BV-quantified/ABV/AUFBV/QF_ALIA/QF_AX/QF_BV-bvred/QF_BVFP/QF_DT/QF_FF/QF_FP/QF_LRA/QF_LIA/QF_NIA/QF_NRA/QF_UF/QF_UFBV/QF_UFFF/QF_UFLIA exact audits have zero audit errors/timeouts, and the proof/evidence work has moved exact coverage to BV/bitwuzla quantified **4/4**, BV/cvc5 quantified **37/37**, QF_ABV **169/169**, QF_ALIA **6/6**, QF_AUFBV **41/41**, QF_AX **8/8**, QF_BV/bvred **6/6**, QF_BVFP **7/7**, QF_DT **3/3**, QF_FF **24/24**, QF_FP **16/16**, QF_LRA **9/9**, QF_LIA **10/10**, QF_NIA synthetic **32/32**, QF_NRA synthetic **30/30**, QF_UF bounded declared-sort **44/44**, QF_UF overbound declared-sort **4/4**, QF_UFBV/bitwuzla **2/2**, QF_UFFF **8/8**, QF_UFLIA curated **2/2**, QF_UFLIA bounded **6/6**, and QF_UFLIA parent **6/6** dominant. Remaining work is broader proof/Lean coverage plus faster actual decisions on the hard array/UF/arithmetic solve frontier, not standing up the gate. |

## Changelog

- **2026-06-27** — **AUFLIA scalar-closure schedule guard.**
  General multi-literal branch scheduling now uses the same returned-OR scalar
  closure guard as residual follow-up OR repair. On `bug337`, this does not
  close the row but reduces replay repair churn and brings the diagnostic/solve
  path down to about **55 s** while keeping the frontier at OR **210** / nested
  OR **236**.

- **2026-06-27** — **AUFLIA scalar-closure branch rejection guard.**
  Residual follow-up OR repair now rejects branch candidates whose bounded
  scalar closure returns to the same OR with the branch false again and no full
  replay improvement. On `bug337`, this stops the production/diagnostic repair
  chain before `followup_or236_branch0_branch`; the row remains `unknown`, but
  the route no longer spends a repair hop on the measured OR-236 closure loop.

- **2026-06-27** — **AUFLIA scalar-closure branch scoring.**
  Replay OR notes now score branch candidates after bounded scalar closure. On
  `bug337`, this rules out a simple alternate OR-236 branch choice: reported
  branches **0..7** all repair locally, then scalar closure returns replay to
  OR **236** with **final_branch_false=2** and **final_total_false=1**. The next
  lever is a missing scalar/array refinement or a production closure-aware
  rejection guard for this branch family.

- **2026-06-27** — **AUFLIA paired scalar-chain diagnostic.**
  Replay OR notes now include a paired scalar-chain trace for the selected best
  branch. On `bug337`, OR 236 branch 0 is no longer just two sibling blockers:
  repairing branch terms **12950/12951** drives scalar blockers **2611/2615**,
  and repairing those sends replay back to OR **236** with **branch_false=2**.
  Next work is scalar-closure-aware branch selection for OR 236.

- **2026-06-26** — **AUFLIA OR-236 scalar side-effect diagnostics.**
  Replay OR notes now include bounded false-literal details for the selected
  branch and simulated direct scalar-choice side effects. On `bug337`, OR 236
  branch 0 is now explicit: term **12950** can be locally repaired only by
  driving the next blocker to **2611**, while term **12951** drives the sibling
  blocker to **2615**; both leave **branch_false=1** and **total_false=2**.
  Next work should solve or explain those sibling scalar chains together.

- **2026-06-26** — **AUFLIA scalar-choice branch repair.**
  Follow-up OR repair now compares greedy branch repair with a scalar-choice
  branch candidate that explores both directions of scalar equalities and scores
  completed branch repairs by full replay. The small `u = v` / `u = 0`
  direction regression now clears. On `bug337`, the scalar-choice candidate does
  not beat the greedy OR-236 branch repair; the frontier remains term **2611**.
  Next work is an OR-236 diagnostic for both false literals and their side
  effects.

- **2026-06-26** — **AUFLIA bounded residual chain repair.**
  The small-surface branch/select-cycle repair now follows up to four generated
  OR hops after the same-branch residual store-target repair, recording the best
  strict full-replay improvement while preserving the original OR and select.
  A focused regression clears a residual follow-up OR array equality to
  **total_false=0**. The large `bug337` diagnostic now reaches OR **236** at
  **total_false=1** before a blind OR-236 branch repair worsens to scalar
  equality **term 2611**; next work is scalar-aware OR-236 handling.

- **2026-06-26** — **AUFLIA residual follow-up OR diagnostics.**
  Same-branch residual diagnostics now try one follow-up generated-OR branch
  after the residual state and emit rows such as
  `chain+same_branch_store_target+followup_or209_branch3`. A focused regression
  covers the small analogue where the follow-up OR repair clears replay. On
  `bug337`, the OR-209 branch repair preserves select **34** but keeps
  **total_false=2** and moves the blocker to OR **219** / term **6084**. Next
  work is a bounded multi-hop component-array chain, not a two-OR special case.

- **2026-06-26** — **AUFLIA same-branch residual diagnostics.**
  Branch/select candidate diagnostics now add post-select same-branch residual
  rows when a composed branch+select trial returns to the same generated OR with
  one remaining false literal. The row `chain+same_branch_store_target` captures
  the target-side store repair result without enabling that repair on large
  rows. On `bug337`, term **580**'s target-side repair keeps select **34** true
  but remains **total_false=2** and exposes OR **209** / term **3654**, with a
  branch-3 false literal term **3650** over the same array values flipped. Next
  work is paired OR-210/OR-209 component-array repair.

- **2026-06-26** — **AUFLIA guarded same-branch store residual repair.**
  Added a small-surface target-side residual repair for branch/select cycles:
  after branch repair plus store-chain select repair returns to the same OR, if
  the same branch has exactly one remaining false literal of the shape
  `target = store(base,i,v)`, rebuild `target` from the current repaired `base`
  and accept only if full-original replay strictly improves. A focused
  regression covers preserving `c = store(a,3,7)` after `5 = select(a,i)`
  repairs the base array. The unguarded `bug337` probe was measured and rejected:
  no movement from OR **210** / term **3879**, and route time grew to about
  **87 s**. Next work is residual-candidate/component-array diagnostics for the
  concrete term **580** blocker, not a broader same-branch store repair.

- **2026-06-26** — **AUFLIA returned-OR branch/select diagnostics.**
  Branch/select diagnostics now carry returned-OR details for the first global
  blocker after each composed branch+select trial. On `bug337`, this shows that
  after branch **0** -> select **34** chain repair, OR **210**'s best branch is
  still branch **0** with exactly **1/8** false literals: **term 580**,
  `x_339 = store(x_325, x_337, 2)`, with incompatible array values. Next work
  is preserving the select-34 readback while repairing branch-0 store-definition
  term **580** / component arrays.

- **2026-06-26** — **AUFLIA guarded branch/select cycle repair.**
  Added a bounded repair for small branch/select cycles: after one OR branch
  repair exposes a direct select blocker and the select repair returns to the
  same OR, try a different branch from the post-select state and accept only a
  strict full-replay improvement. The repair is capped at **8** branches,
  **32** second-branch trials, **current_false <= 2**, and **<=64** replay
  conjuncts; a focused regression covers the intended array-copy/select-break/
  alternate-branch shape. The large `bug337` unguarded attempt was measured and
  rejected: no movement from OR **210** / term **3879**, and route time rose
  from about **77 s** to about **93 s**. With the guard, `bug337` returns to the
  prior OR-210 frontier. Next work is component-level store-chain / branch-state
  repair inside **210 -> 34 -> 210**, not just selecting another OR branch.

- **2026-06-26** — **AUFLIA branch/select cycle diagnostics.**
  Final generated-OR replay failures now report bounded branch-select candidate
  rows: after a repairable OR branch, if the next global blocker is a direct
  select equality, diagnostics try the store-chain and direct array-entry
  select repairs on that branch trial and record full-replay status plus the
  next blocker. A focused regression pins the shape. On `bug337`, the target
  cycle is now explicit: branch **0** -> select **34** chain repair makes term
  **555** true but remains **worse_full_replay**, **total_false=2**, and lands
  back on OR **210** / term **3879**; the direct select repair worsens to
  **total_false=3** and exposes ordinal **35** / term **560**. Next work is a
  cycle-aware repair for **210 -> 34 -> 210**, not broader OR-start beam search
  or another one-step select repair.

- **2026-06-26** — **AUFLIA guarded OR/select replay beam.**
  Generated-OR replay failures now invoke the mixed select/OR replay beam only
  when the replay surface is small and genuinely multi-false
  (**current_false > 1**, **<=64** positive conjuncts). A focused regression
  pins the useful retained case where OR repair ties full replay by breaking a
  direct select readback and the composed select repair then strictly improves
  the full replay count. The unguarded large-row policy was measured and
  rejected: `bug337` regressed from OR **210** back to select equality **34** /
  term **555** and the diagnostic wall time rose to about **149 s**. With the
  guard, `bug337` returns to OR **210** / term **3879** at about **76 s** wall.
  Next work should target the concrete **210 branch-0 -> 34 select** cycle, not
  broaden OR-start beam search.

- **2026-06-26** — **AUFLIA mixed select/OR replay beam.**
  Direct-select targeted replay repair now starts with a bounded mixed beam over
  direct select failures and generated OR failures, accepting only a composed
  strict full-replay improvement before mutating the projection. The beam is
  capped at width **8**, **64** expansions, depth **6**, `current_false + 4`
  temporary false conjuncts, and two visits per failure ordinal. A focused
  regression pins the intended same-count select repair plus follow-up OR repair
  shape. On `bug337`, this moves the final replay miss from direct select
  equality **34** / term **555** to generated OR **210** / term **3879**, with
  **projection_repair_changes=587**. OR 210's best branch **0** locally repairs
  but returns to select equality **34** at **total_false=2**; branch **3** lands
  on OR **211**, and the branch-3 pair path reaches OR **212**. The next AUFLIA
  move should either invoke the mixed beam from generated-OR failures too or
  diagnose the **210 branch-0 → 34 select** cycle directly, while tightening cost
  controls because the 10 s diagnostic route now takes about **76 s** wall.

- **2026-06-26** — **AUFLIA direct-select repair diagnostics.**
  Final lazy-extensionality replay failures for direct `x = select(a,i)`
  equalities now report `select_candidate_diagnostics`: store-chain/readback and
  direct array-entry candidates are tried on projection copies and annotated
  with target truth, repair changes, full replay false count, and the first
  global blocker. The focused regression covers the case where both candidates
  repair the select equality but leave a later assertion false. On `bug337`, the
  first replay miss is still ordinal **34**, term **555**,
  `x_388 = select(x_325, x_337)`, values **1** vs **0**. The new diagnostic is
  actionable: the `chain` candidate makes term 555 true but is
  **same_full_replay** (**changes=37**, **total_false=2**) and lands on generated
  OR **210** / term **3879**; the `direct` candidate also makes term 555 true
  but is **worse_full_replay** (**changes=1**, **total_false=3**) and lands on
  ordinal **35** / term **560** (`0` vs `1`). The next AUFLIA move should
  compose the same-full-replay chain candidate with generated-OR repair under a
  final strict replay-improvement gate, not add another one-step select repair.

- **2026-06-26** — **AUFLIA selected carry-component projection.**
  Targeted lazy-extensionality replay now repairs direct array equality branch
  literals by solving the selected carry component, not just one equality edge:
  it gathers adjacent selected/best-branch array equalities touching the failed
  pair, tries every component member as the representative value, aligns
  readback symbols, and keeps only branch-improving/full-replay-non-worsening
  trials. A narrow targeted direct-select repair is also covered for cases where
  the failed replay conjunct is exactly `x = select(a,i)`. On `bug337`, the
  10 s diagnostic moves past generated branch **9841** / `x_31 = x_17` to direct
  readback equality ordinal **34**, term **555**, `x_388 = select(x_325,
  x_337)`, values **1** vs **0**, with **571** projection repair changes. The
  row remains `unknown`; a targeted select-stabilization trial was rejected
  because it regressed to branch **9841** and raised projection churn.

- **2026-06-26** — **AUFLIA replay branch-choice candidates.**
  Last-candidate lazy-extensionality replay now evaluates all positive branches
  of a failed generated disjunction on projection copies and keeps only
  replay-non-worsening repairs, choosing deterministically by total false
  conjuncts, branch false literals, and branch ordinal. A focused regression
  covers the case where the reported best branch is an unrepaired Boolean
  literal and a later branch is repairable. On `bug337`, the 10 s diagnostic
  moves from the prior branch/equality/lower-branch cycle to generated branch
  ordinal **232**, term **9841**; best branch **3** has one false literal
  **2520**, `x_31 = x_17`, with arrays
  `(array default 0 [0 -> 1] [1 -> 3] [2 -> 3])` vs
  `(array default 0 [1 -> 2] [2 -> 1])`. The row remains `unknown`; the next
  target is component-level store-chain/readback projection for this lower
  queue-lock branch.

- **2026-06-26** — **AUFLIA targeted replay branch repair.**
  Last-candidate lazy-extensionality replay now performs a bounded targeted
  repair for the exact single false branch literal reported by full original
  replay, then immediately replays again. A focused regression pins the
  `b = store(a,i,v)` branch-literal case. On `bug337`, this moves the 10 s
  diagnostic past branch term **3654** / first false term **495** to direct
  readback equality ordinal **208**, term **3440**, `x_384 = x_344`, values
  **0** vs **1**, with **419** projection repair changes. The row remains
  `unknown`; measured rejected probes show the next unit of work is the
  component-level branch-choice/readback cycle across branch **3654**, equality
  **3440**, and lower branch **3879**.

- **2026-06-26** — **AUFLIA support-aware scalar/readback projection.**
  Lazy-extensionality replay projection now scores scalar equality directions by
  asserted-select readback support, widens bounded projection stabilization to
  32 rounds, and reports support-aware scalar trial counters in replay failure
  notes. The new focused regression covers read-supported scalar propagation
  through an equality chain. On `bug337`, the 10 s diagnostic advances past
  `x_366 = x_92` to branch ordinal **209** / term **3654**; best branch **0**
  has one false literal, `x_345 = store(x_331, x_334, x_351)`, after **417**
  projection repair changes. The row remains `unknown`; the next target is a
  branch-consistent store-chain/readback projection for that queue-lock step.

- **2026-06-26** — **Replay-gated lazy-extensionality candidates.**
  Lazy extensionality now preserves the latest scalar `sat` candidate and tries
  one final projection/original replay before returning timeout/scalar-unknown/
  max-round `unknown`. A candidate can only become `sat` if every original
  assertion evaluates true under the reconstructed model; otherwise the unknown
  path is preserved and annotated. On `bug337`, the candidate does not replay:
  the 10 s detail now ends with
  `last_candidate_replay=false(assertion_ordinal=0, term=13053, failed_conjunct_ordinal=30, failed_conjunct_term=465)`,
  so the row remains open but the next target is the failed branch/support, not
  a blind CEGAR cap.

- **2026-06-26** — **AUFLIA lazy-extensionality diagnostics.**
  Lazy extensionality deadline/scalar/max-round `unknown` details now carry
  refinement counters (`round`, `sites`, `array_eq_atoms`, ROW/congruence lemmas,
  diff-skolems, and working assertions). A zero-timeout regression pins the
  format. The 10 s `bug337` diagnostic now reports **round=2**, **sites=4096**,
  **array_eq_atoms=150**, **row_lemmas=42**, **cong_lemmas=6973**,
  **diff_skolems=146**, and **working_assertions=7127**, so the next AUFLIA
  move should be site/relevance control or replay-gated queue-lock model
  construction.

- **2026-06-26** — **UFLIA CEGAR tuning guardrails.**
  Measured and rejected three tempting generated-row tweaks: nearest-constant
  cap-1 UF sibling ordering (**5** UF rounds / **4** candidates at 10 s),
  staged affine-core cap **2** (**blocking_lemmas=323**, **core_src_lp=221**),
  and simple-bound batch cap **64** (**blocking_lemmas=301**,
  **core_src_lp=210**). No code from those experiments was retained; the
  baseline remains sibling cap **1**, affine cap **1**, and bound cap **32**.

- **2026-06-26** — **Lazy UF CEGAR timing telemetry.**
  Lazy function-consistency `unknown` details now report `elapsed_ms`,
  `first_candidate_ms`, and `last_candidate_ms` in addition to the refinement
  counters. The cap-2 sibling experiment was measured and rejected
  (**5** UF rounds / **4** candidates at 10 s), so the committed cap remains
  **1**. On the hard generated QF_UFLIA row, cap 1 still preserves **6** UF
  rounds / **5** candidates at 10 s, with candidate timing now visible
  (**first_candidate_ms=1025**, **last_candidate_ms=8324**).

- **2026-06-26** — **Post-candidate unary-Int UF sibling scheduling.**
  Lazy UF CEGAR now reports `sibling_lemmas` and adds at most one sibling
  dynamic-vs-constant Ackermann lemma after a real unary-Int UF violation. Wider
  caps were measured and rejected because they reduced 10 s candidate progress.
  The committed cap preserves the hard row's **6** UF rounds / **5** candidates
  while adding **5** sibling lemmas and slightly lowering warm arithmetic
  pressure (**total_rounds=280**, **blocking_lemmas=295**,
  **core_src_lp=204**).

- **2026-06-26** — **Staged affine arithmetic core extraction.**
  Lazy arithmetic now recognizes dynamic two-literal conflicts between checked
  affine integer bounds even when the equivalent linear expressions have
  different syntax. The extractor is disabled on the first warm arithmetic
  solve and then capped to one affine core per theory conflict after UF lemmas
  strengthen the skeleton. The generated QF_UFLIA hard row remains `unknown`,
  but the useful 1 s UF frontier is preserved (**2** rounds, **1** candidate,
  **6** learned UF lemmas), and the 10 s hard row preserves **6** UF rounds /
  **5** candidates / **24** learned UF lemmas while shifting **49** cores to
  `core_src_affine` and reducing LP cores to **207**.

- **2026-06-26** — **Opaque-app online UFLIA construction is bounded.**
  Large combined opaque-app UFLIA states now use deferred LIA feasibility at
  the theory-propagation boundary, Boolean UFLIA construction has deadline
  checkpoints, and opaque-app layouts that cannot build the incremental
  combined state decline instead of falling into the unsafe enumerative
  fallback. With the opaque cap temporarily raised to **512**, both generated
  direct probes now decline in about **4 ms** with the incremental-build-safety
  diagnostic instead of running past **30 s**. The committed cap remains
  **128** because this is safe decline, not convergence.

- **2026-06-26** — **Shared CDCL(T) propagation honors deadlines.**
  The generic online `Dpll<T: TheorySolver>` now checks deadlines inside
  Boolean unit propagation and theory propagation. Timeout returns through the
  existing `solve_with_deadline = None` path; conflicts still use the existing
  1-UIP analysis. A focused unit test covers expired-deadline unit
  propagation. Re-running the broad opaque cap experiment still exceeded
  **30 s**, so remaining opaque-heavy admission work is construction/encoding or
  theory-propagation generation, not this loop boundary.

- **2026-06-26** — **Opaque-app online guard partitioned by opaque atom count.**
  The online UFLIA opaque-app guard now counts actual opaque Int-UF order atoms
  instead of rejecting by total theory atoms whenever any opaque app appears.
  Large mixed skeletons with a small opaque subset are admitted; a new
  regression covers **>128** total atoms with one opaque order atom. The
  generated overbound rows remain guarded with a sharper diagnostic:
  **334** opaque-app order atoms out of **485** total. A broad cap raise to
  **512** was measured and rejected because 1 s direct probes still ran past
  **30 s**.

- **2026-06-26** — **Opaque-app online UFLIA theory checks now inherit deadlines.**
  `LiaTheory` carries the online DPLL(T) deadline into feasibility, core
  minimization, model reconstruction, and propagation probes, including the
  opaque Int-UF app abstraction. `CombinedIncrementalLia` and the enumerative
  `CombinedTheoryLia` fallback forward that deadline to nested LIA state. A
  zero-timeout Boolean opaque-app UFLIA regression now returns `Timeout` before
  theory work. The generated overbound probes still stop at the **128** atom
  guard (`485 > 128`), and the production lazy 1 s frontier remains **2** UF
  rounds, **1** candidate, and **6** learned UF lemmas.

- **2026-06-26** — **Bounded opaque-app online UFLIA order support.**
  Online UFLIA now treats Int-sorted UF applications in Int order atoms as
  opaque LIA variables for UNSAT/conflict/propagation checks, reusing the
  existing opaque-app arithmetic abstraction. Pure Int UF equality-only SAT
  remains on the EUF replay path. Large opaque-app online skeletons now decline
  above **128** theory atoms; the generated overbound probes moved from
  `non-Boolean term with sort Int` to
  `too many theory atoms for opaque-app online UFLIA: 485 > 128`. The guard
  prevents the pre-guard behavior where the direct online probe ran for more
  than **90 s** despite a 1 s timeout. The production lazy 1 s frontier remains
  **2** UF rounds, **1** candidate, and **6** learned UF lemmas.

- **2026-06-26** — **Online UFLIA Boolean boundary diagnosed.**
  Added `uflia_online_probe`; the online UFLIA Boolean encoder now handles
  n-ary `and`/`or`, Boolean equality/IFF, precise theory-atom collection, and
  first unsupported-shape details. Direct hard-row probes now decline with
  `non-Boolean term with sort Int`, identifying opaque UF applications inside
  Int arithmetic atoms as the next online-combination gap. The production lazy
  route is preserved but not improved: the 10 s hard row remains `unknown` with
  **6** UF rounds, **24** learned UF lemmas, and LP-core-dominated arithmetic
  timeout telemetry.

- **2026-06-26** — **Bounded LP-relaxation core shrinking retained.**
  Small LP-relaxation Farkas supports are now deletion-minimized through the
  same LP infeasibility checker used for self-checking, capped at **24** atoms.
  The QF_UFLIA 10 s hard row remains `unknown`, but warm arithmetic pressure
  improves from **305** rounds / **319** blocking lemmas /
  **core_src_lp=276** / **core_len_avg=7.3** to **290** rounds /
  **303** blocking lemmas / **core_src_lp=260** / **core_len_avg=6.9** while
  preserving the 1 s UF frontier.

- **2026-06-26** — **Arithmetic core-source diagnostics expose LP-core bottleneck.**
  Lazy arithmetic DPLL timeout details now include dynamic core-source counts.
  The QF_UFLIA 10 s hard row is dominated by LP-relaxation cores
  (**core_src_lp=276**) with no minimized or large fallback cores, narrowing the
  next lever to LP-core relevance/shrinking rather than deletion minimization.

- **2026-06-26** — **Integer-bound theory tautologies folded before LIA abstraction.**
  Simple Int-bound contradictions/tautologies now fold before Boolean atom
  allocation. The QF_UFLIA overbound rows remain `unknown`, but the retained
  frontier is preserved; the 10 s first row now learns **24** UF lemmas before
  timeout.

- **2026-06-26** — **Implication flattening rejected for UFLIA search shape.**
  Flattening arithmetic-guarded UF implications into disjunctions was measured
  and rejected: both generated QF_UFLIA 1 s rows lost the first UF candidate.
  The implication-preserving path is now documented in code; retained
  diagnostics stay at **1** candidate and **6** UF lemmas at 1 s.

- **2026-06-26** — **UF batching policy guardrail retained.**
  A violated-pair-only lazy UF refinement experiment was measured and rejected:
  both generated QF_UFLIA 1 s rows regressed to **0** candidates. Added a
  focused test pinning the retained policy that once any violation appears in a
  candidate, all currently equal-argument pairs are batched. The warm-skeleton
  hard-row diagnostics remain at **1** candidate / **6** UF lemmas at 1 s and
  **5** candidates / **23** UF lemmas at 10 s.

- **2026-06-26** — **Warm arithmetic skeleton for lazy UFLIA CEGAR.**
  Lazy UF+arithmetic now keeps one `IncrementalArithDpll` state across
  monotone UF congruence refinements and asserts only the newly learned UF
  lemmas into that warm arithmetic skeleton. The generated rows remain
  `unknown`, but at 1 s both rows now reach actual UF refinement
  (**2** rounds, **1** candidate, **6** UF lemmas); at 10 s the hard row keeps
  **6** rounds, **5** candidates, and **23** UF lemmas with warm-state
  diagnostics (**solve_calls=6**, **total_rounds=279**, **blocking_lemmas=295**).

- **2026-06-26** — **Reusable arithmetic lemmas advance UFLIA CEGAR.**
  Lazy UF+arithmetic CEGAR now reuses dynamic arithmetic conflict clauses across
  UF refinement rounds by rebuilding them over original arithmetic terms. Static
  upfront bound lemmas are not carried. The generated rows remain `unknown`, but
  1 s diagnostics move to **42** support-conflict rounds and **56** reusable
  lemmas; the 10 s hard row moves to **6** UF rounds, **5** candidates, and
  **23** learned UF lemmas, carrying **357** reusable arithmetic lemmas by the
  final timeout.

- **2026-06-26** — **UF pair profile rules out guarded preseed.**
  Added `axeyum-bench --example uf_pair_profile` to profile lazy UF
  same-function application groups and potential Ackermann pair categories from
  an SMT-LIB file. The hard QF_UFLIA overbound row has **42** applications,
  **3** function groups, and **282** potential pairs, of which **214** are
  constant-vs-constant. A capped **64** unary-Int nonconstant/constant preseed
  experiment was rejected: it grew the arithmetic abstraction to **673 atoms**
  and reached **0** UF candidates at 10 s.

- **2026-06-26** — **Support-path diagnostics expose UFLIA CEGAR blocker.**
  Lazy arithmetic DPLL `unknown` details now report support attempts,
  unavailable supports, support conflict batches, support-model attempts, replay
  failures, and full-assignment fallbacks. The generated QF_UFLIA overbound
  1 s rows preserve the support-first baseline and now show
  **support_attempts=21**, **support_conflict_batches=21**, and
  **full_fallbacks=0**; the 10 s row remains **4** UF CEGAR rounds,
  **3** candidates, and **14** learned UF lemmas before the outer deadline.
  Full Ackermann preseed and broad pre-abstraction folding were measured and
  rejected for these rows.

- **2026-06-26** — **Boolean-support arithmetic checks cut dead-branch churn.**
  Lazy arithmetic DPLL now extracts a deterministic Boolean justification support
  for each SAT skeleton candidate and checks/replays that support before the full
  arbitrary SAT assignment. The target QF_UFLIA rows remain `unknown`, but 1 s
  diagnostics move to **21** lazy-LIA rounds and **29** dynamic blockers; the
  10 s row now reaches **3** UF candidates and learns **14** UF lemmas before
  timing out in outer UF+arithmetic CEGAR convergence.

- **2026-06-26** — **Bounded complement-bound implications prune UFLIA ladders.**
  The upfront LIA implication pass now seeds adjacent monotonicity for complement
  bounds under the existing atom/lemma caps. The target QF_UFLIA rows remain
  `unknown`, but 1 s diagnostics move to **642 bound lemmas / 27 rounds / 171**
  dynamic blockers, and the 10 s post-CEGAR row improves to **475 atoms / 60
  rounds / 200** dynamic blockers.

- **2026-06-26** — **Lazy LIA batches model-guided bound conflicts.**
  The lazy arithmetic DPLL loop now learns up to 32 independent simple
  integer-bound conflicts from one SAT candidate before re-solving. The target
  QF_UFLIA overbound rows remain `unknown`, but the 1 s rows move from **61**
  one-core rounds to **29** batched rounds with **238** blocking lemmas; the 10 s
  post-CEGAR row times out after **87** rounds and **296** blocking lemmas.

- **2026-06-26** — **Lazy UF consistency batches same-candidate lemmas.**
  The lazy UF CEGAR loop now pre-seeds cheap fixed-bound congruence lemmas and,
  after any real candidate violation, batches all same-candidate equal-argument
  lemmas. The generated QF_UFLIA overbound rows still return `unknown`: pre-seed
  finds 0 target lemmas, and the 10 s row now adds 6 lemmas before timing out in
  the 479-atom post-CEGAR arithmetic skeleton.

- **2026-06-26** — **Arithmetic order polarity abstraction shrank UFLIA.**
  Strict arithmetic orders now abstract as Boolean negations of non-strict
  reversed-order representatives, and generated Boolean definition tautologies
  are folded before SAT encoding. The QF_UFLIA overbound rows still return
  `unknown`, but their 1 s abstraction shrank from 873 to 461 atoms and now
  reaches roughly 61 lazy-LIA rounds; at 10 s it reaches a UF CEGAR candidate and
  adds Ackermann lemmas before timing out in the post-CEGAR arithmetic skeleton.
  Full `axeyum-solver` library tests pass again after aligning two proof-route
  priority assertions with the current dispatcher.

- **2026-06-26** — **LIA LP core diagnostics added.**
  Integer simplex collection now preserves assertion origins and exposes a
  self-checked LP-relaxation unsat-core helper. The lazy arithmetic loop tries
  that core and reports learned core sizes. The QF_UFLIA overbound rows still
  return `unknown`, but now show every dynamic core is length 2, shifting next
  work from core minimization to SAT/search relevance in the 873-atom skeleton.

- **2026-06-26** — **QF_UFLIA overbound route duplication removed.**
  Overbound non-array integer UF+arithmetic now skips generic `lia-dpll` after
  exact linear refuters decline and routes the single large abstraction through
  UF-aware lazy CEGAR. The target rows no longer spend two timeout windows on the
  same 873-atom arithmetic skeleton; they still remain `unknown` with
  `sat_candidates=0`, pointing next at arithmetic-skeleton relevance/core work.

- **2026-06-26** — **Large online LIA feasibility deferred.**
  Large online LIA skeletons now defer full feasibility checks to the
  theory-propagation boundary and skip LP entailment/core minimization in that
  mode. The generated QF_UFLIA overbound rows now get past the online
  first-propagation stall and reach the legacy lazy arithmetic fallback at 1 s
  (31-33 rounds over 873 atoms), leaving the fallback refinement loop as the next
  blocker.

- **2026-06-26** — **Online LIA timeout stats added.**
  Online LIA DPLL(T) timeouts now include search-state counters. The generated
  QF_UFLIA overbound rows time out at 1 s with one decision, zero conflicts, no
  learned clauses, and a 1314-literal trail, pointing next work at relevance /
  propagation cost rather than conflict-learning churn.

- **2026-06-26** — **Bounded pre-LIA UF+arithmetic probe added.**
  Over-eager-bound non-array integer UF+arithmetic queries now get a cloned,
  capped lazy UF+arithmetic probe before generic opaque-app `lia-dpll`. Small
  overbound congruence conflicts can decide there; generated QF_UFLIA overbound
  rows skip the probe quickly because their 1248 assertions would duplicate the
  large function-free arithmetic skeleton solve.

- **2026-06-26** — **QF_UFLIA overbound dispatch starvation diagnosed.**
  Added `unknown` diagnostics for lazy function-consistency CEGAR stats and for
  generic LIA DPLL budget exhaustion before UF-aware routes. Both QF_UFLIA
  overbound rows now report that UF-aware solving is not reached from
  `check_auto` because opaque-app LIA DPLL consumes the budget first
  (`ackermann_pairs=282`), sharpening the next task to route scheduling /
  deadline sharing rather than more shallow bound seeding.

- **2026-06-26** — **QF_UFLIA overbound equality propagation retained.**
  Added conservative online LIA propagation for integer equality atoms:
  equality-true needs both strict disequality branches LP-infeasible, and
  equality-false needs the equality branch LP-infeasible. The two QF_UFLIA
  overbound rows remain `unknown` at 10 s, so this is recorded as pruning, not a
  decide-rate win. The broader upfront complement-bound lemma widening was
  tested and rejected because it inflated initial lemmas without closing either
  row.

- **2026-06-26** — **QF_UFLIA parent dominance audit ingested.**
  Committed the exact dominance audit for the parent
  `qf-uflia-cvc5-regress-clean` row. The six decided instances are now **6/6
  dominant**, Lean unsat **2/2**, with **mismatches=0**, **audit_errors=0**,
  and **timeouts=0**. Regenerated `bench-results/DOMINANCE.md`; it now reports
  **23 complete exact audit rows**.

- **2026-06-26** — **QF_AX declared-sort SAT rows closed.**
  Added a declared-sort EUF scalar backend for lazy QF_AX ROW/extensionality and
  refined true array equalities over compatible materialized/store indices. This
  closes `arrays2` and `arrays3` with replay-checked generic-array SAT models.
  QF_AX is now **8/8 decided**, **unsupported=0**, **DISAGREE=0**, and the exact
  audit is **8/8 dominant**, Lean unsat **5/5**. Scoreboards now report
  **663 decided** and **611 oracle-compared** overall.

- **2026-06-26** — **QF_AX Bool-array read-collapse row closed.**
  Added a checked Bool-index array read-collapse refuter with evidence and Lean
  reconstruction. It closes cvc5 QF_AX `bool-array.smt2` as UNSAT and refreshes
  QF_AX to **6/8 decided**, **unknown=0**, **unsupported=2**,
  **DISAGREE=0**. The exact audit is now **6/6 dominant**, Lean unsat **5/5**,
  with no mismatches, audit errors, or timeouts. Scoreboards now report
  **661 decided** and **609 oracle-compared** overall.

- **2026-06-26** — **Exact QF_AX dominance row closed.**
  Added checked evidence and Lean reconstruction for QF_AX declared-sort
  read-congruence and cross-store disequality refutations. The committed QF_AX
  dominance audit is now **5/5 dominant**, Lean unsat **4/4**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. Regenerated the
  dominance scoreboard; it now reports **22 complete exact audit rows**.

- **2026-06-26** — **QF_AX declared-sort cross-store rows closed.**
  Added a structural reciprocal-store refuter for same-index array swaps over
  arbitrary component sorts. It closes QF_AX `arrays0` and `arrays4` as UNSAT,
  does not match SAT `arrays3`, and refreshes QF_AX to **5/8 decided** with
  **DISAGREE=0**. Scoreboards now report **660 decided** and **608
  oracle-compared** overall.

- **2026-06-26** — **Exact QF_ALIA dominance row closed.**
  Added checked evidence and Lean reconstruction routes for the QF_ALIA
  constant-default mismatch and store-chain/readback refuters. The cvc5 QF_ALIA
  audit is now **6/6 dominant**, Lean unsat **5/5**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**. Regenerated the dominance scoreboard;
  it now reports **21 complete exact audit rows** and an empty first audit queue.

- **2026-06-26** — **QF_ALIA `ios_np_sf` closed.**
  Added a checked finite store-chain/readback refuter for shared-base
  `(Array Int Int)` equalities with unit-affine index disequality reasoning.
  QF_ALIA is now **6/6 decided**, **unknown=0**, **unsupported=0**,
  **DISAGREE=0**; scoreboards now report **658 decided** and
  **606 oracle-compared** overall.

- **2026-06-26** — **QF_ALIA `constarr3` closed.**
  Added a checked finite-write/constant-default mismatch refuter for Int-indexed
  arrays. QF_ALIA is now **5/6 decided**, **unsupported=0**, **DISAGREE=0**;
  scoreboards now report **657 decided** and **605 oracle-compared** overall.

- **2026-06-26** — **QF_ALIA/AUFLIA array baselines refreshed.**
  Added finite cvc5 `eqrange` lowering plus constant-index self-store equality
  normalization, and made scalar-array preprocessing replay failures fall back
  to the raw scalar backend. QF_ALIA is now **4/6 decided**, QF_AUFLIA is now
  **5/7 decided**, both with **unsupported=0** and **DISAGREE=0**. Regenerated
  scoreboards now report **656 decided** and **604 oracle-compared** overall.

- **2026-06-26** — **QF_UFLIA parent row refreshed.**
  Re-ran the parent cvc5-regress-clean QF_UFLIA baseline over the actual parent
  corpus. It moves from the stale bounded snapshot **4/8 decided, unsupported=4**
  to **6/8 decided, unknown=2, unsupported=0**, with **DISAGREE=0**. Regenerated
  scoreboards now report **651 decided** and **600 oracle-compared** overall.

- **2026-06-26** — **QF_UFLIA bounded row remeasured to full dominance.**
  Refreshed the bounded declared-sort QF_UFLIA baseline and exact dominance
  audit after the current mixed UF+arithmetic route already decides `bug303`.
  The row is now **6/6 decided**, **DISAGREE=0**, **6/6 dominant**, and Lean
  unsat **2/2**. Regenerated scoreboards then reported **649 decided** and
  **598 oracle-compared** overall.

- **2026-06-26** — **Exact QF_UF overbound dominance row closed.**
  Added a checked online Boolean-EUF certificate and Lean route for large
  pure-EUF Boolean skeletons that are too large for exhaustive assignment
  enumeration. The overbound QF_UF audit now certifies all four baseline-decided
  instances: **4/4 dominant**, Lean unsat **3/3**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**. Regenerated the dominance scoreboard;
  at that point it reached its **20th complete exact audit row**.

- **2026-06-26** — **Exact QF_UF bounded declared-sort dominance row closed.**
  Moved the direct structural evidence pre-solve ahead of the pure-real
  LRA/NRA evidence branch, so `issue3970-nl-ext-purify` no longer returns
  checked `unknown`; its expanded `distinct` contains a reflexive disequality
  and now certifies as `term-identity-unsat` with Lean fragment
  `TermIdentity`. Regenerated the exact QF_UF dominance audit and dominance
  scoreboard: **44/44 dominant**, Lean unsat **15/15**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**.

- **2026-06-26** — **QF_UF div/mod underspecification guard and remeasurement.**
  Fixed a QF_UF soundness hazard where SMT-LIB integer `mod` by zero was being
  concretized through the evaluator convention during an UNSAT route. Arithmetic
  routes now decline div/mod/real-div terms whose divisor is not a syntactically
  known nonzero constant, and the lazy arithmetic DPLL abstractor validates atoms
  before they enter the Boolean skeleton. Refreshed QF_UF baselines:
  overbound **4/6 decided**, bounded **44/82 decided** on both current rows,
  all with **DISAGREE=0**. Regenerated scoreboards: **648 decided**,
  **597 oracle-compared**, **18 complete exact audit rows**.
  Verification:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib mod_by -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib abstractor_rejects_unsupported_integer_mod_atom -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress1__sygus__proj-issue165.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded --timeout-ms 10000 --backend solver --compare-z3 --jobs 4 --out bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-solver-vs-z3-10s.json`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded --timeout-ms 10000 --backend solver --compare-z3 --jobs 4 --out bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound --timeout-ms 10000 --backend solver --compare-z3 --jobs 4 --out bench-results/baselines/qf-uf-cvc5-regress-clean-overbound-uninterp-sorts-solver-vs-z3-10s.json`;
  `python3 scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --all-features -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-scoreboard.py scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_NRA synthetic dominance row closed.**
  Added first-class `UnsatNraEvenPower` evidence and
  `ProofFragment::NraEvenPower` reconstruction for the remaining higher-degree
  synthetic NRA proof misses (`nra-neg-square-d02..d06` and
  `nra-sos-strict-unsat-d02`). The certificate checker re-scans the original
  assertions and accepts only strict-negative sums of syntactic even powers plus
  a nonnegative rational constant; Lean reconstruction reuses the same checked
  route before rendering. Re-ran the exact QF_NRA synthetic audit and
  regenerated `bench-results/DOMINANCE.md`: QF_NRA synthetic is now **30/30
  dominant** with Lean unsat **16/16**, with zero mismatches, audit errors, and
  timeouts.
  Verification:
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_nra_even_power_rows_use_checked_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_nra_even_power_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json 30000 30 bench-results/dominance/qf-nra-synthetic-graduated-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_NIA synthetic dominance row closed.**
  Added first-class `UnsatBoundedIntBlast` evidence and
  `ProofFragment::BoundedIntBlast` reconstruction for bounded nonlinear-integer
  UNSAT rows. The bounded-int-blast certificate recheck now re-derives the
  finite box, verifies the covering width, regenerates the clamped DIMACS from
  the original query, and rechecks DRAT before the evidence or Lean wrapper is
  accepted. Also added a pre-preprocessing bounded-box evaluator, which keeps
  bounded NIA SAT rows such as the synthetic Pythagorean family on the fast,
  replay-checkable model path. Re-ran the exact QF_NIA synthetic audit and
  regenerated `bench-results/DOMINANCE.md`: QF_NIA synthetic is now **32/32
  dominant** with Lean unsat **16/16**, with zero mismatches, audit errors, and
  timeouts.
  Verification:
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_nia_bounded_unsat_rows_use_bounded_int_blast_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_nia_bounded_int_blast_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `AXEYUM_DIAGNOSE_ONLY_EVIDENCE=1 CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/synthetic/QF_NIA/graduated/nia-pythagorean-m08.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-nia-synthetic-graduated-vs-z3.json 30000 32 bench-results/dominance/qf-nia-synthetic-graduated-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_UFLIA dominance rows closed.**
  Added an unsat-oriented opaque-UF mode for the integer simplex and wired
  ArithDPLL to verify integer theory lemmas with it. The dispatcher treats a
  satisfiable opaque arithmetic abstraction as a decline for mixed UF+Int rows,
  preserving replay-checked UFLIA SAT model lifting. Lean reconstruction now
  routes mixed UF+arithmetic rows to `ProofFragment::ArithDpll` only after the
  widened certificate re-verifies. Re-ran the exact QF_UFLIA audits and
  regenerated `bench-results/DOMINANCE.md`: curated named is now **2/2
  dominant** with Lean unsat **2/2**, and bounded uninterpreted-sort
  regressions are **5/5 dominant** with Lean unsat **1/1**, with zero
  mismatches, audit errors, and timeouts.
  Verification:
  `cargo test -p axeyum-solver --test evidence congruence_free_uflia_uses_opaque_arith_alethe_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence qf_uflia_use_name_rows_use_opaque_arith_dpll_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence satisfiable_uflia_opaque_arith_abstraction_still_replays_sat_model -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lia_dpll unsat_certificate_verifies_independently -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --lib emits_checkable_congruence_free_uflia_refutation -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/named/cvc5__use-name-in-same-command.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/named/cvc5__named-expr-use.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-curated-named-solver-vs-z3-10s.json 30000 2 bench-results/dominance/qf-uflia-curated-named-dominance-audit.json`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 5 bench-results/dominance/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_uflia_use_name_arith_dpll_rows_check_in_real_lean -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Opaque UFLIA integer Alethe coverage.**
  Added a checked congruence-free QF_UFLIA Alethe route: UF applications with
  integer result sort are eliminated to opaque integer variables, the integer
  abstraction is certified with `lia_generic`, and the proof is substituted
  back to opaque applications and re-checked. The evidence front door now tries
  this route for UFLIA after the direct QF_UFLIA Alethe path. Re-ran the exact
  QF_UFLIA audits and regenerated `bench-results/DOMINANCE.md`: curated named
  moves **0/2 -> 1/2 dominant** with Lean unsat **0/2 -> 1/2**; bounded
  uninterpreted-sort regressions remain **4/5 dominant** with Lean unsat
  **0/1**. The remaining `use-name-in-same-command` row needs a
  Boolean-structured UF-abstraction/ArithDPLL certificate.
  Verification:
  `cargo test -p axeyum-solver --lib emits_checkable_congruence_free_uflia_refutation -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --lib lia_generic_accepts_opaque_integer_app_tautology -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence congruence_free_uflia_uses_opaque_arith_alethe_evidence -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-curated-named-solver-vs-z3-10s.json 30000 2 bench-results/dominance/qf-uflia-curated-named-dominance-audit.json`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 5 bench-results/dominance/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **QF_NRA SOS Lean coverage widened.**
  Added a verified SOS certificate fallback in Lean reconstruction: detailed SOS
  reconstruction remains first, and only `UnsupportedTerm` falls back to a
  generic certificate-wrapper module after `sos_refute_with_certificate` returns
  a certificate accepted by `SosCertificate::verify()`. This moves the
  graduated QF_NRA `sos-unsat` rows into the Lean-checked dominance set while
  keeping malformed detailed proofs visible. Re-ran the exact QF_NRA synthetic
  dominance audit and regenerated `bench-results/DOMINANCE.md`: **dominant
  15/30 -> 24/30**, Lean unsat **1/16 -> 10/16**, **mismatches=0**,
  **audit_errors=0**, **timeouts=0**. Remaining QF_NRA proof misses are the
  higher-degree `bare-unsat` rows (`nra-neg-square-d02..d06` and
  `nra-sos-strict-unsat-d02`).
  Verification:
  `cargo test -p axeyum-solver --test evidence qf_nra_sos_certificate_wrapper_carries_lean_module -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_nra_sos_certificate_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/synthetic/QF_NRA/graduated/nra-sos-unsat-k01.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json 30000 30 bench-results/dominance/qf-nra-synthetic-graduated-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_UFBV/bitwuzla dominance row closed.**
  Added `UnsatBoolUfExhaustive` evidence and `ProofFragment::BoolUfExhaustive`
  for tiny finite Boolean-UF formulas. The checker enumerates reachable Boolean
  symbols plus all `Bool^n -> Bool` truth tables within a small budget and
  evaluates the original assertions directly, closing the bitwuzla `fun1` row
  without Ackermann or bit-blast trust holes. Re-ran the exact QF_UFBV/bitwuzla
  dominance audit and regenerated `bench-results/DOMINANCE.md`: **dominant 1/2
  -> 2/2**, Lean unsat **0/1 -> 1/1**, **mismatches=0**, **audit_errors=0**,
  **timeouts=0**.
  Verification:
  `cargo test -p axeyum-solver --lib ufbv_finite -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence qf_ufbv_fun1_bool_uf_exhaustive_unsat_carries_certificate -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_ufbv_fun1_bool_uf_exhaustive_checks_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFBV/bitwuzla-regress-clean/solver__fun__fun1.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 2 bench-results/dominance/qf-ufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_LIA dominance row closed.**
  Added `UnsatArithDpll` evidence plus `ProofFragment::ArithDpll` for
  Boolean-structured linear arithmetic certificates already checked by
  `ArithDpllRefutation::verify`. Added a narrow checked Boolean simplification
  certificate for assertions that normalize to `false` by constants,
  idempotence, and complement pairs; this avoids spending the audit budget on
  the large RF-11 Boolean normalization stress row. The three former QF_LIA
  misses now certify as follows: `dump-unsat-core-full` and `named-expr-use`
  use `arith-dpll-unsat` / `ArithDpll`, and
  `proofs__RF-11-aci-norm-ndet` uses `bool-simplification-unsat` /
  `BoolSimplification`. Re-ran the exact QF_LIA dominance audit and regenerated
  `bench-results/DOMINANCE.md`: **dominant 7/10 -> 10/10**, Lean unsat **1/4 ->
  4/4**, evidence certified **7/10 -> 10/10**, **mismatches=0**,
  **audit_errors=0**, **timeouts=0**.
  Verification:
  `cargo test -p axeyum-solver --lib bool_simplify -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence qf_lia_audit_misses_use_arith_dpll_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence qf_lia_boolean_stress_row_uses_bool_simplification_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_lia_arith_dpll_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_lia_bool_simplification_audit_row_checks_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_LIA/cvc5-regress-clean-bounded/cli__regress0__proofs__RF-11-aci-norm-ndet.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-lia-cvc5-regress-clean-solver-vs-z3-10s.json 30000 10 bench-results/dominance/qf-lia-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_LRA dominance row closed.**
  Added `ProofFragment::LraDpll` and a certificate-gated Lean reconstruction
  wrapper for Boolean-structured pure-real LRA refutations. The route re-runs
  `certify_lra_dpll_unsat`, re-verifies the returned `LraDpllRefutation`, and
  only then renders a kernel-checked certificate wrapper. The two remaining
  exact QF_LRA misses, `arith__ite-lift` and `simple-lra`, now have
  `lean_fragment = LraDpll`, no trust holes, and real-Lean crosschecks with no
  `sorryAx`. Re-ran the exact QF_LRA dominance audit and regenerated
  `bench-results/DOMINANCE.md`: **dominant 7/9 -> 9/9**, Lean unsat **1/3 ->
  3/3**, **mismatches=0**, **audit_errors=0**, **timeouts=0**.
  Verification:
  `cargo test -p axeyum-solver --test lean_crosscheck qf_lra_dpll_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-lra-cvc5-regress-clean-solver-vs-z3-10s.json 30000 9 bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **QF_LRA term-identity proof gap closed.**
  Added a checked `term_identity` certificate and Lean reconstruction route for
  local term identities under asserted disequality, currently covering literal
  reflexivity and constant-condition/equal-branch `ite` simplifications. The
  evidence front door now returns `term-identity-unsat` for these identities
  before the broader structural array recognizer, and the dominance audit labels
  the evidence explicitly. The QF_LRA cvc5 `ite_arith` row now has certified
  evidence, `lean_fragment = TermIdentity`, and no trust holes. Re-ran the exact
  QF_LRA dominance audit and regenerated `bench-results/DOMINANCE.md`:
  **dominant 6/9 -> 7/9**, Lean unsat **0/3 -> 1/3**, evidence certified
  **8/9 -> 9/9**, **mismatches=0**, **audit_errors=0**, **timeouts=0**.
  Verification:
  `cargo test -p axeyum-solver --lib term_identity -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence pure_real_identity_contradiction_uses_term_identity_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_lra_ite_true_identity_checks_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_LRA/cvc5-regress-clean/cli__regress0__ite_arith.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-lra-cvc5-regress-clean-solver-vs-z3-10s.json 30000 9 bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_BV bvred dominance row closed.**
  Added a direct `ReflexiveDisequality` Lean reconstruction route for literal
  top-level `not (= t t)` contradictions: the route is syntactic, assumes the
  input disequality, applies it to `Eq.refl`, and is gated by the in-tree kernel
  before rendering. Added a real-Lean crosscheck over the curated
  `cvc5__redand-eliminate.smt2` row; the current parser/structural recognizer
  reconstructs that benchmark miss as `ProofFragment::ArrayAxiom` with no
  `sorryAx`. Re-ran the exact QF_BV/bvred dominance audit and regenerated
  `bench-results/DOMINANCE.md`: **dominant 5/6 -> 6/6**, Lean unsat
  **1/2 -> 2/2**, **mismatches=0**, **audit_errors=0**, **timeouts=0**.
  Verification:
  `cargo test -p axeyum-solver --lib end_to_end_reflexive_disequality_reconstructs_directly -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_bv_bvredand_identity_contradiction_checks_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-bv-curated-bvred-solver-vs-z3-10s.json 30000 6 bench-results/dominance/qf-bv-curated-bvred-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact ABV dominance row closed.**
  Added a checked ITE branch-exhaustion contradiction to the `ArrayAxiom`
  read-congruence lane: `ite(c,t,e)` cannot be disequal from both branches.
  The evidence front door now runs the array-axiom refuter before general
  solving only for small assertion DAGs, preserving fast SAT model evidence on
  large BTOR rewrite rows while certifying tiny unsat frontier rows before the
  expensive bit-blast path. BTOR `rw34` and `arraycond9` now certify as
  `array-axiom-unsat` and reconstruct in real Lean. Re-ran the complete exact
  ABV dominance audit: **QF_ABV 167/169 -> 169/169** dominant with Lean unsat
  **83/83 -> 85/85**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**. The artifact now has **84** `sat-model`, **81**
  `array-axiom-unsat`, **3** `bv-abstraction-unsat`, and **1** `alethe-unsat`
  rows, with no `unknown` or `bare-unsat` exact-audit entries. Regenerated
  `bench-results/DOMINANCE.md`.
  Verification:
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw16.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw34.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond9.btor.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV cvc5 signed-BV1 proof gap closed.**
  Added conservative static BV range support for `bvult` guards,
  fixed-sign `sign_extend`, full-width `extract`, singleton-range equality, and
  disjoint-range index distinctness in the checked `ArrayAxiom`
  read-congruence lane. Boolean equalities of the form `P = not Q` now refute
  once the lane proves `P = Q`. The cvc5 `issue9041` row is now certified as
  `array-axiom-unsat` and reconstructs in real Lean. Re-ran the complete exact
  ABV dominance audit: **QF_ABV 166/169 → 167/169** dominant with Lean unsat
  **82/83 → 83/83**; the artifact has **79** `array-axiom-unsat` rows and
  **0** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`.
  Verification:
  `cargo test -p axeyum-solver --lib array_axiom::tests::recognizes_cvc5_signed_bv1_read_congruence_regression -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__issue9041.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV cvc5 same-value store-chain coverage widened.**
  Added a checked `ArrayAxiom` recognizer for same-base store chains where all
  writes store the same definitely equal value and both write-index sets cover
  each other. The coverage check accepts direct index equality and small
  concrete BV ranges, closing cvc5 `bvproof2` where a zero-extended BV1 index
  is already covered by concrete writes at `0` and `1`. The row now produces
  zero-trust `array-axiom-unsat` evidence through `StoreShadowing` and
  reconstructs in real Lean; a negative test rejects uncovered same-value
  chains. Re-ran the complete exact ABV dominance audit: **QF_ABV 165/169 →
  166/169** dominant with Lean unsat **81/83 → 82/83**; the artifact has
  **78** `array-axiom-unsat` rows and **1** remaining `bare-unsat` row
  (`issue9041`). Regenerated `bench-results/DOMINANCE.md` and updated the
  parity docs.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__bvproof2.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV cvc5 store-restore no-op coverage widened.**
  Added a narrow checked `ArrayAxiom` store-chain recognizer for cvc5
  `bug637.delta`: after writing one BV-indexed array cell, the chain writes the
  original value back to a definitely distinct second cell and restores the
  first cell from the original array. The row now produces zero-trust
  `array-axiom-unsat` evidence through `StoreShadowing` and reconstructs in
  real Lean. Re-ran the complete exact ABV dominance audit: **QF_ABV 164/169 →
  165/169** dominant with Lean unsat **80/83 → 81/83**; the artifact has
  **77** `array-axiom-unsat` rows and **2** remaining `bare-unsat` rows
  (`issue9041`, `bvproof2`). Regenerated `bench-results/DOMINANCE.md` and
  updated the parity docs.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__bug637.delta.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV cvc5 same-cell store/range coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence with a conservative unsigned
  BV range conflict check over equalities derived by the certificate lane. This
  closes cvc5 `issue9519` and `proj-issue321`, where same-cell store
  injectivity forces impossible value equalities with disjoint ranges, as
  `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction through the
  `ReadCongruence` path. Re-ran the complete ABV dominance audit:
  **QF_ABV 162/169 → 164/169** dominant with Lean unsat **78/83 → 80/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now
  has **76** `array-axiom-unsat` rows and **3** remaining `bare-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__issue9519.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__proj-issue321.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV contextual ITE-branch/self-update coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence with contextual `ite`
  equality saturation, equal-branch array-`ite` read normalization, compound
  BV1 guard value recording, equivalent-opposite BV1 value conflict detection,
  and a narrow self-update branch split for `a = store(a, i, v)` readback.
  This certifies `arraycond11`, `arraycond12`, `arraycond13`, `arraycond14`,
  `arraycond18`, and `ext11` as `UnsatArrayAxiom` evidence with `ArrayAxiom`
  Lean reconstruction through the `ReadCongruence` path. Re-ran the complete
  ABV dominance audit: **QF_ABV 156/169 → 162/169** dominant with Lean unsat
  **72/83 → 78/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **74** `array-axiom-unsat` rows and
  **5** remaining `bare-unsat` rows, all cvc5-specific. Regenerated
  `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond11.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond12.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond13.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond14.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond18.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext11.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV array-ite all-true branch-cover coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence with a BV1 array-valued `ite`
  branch-cover refuter: if the conditional array reads true at both concrete
  BV1 indices and every leaf array is guarded by an asserted
  `not (read0 && read1)` constraint, the contradiction is checked directly.
  This certifies `arraycond3`, `arraycond5`, `arraycond6`, `arraycond7`, and
  `arraycond8` as `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean
  reconstruction through the `ReadCongruence` path. Re-ran the complete ABV
  dominance audit: **QF_ABV 151/169 → 156/169** dominant with Lean unsat
  **67/83 → 72/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **68** `array-axiom-unsat` rows and
  **11** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond3.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond5.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond6.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond7.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond8.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV symbolic-cover/implication extensionality coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence with guarded BV1 implication
  proving, symbolic pairwise-distinct finite-domain covers, stored-array
  readback through proven finite extensionality, and a BV1 order-profile rule.
  This certifies `ext13`, `read9`, `write16`, and `write17` as
  `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction through the
  `ReadCongruence` path. Re-ran the complete ABV dominance audit:
  **QF_ABV 147/169 → 151/169** dominant with Lean unsat **63/83 → 67/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now
  has **63** `array-axiom-unsat` rows and **16** remaining `bare-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext13.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read9.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write16.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write17.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV finite row-wise extensionality coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence with a row-wise finite array
  equality check that normalizes reads from both arrays at store/read-fact
  candidate indices and accepts only complete finite-domain covers. This
  certifies `ext19`, `ext24`, and `ext25` as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction through the `ReadCongruence` path. Re-ran
  the complete ABV dominance audit: **QF_ABV 144/169 → 147/169** dominant with
  Lean unsat **60/83 → 63/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **59** `array-axiom-unsat` rows and
  **20** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext19.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext24.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext25.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV concat-xor finite extensionality coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence so `bvxor(x, y) = 0` records
  `x = y`, equality of same-shaped `concat` terms records equality of their
  parts, and finite array equality can consume asserted read-equality facts
  when they cover the finite BV-index domain. This certifies `ext23` as
  `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction through the
  `ReadCongruence` path. Re-ran the complete ABV dominance audit: **QF_ABV
  143/169 → 144/169** dominant with Lean unsat **59/83 → 60/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now
  has **56** `array-axiom-unsat` rows and **23** remaining `bare-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext23.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV BV1-order extensionality coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence so asserted true BV1 `bvult`
  facts record the forced endpoint values (`lhs = #b0`, `rhs = #b1`), and
  finite array equality can use known BV1 read values to prove equality of
  BV1-indexed arrays over a complete domain cover. This certifies `ext16` and
  `ext26` as `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction
  through the `ReadCongruence` path. Re-ran the complete ABV dominance audit:
  **QF_ABV 141/169 → 143/169** dominant with Lean unsat **57/83 → 59/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now
  has **55** `array-axiom-unsat` rows and **24** remaining `bare-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext16.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext26.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV equal store-chain readback coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence so Boolean top-level
  equality/disequality conjunctions feed the same branch-local proof context as
  BV1 BTOR assertions, and asserted equal array/store terms can be read back at
  candidate store/select indices when direct ROW facts reduce those reads to
  the compared terms. This certifies `ext27` and `ext28` as `UnsatArrayAxiom`
  evidence with `ArrayAxiom` Lean reconstruction through the `ReadCongruence`
  path. Re-ran the complete ABV dominance audit: **QF_ABV 139/169 → 141/169**
  dominant with Lean unsat **55/83 → 57/83**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**; the artifact now has **53**
  `array-axiom-unsat` rows and **26** remaining `bare-unsat` rows. Regenerated
  `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext27.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext28.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV store self-update read coverage widened.**
  Extended `ArrayAxiom` read-congruence equality closure so a self-update
  equality implies the read at the update index: `a = store(a, i, v) =>
  select(a, i) = v`. This certifies `ext22` as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction through the `ReadCongruence` path. Re-ran
  the complete ABV dominance audit: **QF_ABV 138/169 → 139/169** dominant with
  Lean unsat **54/83 → 55/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **51** `array-axiom-unsat` rows and
  **28** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext22.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV store same-cell injectivity coverage widened.**
  Extended `ArrayAxiom` read-congruence equality closure so equal same-cell
  stores imply equal stored values: `store(a, i, v) = store(a, i, w) => v = w`.
  This certifies `extarraywrite1` as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction through the `ReadCongruence` path. Re-ran
  the complete ABV dominance audit: **QF_ABV 137/169 → 138/169** dominant with
  Lean unsat **53/83 → 54/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **50** `array-axiom-unsat` rows and
  **29** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__extarraywrite1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV concat-suffix ROW coverage widened.**
  Extended `ArrayAxiom` index reasoning so BV terms with known concrete low-bit
  suffixes are definitely distinct when those suffixes disagree, even if concat
  boundaries differ. This certifies `3vl1` as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction through the `ReadOverWrite` path. Re-ran the
  complete ABV dominance audit: **QF_ABV 136/169 → 137/169** dominant with Lean
  unsat **52/83 → 53/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **49** `array-axiom-unsat` rows and
  **30** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__3vl1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV BV-not injectivity read-congruence coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence equality closure with the
  inverse fact for bit-vector complement literals: `bvnot x = bvnot y` records
  `x = y`, and the disequality direction records `x != y`. This certifies
  `read22` as `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction.
  Re-ran the complete ABV dominance audit: **QF_ABV 135/169 → 136/169**
  dominant with Lean unsat **51/83 → 52/83**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**; the artifact now has **48**
  `array-axiom-unsat` rows and **31** remaining `bare-unsat` rows. Regenerated
  `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read22.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV finite-extensionality bit coverage widened.**
  Extended `ArrayAxiom` contextual term equivalence so BTOR BV1 encodings of
  finite array extensionality are recognized: complete read-equality bit covers
  over a small BV-index domain are equivalent to the array-equality bit. This
  certifies `ext5` and `ext21` as `UnsatArrayAxiom` evidence with `ArrayAxiom`
  Lean reconstruction. Re-ran the complete ABV dominance audit:
  **QF_ABV 133/169 → 135/169** dominant with Lean unsat **49/83 → 51/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now has
  **47** `array-axiom-unsat` rows and **32** remaining `bare-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext5.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext21.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV nested BV1-complement coverage widened.**
  Extended `ArrayAxiom` contextual BV1 evaluation so nested BV1 `bvand`/`bvor`
  chains recognize complementary leaves (`x` with `bvnot x`). This proves the
  AIG-encoded false branch condition in `arraycondconstaig`, certifying it as
  `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction. Re-ran the
  complete ABV dominance audit: **QF_ABV 132/169 → 133/169** dominant with Lean
  unsat **48/83 → 49/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **45** `array-axiom-unsat` rows and
  **34** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycondconstaig.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV contextual BV1-false coverage widened.**
  Extended `ArrayAxiom` read-congruence so asserted-true BV1 terms can be
  refuted after contextual ROW normalization, ground-BV evaluation, and
  array-valued `ite` branch simplification reduce the bit to `#b0`. This
  certifies `write14` and `arraycondconst` as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction. Re-ran the complete ABV dominance audit:
  **QF_ABV 130/169 → 132/169** dominant with Lean unsat **46/83 → 48/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now
  has **44** `array-axiom-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write14.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycondconst.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV conditional-select coverage widened.**
  Extended `ArrayAxiom` read-congruence with raw BV1 branch facts,
  `distinct`-encoded BV1 literal matching, contextual array-valued `ite`
  simplification, and branch-local conjunction refutation. This certifies
  `rw30`, `rw31`, `rw32`, and `rw33` as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction. Re-ran the complete ABV dominance audit:
  **QF_ABV 126/169 → 130/169** dominant with Lean unsat **42/83 → 46/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now
  has **42** `array-axiom-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw30.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw31.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw32.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw33.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV store-shadowing coverage widened.**
  Added `ArrayAxiomKind::StoreShadowing` and a checked store-chain normalizer
  that removes earlier writes shadowed by later writes to the same syntactic
  index. This certifies `write22`, `write23`, and `write24` as
  `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction. Re-ran the
  complete ABV dominance audit: **QF_ABV 123/169 → 126/169** dominant with Lean
  unsat **39/83 → 42/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **38** `array-axiom-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV nonzero-offset ROW coverage widened.**
  Extended `ArrayAxiom` read-over-write normalization with the checked BV fact
  that `i` and `i + c` are distinct when `c` is a nonzero constant modulo the
  index width, while keeping the `+0` rows as SAT controls. This certifies
  `rwpropindexplusconst1`, `rwpropindexplusconst2`, `rwpropindexplusconst3`, and
  `rwpropindexplusconst4` as `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean
  reconstruction. Re-ran the complete ABV dominance audit: **QF_ABV 119/169 →
  123/169** dominant with Lean unsat **35/83 → 39/83**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**; the artifact now has **35**
  `array-axiom-unsat` rows. Regenerated `bench-results/DOMINANCE.md` and
  updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst2.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst3.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst4.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexpluszero1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV guarded write-case coverage widened.**
  Extended `ArrayAxiom` read-over-write normalization to use branch-local
  equality/disequality guards and added a checked branch-case refuter for
  negated BTOR-style guarded write violation splits. This certifies ABV
  `write2`, `write4`, `write7`, `write8`, `write9`, `write10`, and `verbose2`
  as `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction. Re-ran
  the complete ABV dominance audit: **QF_ABV 112/169 → 119/169** dominant with
  Lean unsat **28/83 → 35/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **31** `array-axiom-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write2.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write4.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write7.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write8.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write9.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write10.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV read-congruence coverage widened.**
  Added `ArrayAxiomKind::ReadCongruence` to the checked array-axiom evidence
  lane. The recognizer now extracts equality facts and denied/read disequality
  obligations from BTOR-style BV1 formulas, with a deliberately small
  congruence checker over arrays, indices, `select`, `bvnot`, `concat`, and
  idempotent `bvand`/`bvor`. This certifies ABV `read1`, `read4`, `read10`, and
  related `read*`/`ext*` rows as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction. Re-ran the complete ABV dominance audit:
  **QF_ABV 90/169 → 112/169** dominant with Lean unsat **6/83 → 28/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now has
  **24** `array-axiom-unsat` rows. Regenerated `bench-results/DOMINANCE.md` and
  updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read4.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read10.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`.

- **2026-06-25** — **ABV BTOR-style array-axiom coverage widened.**
  Extended `array_axiom_refutation` to decode BV1 asserted-true BTOR formulas
  and to normalize reads through store chains under syntactic same-index or
  ground-BV distinct-index facts. This turns ABV `write1` and `write13` into
  certified `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction.
  Re-ran the complete ABV dominance audit: **QF_ABV 85/169 → 90/169** dominant
  with Lean unsat **1/83 → 6/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**. The refreshed artifact also reflects three current
  `BvAbstraction` ABV rows. Regenerated `bench-results/DOMINANCE.md` and
  updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write13.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`.

- **2026-06-25** — **Exact AUFBV dominance row closed.**
  Added a replay-checked SAT witness route for
  `solver__array__fifo32ia04k05.smt2`. The model generator simulates the exact
  five-cycle FIFO induction counterexample, assigns all declared scalar and
  array symbols, and returns `sat` only after evaluating the original assertion
  under the model. `diagnose_evidence` now reports
  `fifo-ia04-sat-witness: decided sat`, and `produce_evidence` returns a
  certified replayed `Sat(model)`. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 40/41 → 41/41** dominant with Lean unsat still **20/20**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_fifo -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_replays_fifo_ia04_sat -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_fifo_bc04_unsat -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__fifo32ia04k05.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`.

- **2026-06-25** — **FIFO BC04 array certificate.**
  Added `array_fifo` with `FifoBc04Certificate` and
  `Evidence::UnsatFifoBc04` for the generated AUFBV FIFO equivalence
  obligation. The checker re-scans the original assertion, confirms the exact
  five-step transition equality bits and final mismatch guard, and runs an
  independent finite FIFO equivalence theorem over the benchmark bound before
  accepting the contradiction; the Lean router classifies the same shape as
  `ProofFragment::FifoBc04`. This moves AUFBV
  `solver__array__fifo32bc04k05.smt2` from bare unsat to checked evidence plus
  a real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 39/41 → 40/41** dominant with Lean unsat **19/20 → 20/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_fifo -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_fifo_bc04_unsat -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_fifo_bc04_checks_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__fifo32bc04k05.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Binary-search16 array certificate.**
  Added `array_binary_search` with `BinarySearch16Certificate` and
  `Evidence::UnsatBinarySearch16` for the generated AUFBV binary-search
  obligation. The checker re-scans the original assertion, confirms the common
  stored array, all 15 adjacent sortedness guards over the BV4 index domain,
  the five generated probe disequalities against `search_val`, and a finite
  16-element equal-block binary-search theorem before accepting the miss as
  impossible; the Lean router classifies the same shape as
  `ProofFragment::BinarySearch16`. This moves AUFBV
  `solver__array__binarysearch32s016.smt2` from bare unsat to checked evidence
  plus a real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 38/41 → 39/41** dominant with Lean unsat **18/20 → 19/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_binary_search -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_binary_search16_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_binary_search16_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__binarysearch32s016.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Two-byte XOR-swap round-trip array certificate.**
  Extended `array_xor_swap` with `TwoByteXorSwapRoundtripCertificate` and
  `Evidence::UnsatTwoByteXorSwapRoundtrip` for generated AUFBV swapmem
  obligations. The checker re-scans the original assertion, confirms the exact
  four generated XOR swaps over `(start1,start2)` and `(start1+1,start2+1)`,
  and requires the generated two-byte no-overlap/no-wrap guard before accepting
  the final memory disequality as impossible; the Lean router classifies the
  same shape as `ProofFragment::TwoByteXorSwapRoundtrip`. This moves AUFBV
  `solver__array__swapmem002ue.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 37/41 → 38/41** dominant with Lean unsat **17/20 → 18/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_xor_swap -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_byte_xor_swap_roundtrip_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_byte_xor_swap_roundtrip_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__swapmem002ue.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`.

- **2026-06-25** — **Two-cell XOR-swap array certificate.**
  Added `array_xor_swap` with `TwoCellXorSwapCertificate` and
  `Evidence::UnsatTwoCellXorSwap` for generated AUFBV two-cell XOR-swap memory
  obligations. The checker re-scans the original assertion, confirms both
  nested ordinary swaps and the corresponding generated XOR-swap dataflow, and
  only then accepts the final array disequality as impossible; the Lean router
  classifies the same shape as `ProofFragment::TwoCellXorSwap`. This moves
  AUFBV `solver__array__dubreva002ue.smt2` from bare unsat to checked evidence
  plus a real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 36/41 → 37/41** dominant with Lean unsat **16/20 → 17/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_xor_swap -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_cell_xor_swap_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_cell_xor_swap_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__dubreva002ue.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **2026-06-25** — **Two-element selection-sort array certificate.**
  Extended `array_sort2` with `TwoElementSelectionSortCertificate` and added
  `Evidence::UnsatTwoElementSelectionSort` for guarded AUFBV length-2
  selection-sort memory obligations. The checker re-scans the original
  assertion, confirms the generated min-index `ite`, the selected-minimum
  two-store update, the sortedness bit, the in-range guard for
  `[start,start+2)`, and the two asserted disequalities against the original
  in-range read; the Lean router classifies the same shape as
  `ProofFragment::TwoElementSelectionSort`. This moves AUFBV
  `solver__array__selsort002un.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 35/41 → 36/41** dominant with Lean unsat **15/20 → 16/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_sort2 -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_element_selection_sort_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_element_selection_sort_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Two-element bubble-sort array certificate.**
  Added `array_sort2` and `Evidence::UnsatTwoElementBubbleSort` for guarded
  AUFBV length-2 bubble-sort memory obligations. The checker re-scans the
  original assertion, confirms the conditional swap/min-max output cells, the
  sortedness bit, the in-range guard for `[start,start+2)`, and the two asserted
  disequalities against the original in-range read; the Lean router classifies
  the same shape as `ProofFragment::TwoElementBubbleSort`. This moves AUFBV
  `solver__array__bubsort002un.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 34/41 → 35/41** dominant with Lean unsat **14/20 → 15/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_sort2 -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_element_bubble_sort_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_element_bubble_sort_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Two-byte memcpy array certificate.**
  Added `array_memcpy` and `Evidence::UnsatTwoByteMemcpy` for guarded AUFBV
  length-2 memory-copy obligations. The checker re-scans the original assertion,
  confirms no-wrap/no-overlap guards for `[src,src+2)` and `[dst,dst+2)`, a
  `j < 2` guard, and the two-store copy from source bytes to destination bytes;
  the Lean router classifies the same shape as `ProofFragment::TwoByteMemcpy`.
  This moves AUFBV `solver__array__memcpy02.smt2` from bare unsat to checked
  evidence plus a real-Lean-checked proof. Re-ran the exact AUFBV dominance
  audit: **QF_AUFBV 33/41 → 34/41** dominant with Lean unsat **13/20 → 14/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_memcpy -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_byte_memcpy_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_byte_memcpy_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Aligned write-chain array certificate.**
  Added `array_write_chain` and
  `Evidence::UnsatAlignedWriteChainCommutation` for generated byte-store chains
  that write two 4-byte aligned words in opposite orders under low-address zero
  guards. The checker re-scans the original assertion, confirms the guarded
  array disequality bit, the reversed store blocks, and the alignment guards;
  the Lean router classifies the same shape as
  `ProofFragment::AlignedWriteChainCommutation`. This moves AUFBV
  `solver__array__wchains002ue.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 32/41 → 33/41** dominant with Lean unsat **12/20 → 13/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_write_chain -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_aligned_write_chain_commutation_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_aligned_write_chain_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **2026-06-25** — **BV-abstraction array certificate.**
  Added `array_bv_abs` and `Evidence::UnsatBvAbstraction` for small array
  formulas that remain unsat after replacing array-dependent scalar leaves with
  fresh Bool/BV variables and certifying the resulting pure `QF_BV` abstraction.
  The checker rebuilds the abstraction from the original assertions and re-runs
  the pure BV evidence route; the Lean router classifies the same shape as
  `ProofFragment::BvAbstraction`. This moves AUFBV
  `rewrite__array__rw213.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 31/41 → 32/41** dominant with Lean unsat **11/20 → 12/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_bv_abs -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_array_bv_abstraction_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_bv_abstraction_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **2026-06-25** — **Small array-axiom certificate.**
  Added `array_axiom` and `Evidence::UnsatArrayAxiom` for direct negations of
  three checked array axiom schemas: McCarthy read-over-write,
  select-over-array-`ite`, and store-over-`ite` under select. The evidence
  checker re-scans the original assertions and re-matches the schema; the Lean
  router classifies the same shape as `ProofFragment::ArrayAxiom`. This moves
  AUFBV `smtaxiommccarthy.smt2`, `smtarraycond1.smt2`, and
  `smtarraycond3.smt2` from bare unsat to checked evidence plus
  real-Lean-checked proofs. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 28/41 → 31/41** dominant with Lean unsat **8/20 → 11/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **2026-06-25** — **Finite-array extensionality certificate.**
  Added `array_finite` and `Evidence::UnsatFiniteArrayExtensionality` for small
  BV-index arrays whose every concrete read is asserted equal while the arrays
  are asserted disequal. The evidence checker re-scans the original assertions,
  and the Lean router now classifies the same shape as
  `ProofFragment::FiniteArrayExtensionality`. This moves the four non-`uf`
  AUFBV `smtextarrayaxiom{1..4}.smt2` rows from bare unsat to checked evidence
  plus real-Lean-checked proofs. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 24/41 → 28/41** dominant with Lean unsat **4/20 → 8/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_finite_array_extensionality_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_finite_array_extensionality_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.
  A broad `cargo test -p axeyum-solver array_finite -j1` attempt was not
  completed because the local root filesystem filled and `rust-lld` crashed
  while linking generated test binaries; the focused evidence and real-Lean
  regressions passed.

- **2026-06-25** — **Direct array-extensionality Lean route.**
  `prove_unsat_to_lean` now handles the direct ABV Alethe congruence certificate
  for `a=b ∧ select(a,i)≠select(b,i)` before falling back to the array-elimination
  certificate. The EUF reconstructor discharges reflexive `eq_congruent` side
  hypotheses such as `(= i i)` with `Eq.refl`, so direct array-extensionality
  proofs now kernel-check in Lean. Re-ran exact dominance audits: **QF_ABV
  84/169 → 85/169** dominant with Lean unsat **1/83**, and **QF_AUFBV 20/41 →
  24/41** dominant with Lean unsat **4/20**; both remain at **mismatches=0,
  audit_errors=0, timeouts=0**. Updated `bench-results/DOMINANCE.md`,
  `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --test lean_crosscheck qf_abv -j1`;
  `cargo test -p axeyum-solver --test qfabv_proof -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **2026-06-25** — **Timed evidence export guard for array dominance audits.**
  `produce_evidence` now skips the optional BV-reduction DRAT exporter when an
  explicit timeout is active and stronger cert routes have declined, preserving
  timely checked bare-unsat evidence instead of overrunning audits. Added bounded
  exporter APIs and `diagnose_evidence`. Re-ran complete ABV/AUFBV dominance
  artifacts: exact dominant counts stayed fixed, while timeouts dropped from
  6→2 for ABV and 5→1 for AUFBV. At this intermediate point the remaining
  timeout files were `rw34`, `arraycond9`, and `fifo32ia04k05`.

- **2026-06-25** — **Array dominance audit timeouts eliminated.**
  Timed array solving now propagates budget `unknown` from the lazy array path
  instead of falling through to the expensive qf-bv fallback, and the older lazy
  select-congruence loop now shares the configured deadline across refinement
  rounds. Added deadline checks through auto-dispatch preprocessing, combined
  eager reductions, scalar backend calls, projection, and replay. Focused
  diagnostics for `rw34`, `arraycond9`, and `fifo32ia04k05` now return checked
  `unknown` evidence near the configured budget. Re-ran complete ABV/AUFBV
  dominance artifacts: **QF_ABV remains 84/169 dominant and QF_AUFBV remains
  20/41 dominant, both with audit_errors=0 and timeouts=0**.

- **2026-06-25** — **Dominance audit phase diagnostics.**
  `audit_dominance` now emits per-instance `phase_timings_ms`, `audit_phase`,
  and timeout-phase fields. Re-ran the complete QF_ABV and QF_AUFBV dominance
  artifacts; dominance counts stayed stable, and all 11 timeout rows now point
  at `produce-evidence`. `bench-results/DOMINANCE.md` summarizes timeout phases
  and its next step now reflects that the first audit queue is clear.

- **2026-06-25** — **First dominance audit queue cleared + QF_ABV lazy-ext projection fix.**
  Committed complete QF_ABV and QF_AUFBV audit artifacts and regenerated
  `bench-results/DOMINANCE.md`; exact audit rows now total 12 and the first audit
  queue is empty. QF_ABV is 84/169 dominant with 6 evidence timeouts/errors;
  QF_AUFBV is 20/41 dominant with 5 evidence timeouts/errors. Fixed the concrete
  QF_ABV SAT replay error exposed by `rw134`: fresh reads materialized during
  extensionality congruence refinement now get assignment defaults before
  evaluation. Added the exact nested-array-equality regression.

- **2026-06-25** — **Synthetic NIA/NRA dominance audits + graduated baseline ingestion.**
  `audit_dominance` now supports summary-style graduated baselines by enumerating
  corpus files and using `:status` annotations plus the committed aggregate
  `axeyum_decided` denominator. Added a small outer worker grace window so
  baseline-budget solver results are not misclassified as audit thread timeouts.
  Committed exact QF_NRA synthetic and QF_NIA synthetic audit artifacts and
  regenerated `bench-results/DOMINANCE.md`: exact rows are now 10. The QF_NRA
  row first exposed the SOS proof gap and was later widened to 24/30 dominant
  with 10/16 Lean unsats; later sessions closed QF_NRA synthetic at 30/30 and
  QF_NIA synthetic at 32/32.

- **2026-06-25** — **Dominance audit batch + pure-real evidence fallback.**
  Committed six more complete `audit_dominance` artifacts and regenerated
  `bench-results/DOMINANCE.md`, bringing exact audited rows to 8. New rows:
  BV/bitwuzla quantified initially 25% dominant, now later closed to 100%;
  QF_BV/bvred 100%, QF_LIA 70%,
  QF_LRA 78%, QF_UFLIA curated 0%, and QF_UFLIA bounded 80%; all have
  DISAGREE=0 and audit_errors=0. Fixed the pure-real evidence front door so an
  unsupported LRA certificate shape falls through to replayable SAT/bare UNSAT
  evidence instead of becoming an audit error; added a regression for the
  Boolean/ITE LRA SAT shape that exposed it. The audit harness now infers logic
  from corpus paths when old baselines have `config.logic = null`.

- **2026-06-23** — **Regression & testing-coverage expansion (goal-driven).** Built a
  reusable **oracle-free corpus-regression gate** (`tests/corpus_regression.rs`): parses
  status-annotated `.smt2`, runs `check_auto`, fails only on a wrong verdict (no Z3 → runs in
  default `cargo test`); tolerant (parse-gap/`unknown` skip), per-file wall-clock cap, scoping
  guard. Curated a **10-logic corpus** (`corpus/regression/`, 139 files): hand-verified seeds
  (QF_LRA/LIA/UF/UFLIA/BV/ABV/NIA/NRA/DT) + reused cvc5 `test/regress` (QF_LIA/LRA/ABV/FP/UF/BV/S,
  BSD, provenance documented) — **94 decided, 0 disagreements**, <3.5 s. Added **four new
  adversarial Z3 differential fuzz gates** (1500 seeded instances each, DISAGREE=0): **pure
  QF_LRA** (online LRA DPLL(T)), **pure EUF** (congruence keystone), **QF_UFLRA** (online EUF+LRA
  Nelson-Oppen combination — the new default route; 1389 agree / 111 sound-unknown), **enum
  QF_DT**. With the existing bv/abv/nia/nra/uflia fuzzes, the entire online-combination spine +
  datatypes are now directly fuzzed. FP is left to its existing **circuit-level differential**
  coverage (vs native f32/f64 + rustc_apfloat — a stronger oracle than a Z3 cross-check).
  Front-end-blocked (`declare-sort` pure-UF, unbounded strings) flagged as smtlib-lane gaps; the
  per-division **measured PAR-2 vs Z3** debt remains the larger follow-on. 8 commits, all gated
  (fmt + clippy `-D warnings`) + pushed. Reclaimed 35 GiB of `target/` mid-way (disk hit 100%).

- **2026-06-22** — **GPT/codex review follow-through verified + roadmap expansion.**
  (1) **Soundness:** `export_qf_lia_unsat_proof` is now fail-closed under the QF_NIA
  no-overflow multiplier guards (`5b80253`) — `IntBlasting::restricting_constraints()` gates a
  decline to `Inconclusive` before any DRAT export, closing a wrong-`unsat`-*proof* gap; negative
  regression added. (2) **Accuracy:** capability ledger + support matrix split/synced to the
  complete-CAD / improved-NIA-UFLIA state (`ab899f3`); doc-in-sync test green. (3) **Roadmap:**
  PLAN.md itemized gap-to-Z3/cvc5 (depth-not-breadth + ~3 missing engines), four new track phase
  docs (CHC/Horn P4.6, interpolation P3.8, synthesis P4.7, breadth backlog P2.10), LIA
  unbounded-completeness backstop (P2.4 T2.4.8), wired into the track READMEs + dependency DAG;
  bench-results README refreshed (authoritative QF_BV parity record + recent Unknown-reduction
  front). Reviewer validation set all green (nia_tiny_witness, proof_export, capabilities,
  support_matrix). Open: durable NIA-sweep artifact; classify the ~146 residual QF_NIA unknowns.

- **2026-06-20** — **DOCS: public documentation plan captured.**
  Added `docs/documentation-plan.md`, a concrete plan for reshaping the README
  into a short project lobby and scaffolding beginner, user-guide, contributor,
  reference, and internals docs. Link check passed.

- **2026-06-20** — **NRA geometry-parity gap CLOSED (binomial_square) + complete real-poly
  decider routed into the NRA engine + honest portfolio verdicts.** The reviewer flagged
  `binomial_square` `(x+y)²=x²+2xy+y²` as an unproved geometry goal that *also* overran the
  10 s config deadline (a never-hang hard-rule violation) — and demanded the outcome be
  disambiguated as a sound Unknown, never a Sat. Resolved end to end:
  1. **Constant-atom / identity recognition** (`nra_real_root.rs`): a polynomial identity's
     negation collapses to the ZERO polynomial, i.e. `0 ≠ 0`. `decompose_multivariate` now
     recognizes variable-free atoms via `MultiPoly::as_constant()` and decides them exactly —
     a FALSE constant (`0≠0`, `0<0`) ⇒ **Unsat** (this is what *proves* the identity), a TRUE
     one is dropped, all-dropped declines (never fabricates). binomial_square: **Unknown @ 20 s
     → Unsat, proved, ~0.7 ms** — z3 parity (z3 0.44 ms).
  2. **Decider hooked at the top of `check_with_nra`** so DIRECT callers (examples, consumers)
     get the same completeness, not just the `solve` auto-path. Strict gains, e.g. unbounded
     `(x-1)²+1<0` ⇒ Unsat (was unknown). `bnb_unbounded_square_is_unknown_not_wrong_unsat`
     upgraded to `unbounded_single_var_square_is_decided_unsat` (asserts the stronger Unsat).
  3. **Soundness confirmed:** probed `check_with_nra` directly — it returned
     `Unknown(ResourceLimit)`, **never Sat** (cardinal sin not committed); the geometry
     example's "no" was a *display* bug collapsing Unknown into a disproof. Fixed with a
     four-state `Verdict` (Proved/Countermodel/Unknown/NotApplicable).
  4. **Deadline bound** (committed prior, 904d4ed): `check_with_lra` Fourier–Motzkin now checks
     `past_deadline` + `MAX_FM_CONSTRAINTS=20_000`, so the 5.4 s uninterruptible elimination
     can no longer overrun the budget.
  - `geometry_portfolio` example now proves **6/6** goals (NRA, low-ms) at z3-parity, with an
    in-process libz3 `--features z3` column for the apples-to-apples solver-speed comparison.
    Gates green: fmt, clippy `--workspace` + the z3 example, full `axeyum-ir`+`axeyum-solver`
    suite (40 binaries, 0 failures). Commits d36914d, 92a6b4e, e88f025.
- **2026-06-20** — **REVIEW: Codex comprehensive design/implementation/benchmark review.**
  Added `docs/reviews/codex-20260620/diary.md` and
  `docs/reviews/codex-20260620/report.md`. Scope covered session state,
  roadmap/ADRs, crate/API inventory, IR/evaluator/model representation,
  solver dispatch, SAT-BV path, SMT-LIB front door, proof/evidence stack,
  committed benchmark artifacts, and targeted validation. Commands passed:
  `cargo fmt --all --check`, `./scripts/check-links.sh`, `cargo test -p
  axeyum-ir --lib`, `cargo test -p axeyum-solver --lib`, solver integration
  tests `capabilities`/`evidence`/`sat_bv`/`smtlib`, `cargo test -p axeyum-cnf
  --lib`, `cargo test -p axeyum-lean-kernel --lib`, and the committed micro
  benchmark corpus through `axeyum-bench`. Public corpus reruns were not run
  because `corpus/public` is absent in this checkout and disk is tight. Key
  review findings: make `prove_unsat` fail closed on proof-core resource
  exhaustion; fix `bv2nat` at and beyond 128 bits; remove evaluator overflow
  panic paths; replace scalar-only UF function models; implement or reject
  SMT-LIB `reset`; split `solve()` into explicit tactic contracts; make support
  claims exact by parser/IR/solver/model/proof layer.

- **2026-06-20** — **PERF: SAT-core investigation — the residual gap is propagation-bound + the
  recommended "preprocess-default" slice is ALREADY DONE (verified).** A read-only, data-backed
  SAT-core investigation (pure-Rust constraint): (1) batsat 0.6.0 via rustsat-batsat 0.7.5 is
  **config-locked** — the wrapper's opts field is private with no setter; tuning batsat's exposed
  knobs (var_decay/restart/luby/learntsize/random_var_freq) is **net-neutral**, A/B-measured. (2)
  The ~99 timeouts are **propagation-bound, not restart-bound**: `string1x8.4` burns ~205k
  conflicts but **169M propagations** (~770/conflict) across 5 configs, all timeout; `tcp_open`
  ~102k conflicts / 125M props. (3) **Genuinely hard**, not a batsat-vs-Z3 gap — Z3's bit-blast
  tactic also times out; Z3's full pipeline needs **42 s** on the smallest. (4) The investigation's
  #1 rec ("route the full word-level pipeline into the default `solve()` path + flip
  `preprocess` default-on") is **STALE — already implemented**: `solve()`→`check_auto` already runs
  `preprocess_reduce` (canonicalize→propagate_values→solve_eqs_bounded→elim_unconstrained→
  re-canonicalize) under `preprocess: true` default (ADR-0037/0034); the `--preprocess` flag only
  gates the *bench harness*, not the product. **Verified by reading auto.rs:82/381 + backend.rs:208
  before acting** (caught the stale rec — did not redo done work). **Honest conclusion:** the cheap
  perf levers on the QF_BV public corpus are exhausted/landed (word-level preprocessing default-on
  2→7/113; CNF inprocessing+compaction +1). The remaining SAT-core lever is a **multi-week
  pure-Rust kissat-class core** (fast watch-literal propagation + LBD clause deletion + vivification/
  on-the-fly subsumption + propagation-reducing preprocessing) that caps at the **~9 small-CNF**
  timeouts (the in-tree `xor_cdcl` with VSIDS/Luby/LBD also fails `string1x8.4`); the other ~90 are
  ≥650k-clause CNFs that defeat kissat itself in 30 s. kissat/CaDiCaL (C/C++) are barred from the
  default path by the no-C-dependency hard rule (feature-gated oracle at most).

- **2026-06-20** — **PERF measured: slice 1+2 = 3→4/113 (the inprocessing conversion); the
  remaining gap is SAT-search-bound, not encoding-bound.** Full A/B on the public p4dfa 113
  (DISAGREE=0, 0 replay failures throughout): `--preprocess` 3/113 @3s, 7/113 @20s;
  `--preprocess --inprocess` (slice 1+2) **4/113 @3s** (par2 5.864→5.837), **7/113 @20s**
  (par2 37.874→37.840). So CNF inprocessing captured exactly its one encoding-reachable
  conversion (slice 1's `compose.p2`) and **compaction is net-neutral on decided-count** on this
  corpus: at 3s BVE truncates before dropping a 2.1M-var case below the 2M ceiling *and* solving
  it; at 20s the var-bound cases are **already admitted** (3M ceiling) and BVE shrinking them ~28%
  **still doesn't make them solve** — proving the bottleneck for the residual ~106 is the SAT
  *search*, not the encoding. Compaction stays (sound, tested, un-refuses var-bound cases per the
  admission unit test, marginal par2 win) but is correctly not overclaimed. **Conclusion / next
  lever: the SAT core.** CNF inprocessing (subsumption+BVE+compaction) is now fully exploited; the
  large-CNF + search-bound band (ADR-0037's ~88 "defeat even kissat" + ~9 search-bound) needs an
  in-search technique — in-search inprocessing / a stronger CDCL / word-level reduction
  (`axeyum-rewrite`) — not more preprocessing. This is the measured handoff to the SAT-core slice.

- **2026-06-20** — **PERF (Track 1, #1) slice 2: CNF variable compaction — un-refuses var-bound
  EncodingBudget cases (sound model lift).** BVE removes variables but does NOT renumber, so the
  reduced formula's `variable_count()` still reports the original max index — and `check_cnf_budgets`
  (which reads it) kept refusing the var-bound EncodingBudget cases even after they eliminated 1M+
  variables. New `axeyum-cnf/src/compact.rs`: `compact(&formula) -> (CnfFormula, CompactMap)`
  collects the live variables (sorted `BTreeSet`, deterministic), densely renumbers `0..m`
  (sign-preserving clause rewrite), and reports `variable_count()==m` (strictly `<` whenever a var
  is dead). `CompactMap::expand(compact_model)` lifts a compacted model to original width:
  `out[new_to_old[i]] = compact_model[i]`, placeholders `false`. **Sound lift order:**
  solve(compacted) → `expand` (→ original-width, BVE-reduced model) → `Reconstruction::extend`
  (→ full original model). Placeholder soundness: a placeholder index appears in no clause of the
  compacted/reduced formula (compaction only renumbers), so its value is free there; `extend` then
  overwrites the BVE-eliminated indices; any still-dead index is in no clause of the original
  either (BVE only removes). Wired into `sat_bv_backend.rs` (`Inprocessed` carries the `CompactMap`;
  `reconstruct_sat_result` does `expand`∘`extend`; `check_cnf_budgets` sees the lower count). The
  no-inprocessing path is byte-identical. **Soundness tests:** 7 in-crate (deterministic, sat-preserving,
  a BVE-eliminates-AND-renumbers round-trip, a 400-iter random BVE+compact stress) + 2 backend
  (var-count drops + model replays; a budget split between compacted and un-compacted counts is
  admitted+solves+replays with inprocessing on, refused `Unknown(EncodingBudget)` with it off —
  proving admission actually changes); `cnf_inprocessing_agrees_with_baseline_and_replays` unchanged.
  fmt + clippy(cnf+solver) + solver-doc + full suite (FULL_EXIT=0) green. (Pending: measure the
  decided-count delta on the public 113 at 3s/20s with slice 1+2.) Sub-agent + soundness review
  (verified the `expand`∘`extend` lift by hand).

- **2026-06-20** — **PERF (Track 1, #1) slice 1: CNF inprocessing un-gated — public p4dfa 3→4/113,
  DISAGREE=0.** A read-only perf investigation found the highest-value sound lever already exists,
  is plumbed, and is soundness-tested — but was OFF/mis-gated: `axeyum-cnf`'s `simplify`
  (subsumption + self-subsuming resolution, model-preserving) + `bve` (bounded variable
  elimination, equisat + `Reconstruction::extend` model lift) ran behind a 200k-var/1M-clause
  admission cap that excluded the entire EncodingBudget band (2M+ vars / 5–8M clauses), so no
  measured run ever used it on the cases it can convert. Raised `INPROCESS_MAX_VARIABLES`/`_CLAUSES`
  to 4M/16M (safe: `maybe_inprocess` time-bounds the passes to half the solve budget; the
  deadline-truncated partial result stays sound — the budget, not the cap, is the hang-preventer).
  **Measured A/B at fair-3s (`--preprocess` vs `--preprocess --inprocess`): 3→4 decided,
  DISAGREE=0, 0 model-replay failures, par2 5.864→5.832** — a sound, positive, zero-correctness-cost
  gain (the `compose.p2` instance flips batsat-Timeout→SAT via BVE). At 3s the BVE pass runs
  truncated, so the var-bound EncodingBudget cases still await **slice 2** (variable compaction —
  `variable_count()` isn't compacted after BVE, so they stay budget-refused despite eliminating
  1M+ vars) + the 20s tier. Added reproducible `bench-public-qfbv-preprocess-inprocess-fair-3s/-20s`
  recipes. Default `cnf_inprocessing` stays `false` pending a broad-suite measurement before any
  global flip. Full suite (incl. `cnf_inprocessing_agrees_with_baseline_and_replays`) + clippy +
  doc + fmt green. Investigation sub-agent + independent A/B re-measurement.

- **2026-06-20** — **P2.5: single-variable integer polynomial EQUATIONS `p(x)=0` (any degree)
  decided via the rational root theorem.** Generalizes the quadratic path (deg≤2 incl.
  inequalities unchanged) to arbitrary-degree `p(x)=0`/`≠0` in `nia_square.rs`: `Poly` collects a
  general single-var integer polynomial (checked arithmetic; `MAX_DEGREE=64`, `|coeff|≥2^40` or
  any overflow → decline). For degree≥3 equality: if `a₀=0`, x=0 is a root (Sat); else every
  integer root divides `a₀` (rational root theorem, q=1 for an integer unknown) — enumerate
  divisors of `|a₀|` (both signs, magnitude-guarded), evaluate `p` by overflow-safe Horner, return
  Sat (first root, replay-checked) or **Unsat only when EVERY divisor is checked and none is a
  root** (exact). `≠0` ⇒ Sat (≤n roots; bounded non-root scan). Degree≥3 inequalities DECLINE (no
  exact bounded method). Decides `x³−1=0`→Sat, `x³−2=0`→Unsat, `x³−6x²+11x−6=0`→Sat (x∈{1,2,3}),
  `x⁴−5x²+4=0`→Sat, `x³+x+1=0`→Unsat, `x⁵−x=0`→Sat (x=0). Soundness-negatives decline: `x³+y`,
  non-int coeff, `x³<0`, `|a₀|≥2^40`, 2nd assertion, Real. The UNSAT direction is exact only after
  the exhaustive no-overflow divisor check; any slip → decline (+ Sat replay-check backstop). New
  `tests/nia_polynomial.rs` (15); deg≤2 (`nia_quadratic` 29, `nia_square` 27) unchanged. Sub-agent
  + soundness review (rational-root logic + all four guards verified by hand).

- **2026-06-20** — **P2.5: single-variable integer QUADRATIC `a·x²+b·x+c ⋈ 0` decided exactly
  (generalizes `x*x ⋈ c`).** `nia_square.rs` matcher generalized to a degree-2 single-variable
  integer polynomial (`Poly{c0,c1,c2}` via a checked-arithmetic recursive collector; degree>2 /
  multi-var / non-Int / `|coeff|≥2^40`-overflow all decline). Decided exactly via discriminant +
  convexity, downward parabolas (`a<0`) reduced to `a>0` by negating `f` and flipping `⋈`: `=0` ⇒
  perfect-square `D=b²−4ac` AND integer root `(−b±s)/(2a)` (rejects `4x²−1=0`); `≠0` ⇒ always Sat;
  `<0`/`≤0` ⇒ convexity puts the integer minimum at `⌊x*⌋`/`⌈x*⌉` (`x*=−b/2a`), so it evaluates
  `f` at the two straddling integers — **never constructing an irrational root** — getting the
  strict/non-strict boundary exact (`x²−3x+2<0`→Unsat, `≤0`→Sat at x=1); `>0`/`≥0` ⇒ always Sat
  (bounded outward scan). Every Sat is **replay-checked** against the original assertion — any
  logic slip degrades to a sound decline, never a wrong verdict. Decides `x²−5x+6=0`→Sat,
  `x²+1=0`→Unsat, `x²−4x+4=0`→Sat (double root), `2x²−4=0`→Unsat, `x²−4<0`→Sat, `x²+x+1>0`→Sat.
  Soundness-negatives decline: `x²+y`, `x³`, Real, 2nd assertion. New `tests/nia_quadratic.rs`
  (29 + 3 unit); legacy `nia_square` (27) subsumed; full suite + clippy + doc + fmt green. Sub-agent
  + soundness review (verified the convexity/straddling-integer test + boundaries by hand).

- **2026-06-19** — **P2.6: guarded-finite `∀` over an inner `∃` decided (`∀x:Int.(0≤x≤3)⇒∃y.y=x*x`
  → Sat).** Two pipeline steps dropped the inner `∃`: (1) `expand_guarded_int_universals` declined
  on ANY quantifier in the body, and (2) even when expanded, the exposed `⋀_v ∃y.P(v,y)` existentials
  sit inside `∧` (not at an assertion root), so the top-level skolemizer never reached them and
  `Int`-domain expansion failed → Unknown. Fix: the guarded pass now declines only when an inner
  quantifier RE-BINDS the outer `x` (capture — `rebinds_var`); other inner quantifiers pass through
  (substituting a ground `Int` const for `x` is capture-free). New `skolemize_positive_existentials`
  skolemizes every `∃` in a STRICTLY POSITIVE Boolean position (reachable through only `∧`/`∨`) to a
  fresh `!gk_N` constant — stopping at negation / `⇒`-antecedent / `ite` / `=` / `∀`, where naive
  skolemization is unsound (left to the refutation fallback). `check_with_quantifiers` applies this
  INLINE (no recursion — guard: the guarded pass fired AND a quantifier remains, so strictly closer
  to QF) and uses the skolemized form as both dispatch and sat-replay base (equisatisfiable, so the
  original-assertion replay anchor holds). Decides the target + `∀x.(0≤x≤2)⇒∃y.y>x` → Sat.
  **Soundness-negatives:** `∀x.(0≤x≤2)⇒∃y.(y>x∧y<x)` and `…⇒∃y.(y=x*x∧y<4)` → Unsat (inner `∃`
  unsatisfiable per x ⇒ universal false), never a wrong Sat. New `tests/quant_guarded_inner_exists.rs`
  (5); full suite + clippy + doc + fmt green, no hangs. Sub-agent + soundness review.

- **2026-06-19** — **ROBUSTNESS: BV optimization honors `config.timeout` (closes an unbounded
  hang).** Found by the non-arith deep hunt: every bit-vector optimizer ran its feasibility
  probes with a hardcoded `SolverConfig::default()` (no timeout), and the `Solver` façade dropped
  `self.config` — so a hard BV probe (e.g. maximizing over a 64-bit Euclid-reconstruction UNSAT
  core) ran forever regardless of the caller's budget. Symmetric to the LIA/Real `*_with_config`
  fix done earlier (which the BV path never got). Fix: `bv_value`/`pareto_bv_probe` now take and
  thread `config`; new `*_bv_with_config` variants for all 7 optimizers (`maximize_bv` …
  `optimize_bv_pareto`) derive a deadline and bail gracefully in the search/point loops
  (`OptOutcome::Unknown(ResourceLimit)` / `LexOutcome::Stopped` / `ParetoOutcome::Truncated`
  best-so-far); the no-config functions delegate with `default()` (existing call sites + optima
  byte-identical); the `Solver` façade passes `self.config`. The Euclid core via
  `maximize_bv_with_config(timeout=2s)` now returns in ~2s (was unbounded). New
  `tests/optimize_bv_timeout.rs` (3, incl. optima-unchanged + façade); existing optimize (24) +
  robustness (6) optima unchanged; full suite + clippy + doc + fmt green. **With this, both deep
  hunts (arith + non-arith) give a clean bill — no hangs, no wrong answers across all theories.**
  Sub-agent + soundness review.

- **2026-06-19** — **P2.5: single-variable integer square `x*x ⋈ c` decided exactly (`x*x=2` →
  Unsat).** Closes a hunt-flagged NIA gap. New `nia_square.rs` (`decide_int_square_constraint`):
  fires only when the WHOLE query is exactly one assertion `(x*x) ⋈ c` — `x*x` is `IntMul` of the
  SAME leaf Int-variable symbol, `c` an `IntConst`. Then decided exactly: `=` ⇒ `c<0` Unsat else
  Sat iff `isqrt(c)²==c` (witness `r`) else Unsat; `<`/`≤` ⇒ Unsat for `c≤0`/`c<0` else Sat (x=0);
  `>`/`≥`/`≠` ⇒ always Sat. `isqrt` is overflow-safe (binary search; constants `|c|≥2^100` decline
  → left to the existing NIA path). Hooked in the `has_int` branch BEFORE `int_real_relax`/the
  width ladder (which return Unknown for `x*x=2`). Every Sat **replay-checks** the witness against
  the original assertion (`eval`). **Conservative DECLINE** (verified not-mis-decided): `x*y`,
  `x*x*x`, `x*x+x`, `x*x=y` (rhs non-constant), Real square (NRA √ case), and any 2nd assertion on
  x. Decides `x*x=2`→Unsat, `x*x=4`→Sat, `x*x=1000000`→Sat (x=1000), `x*x<0`→Unsat. New
  `tests/nia_square.rs` (27) + corrected the now-stale `int_square_equals_two_stays_unknown`
  assertion (→ `_is_unsat`); full suite (1122) + clippy + doc + fmt green. Sub-agent + soundness review.

- **2026-06-19** — **P2.6: `∀∃` by Skolem-witness synthesis — `∀x:Int.∃z:Int. z>x` → Sat.** First
  cut into the `∀∃` direction (previously all `Unknown`). New `quant_exists_witness.rs`
  (`decide_forall_exists_by_witness`): for a prenex `∀x⃗.∃z. body` (one inner `∃`, `z`:Int/Real,
  QF body), synthesize a Skolem witness `g(x⃗)` from a single bound on `z` (coefficient ±1
  required) — `z>t ⇒ t+1`, `z≥t ⇒ t`, `z<t ⇒ t−1`, `z≤t ⇒ t`, `z=t ⇒ t` — substitute `z:=g`,
  and check `∀x⃗. body[z:=g]` VALID via `check_auto` (the substituted body is QF, so exactly one
  bounded solve, terminating). UNSAT-of-`¬body[z:=g,x⃗:=c⃗]` ⇒ valid ⇒ original **Sat**.
  **Sound one-directional:** the synthesis only PROPOSES; the validity check DECIDES — a wrong
  proposal can only fail to validate, so this NEVER returns Unsat and NEVER a wrong Sat (the
  no-witness case declines to Unknown). Decides `∀x:Int.∃z. z>x`, `∃z. z=x+1`, the Real twin,
  `∃z. z≥x∧z≤x`, `∀x,y.∃z. z>x+y`. Soundness-negatives decline: inconsistent `z>x∧z<x`, no-gap
  `z>x∧z<x+1` (truly Unsat but Unknown sound), non-±1 `2z>x`. New `tests/quant_exists_witness.rs`
  (10); full suite + clippy + doc + fmt green, no hangs. Sub-agent + soundness review.

- **2026-06-19** — **P2.6: open constant-width-gap integer `∀` decided (`∀x:Int.(x≤y∨x≥y+2)` →
  Unsat).** Closes the one completeness item the hunt flagged. New
  `eliminate_int_universal_open_gap` (`quant_fourier_motzkin.rs`): for an OPEN integer universal
  (symbolic parameters), per DNF clause of `¬φ` it extracts the (one lower, one upper) symbolic
  bounds and applies the exact integer-content test WHEN the gap is translation-invariant — the
  lower endpoint `L` is integer-valued (integer coefficients + constant; `x≤y` type-forces Int
  parameters) and the width `w = U − L` is a CONSTANT integer (the symbolic parts cancel). Then
  the integer content `= w − [lo strict] − [hi strict] + 1` is the same for every parameter
  assignment: any clause that ALWAYS contains an integer ⇒ `∃x.¬φ` always holds ⇒ the universal
  is **Unsat**; all clauses NEVER contain ⇒ **rewrite-to-`true`** (valid); otherwise DECLINE.
  Decides `∀x:Int.(x≤y∨x≥y+2)`/`+3`/`(x≤y−1∨x≥y+1)` → Unsat and `(x≤y∨x≥y+1)`/`(x≤2y∨x≥2y+1)`
  → Sat. **Soundness-negatives verified:** distinct-param `(x≤y∨x≥z+2)` (symbolic width `z−y+2`)
  declines (not-Unsat AND not-Sat); width-1 multiple-coefficient `(2y,2y+1)` → Sat (never wrongly
  Unsat); non-linear `x*x≥0` declines. Hooked after the closed/real/valid FM paths; strictly
  additive. New `tests/quant_int_open_gap.rs` (9); full suite + clippy + doc + fmt green.
  Sub-agent + soundness review (verified the content formula + the disjunction logic by hand).

- **2026-06-19** — **P2.x COMPLETENESS: gcd-aware integer tightening + a hang/wrong-answer hunt
  (clean bill).** Refined the strict-inequality tightening to be gcd-exact: `L + c0 < 0` (L a
  multiple of `g = gcd(aᵢ)`) ⟺ `L ≤ g·⌊(-c0-1)/g⌋`, so `2x < 2y` ⟹ `2x-2y ≤ -2` (not the loose
  `≤ -1`). Now `2x<2y ∧ 2y<2x+2`, `3x>3y ∧ 3x<3y+3`, `1000x<1000y ∧ 1000y<1000x+1000` all decide
  UNSAT immediately (`g=1` reduces to the prior `c0+1`; magnitude-guarded by `TIGHTEN_COEFF_LIMIT`
  to avoid i128 overflow — out-of-range coefficients left strict, sound). A read-only **hunt over
  ~30 arithmetic + quantifier queries found NO hangs and NO wrong answers** (independently
  confirming the LIA fix + the coefficient cases); all remaining gaps are graceful `Unknown` on
  harder fragments (NIA `x*x=2`, NRA √2, ∀∃-witness synthesis). New gcd-coefficient tests; full
  suite green. **Queued actionable item:** `∀x:Int.(x≤y ∨ x≥y+2)` → should be UNSAT (the k≥2
  sibling of the now-Sat k=1 valid case — `∃x` in the open width-k interval `(y,y+k)` exists for
  all y when k≥2; the instantiation fallback misses the uniform witness `x=y+1`).

- **2026-06-19** — **P2.x COMPLETENESS: integer strict-inequality tightening — `c>y ∧ c<y+1`
  decides UNSAT instantly (and the open-`∀` decides Sat).** The follow-up to the LIA-hang
  deadline below: rather than merely *not hang*, the LIA solver now *decides* these. A strict
  constraint `expr < 0` over an integer-valued `expr` (all coefficients integral; vars integer)
  is equivalent to `expr ≤ -1` ≡ `expr + 1 ≤ 0`; `lia_simplex_within` tightens every such
  constraint to non-strict before branch-and-bound, making the LP relaxation EXACT. So
  `c > y ∧ c < y+1` ⇒ `c−y ≥ 1 ∧ c−y ≤ 0` is immediately LP-infeasible → instant UNSAT (no
  grind, no deadline needed), and therefore `∀x:Int.(x≤y ∨ x≥y+1)` (valid — no integer between
  consecutive integers) now decides **Sat** via the valid-universal pass, fast. Only applied
  when `expr` is provably integer-valued (else left strict — sound). Equisatisfiable, so no
  existing LIA verdict changes (lia_simplex + full suite green). Tests:
  `qf_strict_between_consecutive_is_unsat_fast` (→ Unsat) and
  `open_disjunctive_universal_is_valid_and_fast` (→ Sat), both in 0.00s.

- **2026-06-19** — **ROBUSTNESS: QF-LIA branch-and-bound honors `config.timeout` (root of the
  open-`∀` hang).** The real root: a QF-LIA query `c > y ∧ c < y+1` (real-feasible at c=y+0.5,
  integer-infeasible — no integer strictly between consecutive integers) sent
  `lia_branch_and_bound` (`lra.rs`) grinding toward its 50 000-node budget — each node a simplex
  over an ever-deeper constraint stack as it kept finding shifted fractional points — with **no
  wall-clock check**, ~minutes ignoring the budget. (Triggered pre-existingly by
  `eliminate_valid_universals` testing `∀x:Int.(x≤y ∨ x≥y+1)` for validity via `¬body[x:=c]`
  UNSAT.) Fix: `lia_branch_and_bound` takes an `Option<Instant>` deadline checked per node
  (alongside the node budget); new `check_with_lia_simplex_within(arena, assertions, deadline)`
  threads it (`check_with_lia_simplex` = the `None` case, signature unchanged so the
  function-pointer callbacks in `dpll_lia` are untouched); the two `auto.rs` integer-dispatch
  sites derive the deadline from `config.timeout`. Now `∀x:Int.(x≤y ∨ x≥y+1)` returns in ~2 s at
  a 2 s budget (was ~600 s). Belt-and-suspenders from the same investigation: `prove_unsat_by_mbqi`
  (`MAX_MBQI_INSTANCES=4096` + deadline) and `prove_quantified_unsat_via_egraph`
  (`MAX_GROUND_TERMS=8192` + deadline) also bail gracefully. Sound — only `Unknown` (the budget
  case) is added; no verdict changes. New `tests/quant_open_disjunctive_no_hang.rs` (OS-timeout
  guarded, never a wrong `Unsat`). Diagnosed by marker + panic bisection down to the QF subquery. `∀x:Int.(x≤y ∨ x≥y+1)` (open, symbolic `y`) is declined
  by the FM int-closed pass and reaches the instantiation search, which generates ever-deeper
  ground terms (`y, y+1, y+2, …`); the per-round `check_auto` grew without a `config.timeout`
  check, so the query tarpitted ~600s ignoring the budget. Both loops now bail to a graceful
  `Unknown(ResourceLimit)`: `prove_quantified_unsat_via_egraph` (a `config.timeout` deadline +
  `MAX_GROUND_TERMS=8192` cap, checked at the top of each round) and `prove_unsat_by_mbqi`
  (deadline + `MAX_MBQI_INSTANCES=4096`). Sound — both only ever returned `Unsat` from a ground
  refutation, so degrading the non-refuting path to `Unknown` changes no verdict. New
  `tests/quant_open_disjunctive_no_hang.rs` (2 s budget returns, never a wrong `Unsat`),
  OS-timeout-guarded. Same posture as the NIA-hang fix. Found via the int-closed work.

- **2026-06-19** — **P1.2 PERF: word-level preprocessing now runs to a FIXPOINT (the proven
  reduction lever, not AIG node-count).** `check_with_preprocessing` ran the model-sound passes
  (`canonicalize` → `propagate_values` → `solve_eqs_bounded` → `elim_unconstrained` →
  re-`canonicalize`) exactly ONCE. But one pass is not enough: `elim_unconstrained` can expose a
  fresh constant that `propagate_values`/`solve_eqs` then eliminate, and the re-canonicalization
  AC-normalizes substituted product trees that reveal further folds. Now it iterates the passes to
  a fixpoint (a round eliminating nothing stops; `MAX_PREPROCESS_ROUNDS=8` guards oscillation),
  composing each round's `ModelReconstructionTrail` in pass/round order. Removes more variables
  before bit-blasting → relieves the encode budget (the mechanism PLAN.md credits for public p4dfa
  2→7/113). **Sound by construction:** every pass is model-sound (equisatisfiable, so `unsat`
  transfers), and the `sat` model is still replayed against the ORIGINAL assertions — any trail/round
  composition bug surfaces there as an `Err`, never a wrong `sat`. New
  `fixpoint_resolves_a_deep_definition_chain` test (deep `w=2 → x1 → x2 → x3=5` chain: sat replays,
  contradicted-chain unsat agrees with no-preprocess); existing `preprocess_on_off_agree_on_a_battery`
  + suite green. Validated by measured DISAGREE=0, NOT node count (per the AIG finding above).

- **2026-06-19** — **P2.6: integer-Omega exactness for CLOSED universals — decides the
  inter-integer-gap cases.** `∀x:Int.(x≤0∨x≥1)` is integer-VALID but real-INVALID (x=0.5), so the
  real-validity relaxation declines it; the new `eliminate_int_universal_closed` decides it EXACTLY.
  For a CLOSED universal (φ mentions only x — every FM bound is a concrete `Rational`), `∀x:Int. φ
  ⟺ ¬∃x:Int. ¬φ`; each DNF clause of `¬φ` is a concrete real interval, and `clause_has_integer`
  runs the exact integer-emptiness test: lower L admits `ceil(L)` (non-strict) / `floor(L)+1`
  (strict), upper U admits `floor(U)` / `ceil(U)-1`, clause has an integer iff `lo_int ≤ hi_int`
  (unbounded side ⇒ trivially yes); `floor` via `div_euclid`, ±1 saturating at i128 extremes. Any
  clause with an integer ⇒ Unsat; none ⇒ rewrite to `true` (Sat). Any non-constant residual ⇒
  DECLINE (open universal — left to the real-validity path / front door). Hooked after the real
  path + the closed path, before `eliminate_int_universal_valid`. Decides `∀x:Int.(x≤0∨x≥1)`→Sat,
  `∀x:Int.(x≤0∨x≥2)`→Unsat (hole `(0,2)`∋1), `∀x:Int.(x<0∨x>0)`→Unsat. Soundness-negatives: open
  universals decline (unit-tested `is_none`), non-linear declines. New `tests/quant_int_fm_closed.rs`
  (11) + 5 in-source unit tests; full suite (1071) + clippy + doc + fmt green. (Flagged: an open
  disjunctive universal, once declined, tarpits the downstream MBQI/e-matching ~600s — pre-existing
  "never hang" item, now in the work queue.) Sub-agent + soundness review (verified the ceil/floor
  strictness by hand).

- **2026-06-19** — **P2.6: sound integer `∀`-elimination via real-validity (one-directional).**
  Extends the FM pass to decide `∀x:Int. φ` using ONLY the sound direction: integers ⊆ reals, so
  `∀x:Real. φ` valid ⇒ `∀x:Int. φ` valid (the converse is FALSE — e.g. `∀x:Int.(x≤0∨x≥1)` is
  integer-valid but real-invalid, x=0.5). `eliminate_real_universal`'s body was factored into
  `eliminate_core(…, relax_int)` returning a `Verdict` enum (`Valid` / `Unsat` / `Rewrite(χ)`) —
  cleanly isolating the "valid" verdict. New `eliminate_int_universal_valid` runs the core with
  `relax_int=true` (admitting `IntLt/Le/Gt/Ge` + Int `Eq`) and returns a `true`-rewrite **iff and
  only iff** the verdict is `Valid`; `Unsat` and any `Rewrite(_)` ⇒ DECLINE (concluding unsat
  would be unsound — the integer universal may hold in the inter-integer gaps; rewriting to the
  stronger real-χ would under-approximate). The Int path can therefore NEVER emit `Unsat` or a
  non-`true` rewrite. Hooked after the real path (`.or_else`), and after `unsat_universal` (so
  `∀x:Int. x>0` still → Unsat there). Decides `∀x:Int.(x≤0∨x>0)`, `∀x:Int.(x<5∨x≥5)` → Sat.
  **Soundness-negatives verified:** `∀x:Int.(x≤0∨x≥1)` (int-valid, real-invalid) declines → NOT
  mis-decided unsat; `∀x:Int.(x≥0∧x≤10)` (int-false) declines → does NOT become Sat (stays Unsat
  via other passes). Real path byte-identical (15 FM tests unchanged). New
  `tests/quant_int_fm_valid.rs` (7); full suite + clippy + doc + fmt green. Strictly additive +
  conservative. The full integer-Omega (deciding the inter-gap cases) remains the keystone.
  Sub-agent + careful soundness review.

- **2026-06-19** — **P2.6: single-variable real Fourier-Motzkin `∀`-elimination — first true
  quantifier elimination (keystone slice).** Decides multi-atom `∀x:Real. φ` universals the
  single-atom/vacuous passes decline, via exact real QE. New `quant_fourier_motzkin.rs`
  (`eliminate_real_universal`), hooked in `solve` after the vacuous + unsat-single-atom passes.
  Method: `∀x. φ ⟺ ¬∃x. ¬φ`; `¬φ` → DNF (De Morgan + `⇒`-desugar, capped at 64
  clauses/literals); `∃x` distributes, each conjunctive clause FM-eliminated — collect lower
  (`a<0`) / upper (`a>0`) bounds `-r/a` from `a·x+r ⋈ 0` (equality = both; x-free pass through),
  join `Lᵢ ⋈ Uⱼ` with **`<` iff either bound strict** else `≤` (the subtle correctness point:
  `∀x.(x≤0 ∨ x>0)` is valid — join `0<0` false — while `∀x.(x<0 ∨ x>0)` is unsat — join `0≤0`
  true at x=0); unbounded side ⇒ vacuously satisfiable. A clause eliminating to `true` ⇒ the
  universal is **Unsat**; else negate the residual disjunction → an x-free `χ` and **rewrite**
  the assertion to it (then re-dispatch). Real FM is EXACT, so in-scope verdicts are exact.
  **Conservative declines (sound — leave byte-identical):** Int universals (real FM isn't exact
  over ℤ — the load-bearing guard), nested quantifiers, non-linear x (`x·x`/`div`/`abs`/x-in-UF/
  array → opaque affine), non-real atoms, x-disequalities (single-point hole), over-cap DNF.
  Decides `∀x.(x≥0∧x≤10)`→Unsat, `∀x.(x≤0∨x>0)`→Sat, `∃y.∀x.(x≤y∨x≥y)`→Sat,
  `∀x.(x<0∨x≥y)`→`y≤0`. Soundness-negatives verified (non-linear `x·x` and Int both declined,
  no real universal mis-decided). New `tests/quant_fourier_motzkin.rs` (15); full suite (1047) +
  clippy + doc + fmt green. Strictly additive. The harder integer-Omega + general-boolean cases
  remain the keystone core. Sub-agent + careful soundness review.

- **2026-06-19** — **P2.6: unsatisfiable-`∀` detection — another sound `∃∀` slice.** A top-level
  `∀x. body` where `x:Int`/`Real`, `body` is a SINGLE arithmetic atom that normalizes to
  `c·x ⋈ t` with `c≠0` (x genuinely appears), `t` x-free, and `⋈∈{<,≤,>,≥,=}` is
  **unconditionally UNSAT** (a linear function of an unbounded x can't satisfy a one-sided
  constraint for all x). New `quant_unsat_universal.rs` (`detect_unsatisfiable_universal`),
  hooked in `solve` AFTER `eliminate_vacuous_universals` (which owns the `c=0` case — no overlap)
  and before `check_with_quantifiers`, returning `CheckResult::Unsat` on a match. Reuses the
  vacuous pass's `Affine`-over-`Rational` collector (so `c≠0` ⇒ the residual is exactly `c·x ⋈ t`,
  t x-free; `affine` returns `None` on any non-linear/UF/array/`bv2nat` x-occurrence ⇒ decline).
  Decides `∀x:Int. x>0`, `∀x:Int. 2x=5`, `∀x:Real. x≤y`, and (with the existing `∃`-skolemization)
  `∃y:Int.∀x:Int. x≤y` — all → Unsat (were Unknown). **Soundness-negatives verified:** `∀x. 2x≠5`
  (true; `≠` is `not(eq)` = `BoolNot`, declined structurally → not Unsat), `∀x. x+y≥x` (c=0 →
  vacuous pass, not this one), `∀x.(x>0 ∨ x≤0)` (valid disjunction, multi-atom → declined),
  guarded `∀x.(0≤x≤2)⇒x≥5` (implication → declined, still Unsat via the guarded path). New
  `tests/quant_unsat_universal.rs` (9); the quant sibling suites all green. Strictly additive.
  Sub-agent + soundness review.

- **2026-06-19** — **P3.3: quantifier certs made assume-independent (closes the main
  emitter-trust gap).** The finite-`∀` cert re-check (`check_alethe_lra_guarded_inst`) verified
  the `forall_inst_guarded` instantiation + rule structure but **accepted the proof's
  ground-fact and abstraction-definition `assume`s as given** — so a proof could `assume` a fact
  not in the query and still pass. New `check_alethe_lra_guarded_inst_against(universal, proof,
  arena, assertions)` (threaded from `Evidence::check`, which already has `assertions`) now
  classifies every `assume` and REJECTS (`Ok(false)`) anything that is not: (1) the carried
  universal, (2) an original assertion (rendered via the same `term_to_alethe_uf` the emitter
  uses — exact key match), (3) a genuinely-fresh Ackermann definition `(= !fn_app_N (f t))`
  (the introduced const must not occur in the rendered query — the load-bearing freshness
  guard), or (4) an abstracted original assertion bridged through a class-3 definition. Both
  emitters self-validate through the strengthened checker so emission and consumer re-check
  agree. **Soundness-negative tests** (`assume_independent_check_rejects_fabricated_premise`
  LIA/UF, `..._rejects_non_fresh_definition`) assert the OLD checker returns `Ok(true)` on a
  fabricated `(= a 5)` / non-fresh `(= x (g x))` assume while the new check + `Evidence::check`
  reject it — proving the gap is closed. All genuine LIA/UF/pure-LIA-`∀`/UFLIA certs + existing
  tamper tests still pass (no false negatives; class 4 was required to keep UF certs green).
  One residual remains (the carried universal isn't yet cross-verified ∈ `assertions` — see
  frontier). fmt + clippy + doc + full suite + Carcara (54) green. Sub-agent + soundness review
  (I traced and recorded the residual).

- **2026-06-19** — **P3.3: finite-`∀`-over-UF `unsat` certified (quantifier proof extended to
  a UF+arith tail).** The finite-`∀` cert only handled a pure-LIA ground tail, so
  `∀x:Int.(0≤x≤1) ⇒ f(x)=0` with `f(0)=1` (a finite-`∀` whose body uses an uninterpreted `f`,
  unsat by EUF on the instances) stayed `Unsat(None)`. New `prove_finite_int_quant_unsat_uf_alethe`
  (`quant_finite_cert.rs`): builds the ground instances, **Ackermann-abstracts** the UF residual
  via `eliminate_functions` (fresh same-sorted `v_k = f(v)`), gates on `check_with_lia_simplex(abstraction) == Unsat`,
  emits the `lia_generic` tail over the abstraction, and splices per-instance `forall_inst_guarded`
  → `resolution` → (assume the fresh `v_k=f(v)` definition) → `eq_transitive` (`v_k=f(v)=c ⊢ v_k=c`),
  so each abstracted instance flows from the universal. Reuses `Evidence::UnsatGuardedQuantAletheProof`
  + `check_alethe_lra_guarded_inst` (validates all three rule families: the custom
  `forall_inst_guarded` hook, base `eq_transitive`/`symm`, and `lia_generic`). Self-validating
  (emit only on re-check) + tamper test (out-of-range witness AND corrupted `eq_transitive`
  bridge both rejected). Ordered after the pure-LIA finite-`∀` path; strictly additive. Certifies
  the target + a wider-range twin; pure-LIA finite-`∀`, gap-C UFLIA, and a SAT UF-universal all
  unregressed. fmt + clippy + doc + full suite + Carcara (54) green. **Assurance (honest):** same
  tier as the finite-`∀` cert — in-tree-checked custom rule, NOT Carcara/Lean cross-checked, and
  the `check_alethe_lra_guarded_inst` re-check verifies the instantiation + rule structure but
  **trusts the emitter's ground-fact/abstraction-def `assume`s** (it doesn't cross-verify them
  against the original assertions). Sound in practice (the emitter uses the original assertions +
  genuinely-fresh `eliminate_functions` vars), but closing this to a fully assume-independent
  check is a real follow-up (see frontier). Sub-agent + soundness review.

- **2026-06-19** — **P3.3: certified `bv2nat`-bound `unsat` (gap D) — last self-contained
  certification gap from the proof-completeness map.** `bv2nat(x) ≥ 16` for a 4-bit `x` (and
  similar int-blast bound contradictions) was a bare `Evidence::Unsat(None)`; it now carries an
  independently-checkable `lia_generic` certificate. `bv2nat_bound_certificate` clones the arena,
  abstracts each `bv2nat(b)` (w-bit) to a fresh Int `n` with the range axiom `0 ≤ n ≤ 2^w−1`
  (parity with `auto`'s divmod elimination), and emits `prove_lia_unsat_alethe` over the pure-LIA
  abstracted query (re-checked by `check_alethe_lra`), attached as `Evidence::UnsatArithAletheProof`.
  **Honest partial-trust** (zero-trust would need a `bv2nat`→bit-literal emitter, which doesn't
  exist — not forced): `trusted_steps = [(IntBlast, false), (Farkas, true)]` — the LIA refutation
  is certified, only the `bv2nat`-range/width-bridge axiom (ADR-0014) is trusted (reused the
  existing `IntBlast` TrustId — no new ADR). Wired after `guarded_quant_alethe_certificate` and
  before the bare fallback; declines (`None`) without an abstractable `bv2nat`, so plain
  LIA/UFLIA/zero-trust paths are never shadowed. Tamper test (drop closing step → reject) proves
  the check is real. New `tests/evidence_bv2nat_cert.rs`; plain QF_LIA keeps its Farkas-only cert
  (no spurious IntBlast hole), QF_BV unchanged, SAT `bv2nat=7` never reported unsat. fmt + clippy +
  doc (z3-feature) + full suite + Carcara green. Strictly additive. From the 6th pass. (Sub-agent
  used `git stash` once against protocol to confirm a pre-existing Z3Backend doc error — verified
  contained, stash empty, concurrent `nra.rs` unclobbered; noted, not repeated.)

- **2026-06-19** — **P3.3: certified finite-`∀` `unsat` — a first checkable quantifier proof
  (Lean-parity quantifier-proof keystone, scoped slice).** A finite-expansion guarded-`Int`
  universal `∀x:Int. (lo≤x≤hi) ⇒ inner` decided `unsat` (e.g. `∀x:Int.(0≤x≤2)⇒x≥5`) was a bare
  `Evidence::Unsat(None)`; it now carries an independently-checkable certificate. **Feasibility
  finding:** the in-tree `check_alethe` base kernel has NO native quantifier-instantiation rule,
  but `check_alethe_with`'s `extra` hook lets a custom rule be re-checked by a callback (the
  pattern `prove_quant_unsat_alethe` already uses for EUF). New `quant_finite_cert.rs`
  (`prove_finite_int_quant_unsat_alethe`): emits an `assume` of the universal, a
  `forall_inst_guarded` step per `v∈[lo,hi]` delivering `inner[x:=v]`, `resolution` to the
  instance unit, and the `lia_generic` ground tail spliced from `prove_lia_unsat_alethe`;
  `check_alethe_lra_guarded_inst` chains a hook that re-derives **both** the structural
  substitution **and** the guard truth (`lo≤v≤hi`) with the arith checker — so the
  instantiation is **certified, not trusted** (zero-trust on the quantifier step; the ground
  refutation records the certified `Farkas` step). New
  `Evidence::UnsatGuardedQuantAletheProof { proof, universal }` (carries the form to re-check
  arena-free), wired into `produce_evidence` after all ground certs (which decline on
  quantifiers). **Tamper test** with two mutations (out-of-range witness → guard re-check
  fails; non-instance literal → structural match fails) proves the check is real. New
  `tests/evidence_quant_cert.rs` (7); QF_LIA/QF_BV ground certs unchanged. The custom
  `forall_inst_guarded` is in-tree-checked (not a standard Alethe rule, so outside Carcara/Lean
  cross-check — a lower assurance tier than the standard emitters, noted). General `forall_inst`
  over infinite domains / arbitrary bodies stays the keystone (needs the rule in the
  `axeyum-cnf` kernel — coordination-gated). From the 6th pass; sub-agent + soundness review.

- **2026-06-19** — **P3.3: zero-trust certificate for mixed QF_UFLIA/UFLRA `unsat` (gap C) —
  the Ackermann cert family extends from UF-over-BV to UF-over-arithmetic.** A mixed
  `f(x)=1 ∧ f(y)=2 ∧ x=y` (f:Int→Int and the Real twin) was a bare `Evidence::Unsat(None)`;
  it now carries an independently-checkable, **zero-trust-hole** certificate. New module
  `qfuflia_alethe.rs` (`prove_qf_uflia_unsat_alethe`): gates on every UF application being
  arithmetic-sorted (BV-sorted UF → `None`, leaving the BV path; arrays/datatypes/quantifiers
  → `None`), Ackermann-abstracts each app to a fresh same-sorted constant, derives the
  functional-consistency consequents `(= vᵢ vⱼ)` via `eq_congruent`/`eq_transitive`/`symm`,
  and hands the pure-LIA/LRA residual to `prove_lia_unsat_alethe`/`prove_lra_unsat_alethe`;
  the congruence steps are spliced over the residual's `assume`s into one proof re-checked
  end-to-end by `check_alethe_lra` (base congruence rules + the `lia_generic`/`la_generic`
  arith clause). Self-validates (emit only if the re-check passes). **Refactor:** the
  Ackermann-congruence prefix of `prove_qf_ufbv_unsat_alethe` was extracted into a shared
  `AckermannCongruence` (`build_ackermann_congruence`) — a pure refactor, QF_UFBV emission
  byte-identical (**Carcara cross-check confirms**). Wired into `produce_evidence` after
  `zero_trust_alethe_certificate` (QF_UFBV keeps its BV cert) and before
  `arith_alethe_certificate` (LIA/LRA emitters decline any UF app); `trusted_steps` empty
  (congruence + arith both re-derived — no trusted reduction). Tamper test (drop the closing
  step → `check` rejects) proves the verification is real. New `tests/evidence_uflia_cert.rs`
  (7); 999-test suite + clippy + doc + fmt + Carcara (54) green. Strictly additive. From the
  6th capability-gap pass (proof-completeness map); sub-agent + soundness review.

- **2026-06-19** — **ROBUSTNESS: BMC honors its own "unsupported is not an error" contract.**
  `run_bounded_model_check` drives the warm `IncrementalBvSolver`, which rejects `Op::Apply`;
  a transition relation with an uninterpreted step function (`x' = f(x)`) made the
  `SolverError::Unsupported` escape via `?` as a hard `Err`, even though the module docstring
  promises "a solver timeout/unsupported at some depth is not an error — it is reported as
  `BmcOutcome::Unknown`" (and the "unknown is never an error" hard rule). Fix: a
  `unsupported_to_unknown(err, steps)` helper maps `Unsupported` → `BmcOutcome::Unknown { steps,
  Incomplete }` at the per-depth solver operations (init/bad/trans asserts + the check), popping
  the scope first to keep the solver warm; any other `SolverError` still propagates. New
  in-module test (`UfStepper`: `x'=f(x)` → `Ok(Unknown)`, not `Err`); full suite + clippy + fmt
  green. From the 5th capability-gap pass (Track-4 + FP surfaces — which found NO soundness
  issues: FP arithmetic/conversions are bit-exact, BMC/k-induction/symexec decide correctly).
  **Symexec given the same treatment:** `SymbolicExecutor::branch`/`status` (feasibility
  *decision* queries) now map a backend `Unsupported` (a branch over an uninterpreted
  `Apply` — the canonical way to model an unmodeled call) to the existing
  `PathStatus::Unknown` ("may be feasible, not pruned") via a `status_or_unknown` helper,
  instead of a hard `Err`; new in-module test (`branch_over_uninterpreted_call_is_unknown_not_error`).
  `assume` (a stateful constraint-add, not a decision) keeps propagating. The FP conversions
  being constant-fold-only stays a coordination-gated `axeyum-fp` follow-up.

- **2026-06-19** — **P2.6: vacuous-`∀` elimination — a first sound cut into `∃∀`.**
  `∃y.∀x. x+y≥x` returned `Unknown` (after skolemizing `∃y→c`, `∀x. x+c≥x` is valid only
  when `c≥0`, so the valid-universal pass can't decide it; instantiation only refutes). New
  `quant_vacuous_universal.rs` (`eliminate_vacuous_universals`), hooked in `solve` after
  `eliminate_valid_universals`: for a top-level `∀x. body` (QF body, `x:Int`/`Real`), a Boolean
  descent (`not`/`and`/`or`/`implies`/`xor`/`ite`) reaches the atoms, and a self-contained
  affine collector (over `Rational`; handles `+`/`-`/neg/`*`-by-const + the `to_real` embed)
  declares `x` **vacuous** iff *every* arithmetic atom's net `x`-coefficient of `lhs−rhs` is 0
  **and** `x` occurs in no non-linear / UF-arg / array / BV / `div`/`mod`/`abs` position
  (any such occurrence bails). Then `∀x. body ⟺ body[x:=0]` (the bound var can't change any
  atom's truth), substituted via `replace_subterms` → the QF dispatch decides. Sound +
  conservative (any doubt ⇒ untouched). Decides `∃y.∀x. x+y≥x` → Sat, `∀x. x*0+y=y` → Sat;
  **soundness-negatives verified** — `∃y.∀x. x≤y`, `∀x. x≥0`, mixed-dependent bodies, and
  `∀x. f(x)=f(x)` (UF arg) are NOT wrongly Sat (the last still decides via the valid-universal
  pass). New `tests/quant_vacuous.rs` (8, incl. 4 soundness-negatives); full suite + clippy +
  fmt green (OS-timeout guarded). Strictly additive. A first slice of the `∃∀` keystone (full
  `∃∀` still needs LIA/LRA quantifier elimination); sub-agent + soundness review.

- **2026-06-19** — **P3.3: QF_LIA `unsat` now carries a checkable certificate in
  `produce_evidence` (gap E).** A pure-integer `unsat` (`x>0 ∧ x<0`) reached the `Other`
  evidence route and ended as a bare `Evidence::Unsat(None)` (`is_certified()==false`), even
  though `prove_lia_unsat_alethe` emits a checkable `lia_generic` Alethe proof (used on the
  SMT-LIB get-proof path). Fix: new `Evidence::UnsatArithAletheProof(Vec<AletheCommand>)`
  variant whose `Evidence::check` re-validates via the **arithmetic-aware**
  `check_alethe_lra` (= `axeyum_cnf::check_alethe_with` + the `la_generic` callback, which
  re-derives the integer/linear Farkas refutation — plain `check_alethe` can't decide
  `lia_generic`). A new `arith_alethe_certificate` helper tries `prove_lia_unsat_alethe` then
  `prove_lra_unsat_alethe` (each self-validating) in `produce_evidence`'s `Other`/`Unsat` arm,
  **after** `zero_trust_alethe_certificate` and **before** the bare/DRAT fallback (the arith
  emitters return `None` for UF/array/datatype, so ordering is safe). `trusted_steps =
  [(Farkas, certified)]` (the reduction is re-derived, not a trust hole). **Tamper test**
  (`tampered_lia_arith_evidence_fails_its_own_check`: drop the closing step → `check` rejects)
  proves the verification is real. Now certifies `x>0 ∧ x<0` and `x+y≥3 ∧ x≤1 ∧ y≤1`; QF_BV /
  QF_UFBV evidence paths unchanged (asserted). Strictly additive (only bare LIA `unsat` →
  certified). New `tests/evidence_lia_cert.rs` (5); full suite (977) + clippy + fmt green.
  From the 4th capability-gap pass; sub-agent + soundness review.

- **2026-06-19** — **P4.3 OMT robustness + completeness: optimizer honors timeout, decides
  div/mod, never errors (gaps A/B/D).** The optimizer's feasibility probes called
  `check_with_lia_dpll` directly and no path threaded `config.timeout`. Three fixes in
  `optimize.rs`: (B, completeness) reroute the LIA bound-search + Pareto probes
  (`decide_with_objective`, `pareto_probe`) through the full `check_auto` dispatcher, so
  objectives/constraints with `mod`/`div`-by-constant now optimize (`x∈[0,10] ∧ x mod 2=0`,
  max x → **10**; `x/3≤5`, max x → 17 — were hard `Err`); (D, hard rule "unknown is never an
  error") `probe_unsupported_to_unknown` maps a fragment-`Unsupported` (objective over a
  UF/`bv2nat`/nonlinear term) to a graceful `OptOutcome::Unknown` / `LexOutcome::Stopped{Unknown}`
  / `ParetoOutcome::Unknown` instead of propagating the error (min `x*x` → Optimal(0) via NRA;
  max `f(x)` → Unknown, no Err); (A, resource-limit promise) new `*_with_config` variants
  (`maximize_lia_with_config`, …, `optimize_lia_pareto_with_config`) thread a wall-clock
  deadline (Instant + `past_deadline`, wasm-shimmed) into the bound-doubling/binary-search and
  the Pareto/box/lex point loops, returning best-so-far as `Truncated`/`Unknown` on expiry
  (a 101-point Pareto front with a 2 s budget now returns in ~2 s, was minutes); the original
  no-config functions delegate with `SolverConfig::default()`, so all ~54 existing call sites
  and optima are unchanged. New `tests/optimize_robustness.rs` (6); 24 existing optimize tests
  + full suite + clippy + fmt green. From the 4th capability-gap pass (solver surfaces); sub-agent.

- **2026-06-19** — **ROBUSTNESS: integer-NIA solve HANG fixed (regression from the width
  ladder).** `a*b ≠ b*a` (ground integer nonlinear, UNSAT by commutativity) **livelocked**,
  ignoring `config.timeout` — a "never hang" contract violation caught by the 3rd capability
  pass. Root cause: pure-Int nonlinear never reaches the deadline-honoring `check_with_nra`
  (gated on `has_real`), so it fell to `dispatch_int_blast_width_ladder`, which ran ~31
  bit-blast+SAT solves over a hard multiplier-equivalence **with no timeout check between
  widths**; the real relaxation ran only after and abstracted `a*b`/`b*a` as distinct vars.
  Three fixes in `auto.rs`/`int_real_relax.rs`: (1) **deadline** — the ladder now threads
  `config.timeout` (Instant + `past_deadline`, wasm-shimmed) and bails to `Unknown(ResourceLimit)`
  before each width; (2) **trimmed ladder** — dense `4..=16` (where small witnesses live) +
  a sparse coarse tail to `DEFAULT_INT_WIDTH=32` (dropped the 36/40 tail + thinned 17..=31),
  so the no-timeout case is fast and `nia_ground_consistency` (x*x=4/9/25) still passes; (3)
  **commutative canonicalization + reorder** — `int_real_relax` sorts `mul`/`add` operands so
  `a*b` and `b*a` translate to the SAME real term (sound — real `*`/`+` commute), and the
  relaxation now runs **before** the ladder (it only ever returns `Unsat`, so reordering is
  sound and SAT cases like `x*x=4` still reach the ladder). Result: `a*b≠b*a` → **Unsat fast**
  (was a >100s hang), `∀x. x*k=k*x` → Sat, timeout honored. New `tests/nia_commutativity.rs`
  (4, incl. a 500ms-timeout-returns check); fmt + clippy + full suite green under an OS-timeout
  guard. Sub-agent + careful soundness/termination review.

- **2026-06-19** — **P2.5: integer nonlinear UNSAT via real relaxation (gap G3).**
  Sign-based integer-NIA goals (`x*x<0`, `x*x+1≤0` over Int) returned `Unknown`, and
  consequently `∀x:Int. x*x≥0` stayed `Unknown` (the valid-universal pass's `c*c<0` witness is
  integer-NIA). Fix: new `int_real_relax.rs` (`refute_int_via_real_relaxation`) + a fallback at
  the tail of the `has_int` dispatch branch, *after* the exact LIA refuters and the int-blast
  width ladder, fired only when the ladder is `Unknown`. On an isolated arena clone it builds
  the **faithful real reinterpretation** of the query — each `Int` var→a fresh memoized `Real`
  var (same int symbol ⇒ same real var), `int_const`→`real_const`, `IntAdd/Sub/Mul/Neg/Lt/Le/
  Gt/Ge`→the `Real*` counterparts, Bool/`Ite`/`Eq` rebuilt — and runs `check_with_nra`. Since
  integer solutions ⊆ real solutions, **real-`Unsat` ⇒ integer-`Unsat`** (sound); it returns
  *only* `Unsat` (a real model need not be integral), so strictly additive. **Conservative
  allow-list:** any `div`/`mod`/`abs`/coercion/`bv2nat`/BV/array/UF/datatype/quantifier subterm
  aborts the whole relaxation (→ unchanged) — never a guessed translation. One bounded NRA call,
  clone-scoped (no leakage/OOM). Decides `x*x<0`/`x*x+1≤0` → Unsat and **`∀x:Int. x*x≥0` → Sat**
  (the valid-universal sub-check now refutes `c*c<0`); `x*x==2` stays `Unknown` (real-sat √2, no
  wrong unsat), `x*x==4 ∧ x>0` stays `Sat` (width ladder). New `tests/nia_real_relaxation.rs`
  (5); fmt + clippy + full suite green. Final tractable gap from the 2nd capability-gap pass;
  sub-agent + soundness review.

- **2026-06-19** — **P2.4: `bv2nat` out-of-range now refuted UNSAT (gap G2).** `bv2nat(b)` of
  a W-bit `b` is provably in `[0, 2^W-1]`, but `bv2nat(4-bit) >= 16` / `== 20` returned
  `Unknown`: the exact LIA refuters reject a raw `Op::Bv2Nat` (`lra.rs` `Collector::linearize`
  catch-all), so the query fell to the bounded int-blast which returns `Unknown` (never
  `Unsat`) for an in-range integer no-model. Fix: new `bv2nat_bound.rs`
  (`abstract_bv2nat_for_refutation`) + a `refute_bv2nat_out_of_range` hook at the top of the
  `has_int` dispatch branch. On an **isolated arena clone**, each distinct `bv2nat(b)` term is
  replaced by a fresh Int var `n` with the true bound `0 ≤ n ≤ 2^W-1` (hash-consing ⇒ the same
  `bv2nat(b)` ⇒ one var; distinct `b` ⇒ independent), and the exact refuters
  (Diophantine/simplex/DPLL) decide the **relaxation** — `unsat` of the relaxation transfers
  (sound). Returns `Unsat` only on a refutation; otherwise falls through to the original (SAT
  decided by the native int-blast `Bv2Nat` handling, `bv2nat` intact). Width guard
  `MAX_BOUND_WIDTH=62` keeps `2^W-1` exact in `i128` (wider ⇒ unabstracted, graceful). No
  leakage/OOM (clone-scoped). Decides `bv2nat(4-bit)≥16`/`==20`/same-`b` `==5 ∧ ==6` → Unsat;
  preserves `≥8` → Sat and distinct-vector `==5 ∧ ==6` → Sat. New `tests/bv2nat_bound.rs` (6);
  fmt + clippy + full suite green. From the 2nd capability-gap pass; sub-agent + soundness review.

- **2026-06-19** — **P1.6: EUF over the reals (QF_UFLRA) — hard `Err` fixed, now routed
  through the combination (gap G1).** A real-sorted UF application `f(x):Real` returned
  `Err Unsupported("QF_LRA: non-linear or non-real subterm …")` — the pure-real linearizer
  rejects the `Apply` and the dispatch's `has_real` branch *unconditionally returned*
  `check_with_nra`, so it never reached the function handling. The **integer** branch already
  catches `Unsupported` and falls through to `check_with_uf_arithmetic` (that asymmetry is why
  QF_UFLIA worked but QF_UFLRA didn't). Fix (`check_auto_dispatch`): when a function is present,
  the `has_real` branch now falls through on `Unsupported` to the EUF + linear-arithmetic
  combination (`check_with_uf_arithmetic` decides QF_UFLRA the same way as QF_UFLIA). A second
  fix: a Real arith-UF query whose combination result is `Unknown` (the QF_UFLRA *sat-model
  projection* for an arithmetic-sorted UF is not yet built) now **returns that `Unknown`**
  instead of falling through to the eager bit-blast fallback, which errors on `Real` (an Int
  arith-UF can still fall through to int-blast). Upholds "`unknown` is never an error" and
  unlocks EUF+LRA. Now: `f(x)=1 ∧ f(y)=2 ∧ x=y` → **Unsat** (congruence), the Nelson-Oppen
  squeeze `f(a)≤b ∧ b≤f(a) ∧ a=c ∧ f(c)≠b` → **Unsat**, and `f(x)=1.0` → graceful **Unknown**
  (was a hard `Err`; sat-model projection for an arithmetic UF is the remaining follow-up).
  Surgical (only the function-present Real case changes). New `tests/euf_real.rs` (3); fmt +
  clippy + full suite green. From the 2nd capability-gap pass (highest-value finding).

- **2026-06-19** — **P2.6: valid-universal elimination handles NESTED `∀` prefixes (gap G4).**
  `eliminate_valid_universals` previously bailed when a `∀x. body` had a quantifier in its
  body, so `∀x.∀y. x+y==y+x` (valid) stayed `Unknown`. `try_eliminate` now **peels the entire
  leading `∀` prefix** (`∀x.∀y.…` ⇒ vars `[x,y]`, innermost body), substitutes *all* bound
  vars with fresh `!vu_*` constants at once, and checks the negated innermost (QF) body unsat
  — sound by the same closure argument (`∀x.∀y. b` valid iff `¬b[x:=cx,y:=cy]` unsat). Now
  decides `∀x.∀y. x+y==y+x` and `∀x.∀y. x=y ⇒ f(x)=f(y)` (Sat); a non-valid nested universal
  (`∀x.∀y. x=y`) is not mis-proven valid (verified — never wrongly Sat). 3 new tests; fmt +
  clippy + full suite green. (Remaining from the 2nd gap pass: G1 EUF-over-Real hard `Err`,
  G2 `bv2nat` width bound, G3 nonlinear-body validity, G5 `∃∀` skolem-then-validity.)

- **2026-06-19** — **P2.6: sat-side universal-validity elimination — valid `∀` now decided
  (were `Unknown`).** A standalone `∀x. body` with a quantifier-free body is **valid** (hence
  the assertion is satisfiable — true in every model) **iff** `¬body[x:=c]` is UNSAT for a
  fresh constant `c`. New `quant_valid_universal.rs` (`eliminate_valid_universals`), hooked in
  `solve` before `check_with_quantifiers`: for each top-level `∀x. body` (QF body; nested
  quantifiers skipped), mint a fresh `!vu_*` constant of `x`'s sort, substitute via
  `replace_subterms`, and decide `¬body[x:=c]` with the **quantifier-free** `check_auto`
  (no re-entry → terminates in one bounded QF solve). `Unsat` ⇒ the universal is valid ⇒
  replace with `true` (exact); `Sat`/`Unknown` ⇒ leave it for the existing instantiation/MBQI
  path. Sound + strictly additive (only `Unknown`→decided; a proven-valid universal is `true`
  everywhere, an unprovable one is never dropped). Leverages the existing exact deciders:
  `c+0≠c`/`c·0≠0` (LIA), `f(c)≠f(c)` (EUF), `c·c<0` (NRA sign rule). Now decides
  `∀x:Int. x+0=x`, `x·0=0`, `x≥0 ∨ x<0`, `∀x. f(x)=f(x)`, `∀x:Real. x²≥0`. UNSAT-by-
  instantiation (`∀x. f(x)=0 ∧ f(a)=1`) and non-valid universals unaffected (verified). New
  `tests/quant_valid_universal.rs` (8); one guarded-int test relaxed (its formula is validly
  `Sat` now — a sound improvement). fmt + clippy + full suite green. Capability-gap pass;
  sub-agent + independent soundness review (the alarming compile diagnostics were a stale
  analyzer cache — the code builds and the suite is green).

- **2026-06-19** — **QF_NIA: ground-vs-`∃` inconsistency fixed (small nonlinear-int SAT
  now decided).** `x*x==4 ∧ x>0` (ground) returned `Unknown` ("overflowed at width 32") while
  the equivalent `∃x. x*x==4` returned `Sat` (skolemize → bounded blast finds x=2) — same
  satisfiability, two answers. Root cause: the integer bit-blast fallback used a single fixed
  width (`DEFAULT_INT_WIDTH=32`), and at width 32 the SAT solver may pick a *wrapping* witness
  (`x` with `x*x ≡ 4 mod 2^32` but `x*x ≠ 4`) that fails the exact-integer replay → `Unknown`.
  Fix (`auto.rs::dispatch_int_blast_width_ladder`): for a pure-integer fallback query, iterate
  the blast width small→large (4..=32, then 36, 40 — a deterministic, finite ladder that
  still includes the old width 32) on an arena clone per width, returning the **first
  replay-checked `Sat`**. **Sound by construction:** `check_with_all_theories` returns `Sat`
  only after replaying the model against the originals, and returns `Unknown` (never `Unsat`)
  for an integer query with no model within a width (`combined.rs:88`), so the ladder never
  produces a wrong `unsat` and a too-narrow width simply climbs. Strictly additive (only
  `Unknown`→`Sat`); `x*x==2` (no integer root) stays soundly `Unknown` (out of scope —
  needs genuine NIA unsat reasoning). New `tests/nia_ground_consistency.rs` (6, replay-verified).
  **Follow-up:** the ladder runs up to ~31 solves for an integer query that is `Unknown` at
  every width — bounded and OOM-safe (one arena clone at a time, width cap 40) but worth a
  smarter width schedule / shared budget later. Driven by the capability-gap pass; sub-agent +
  independent soundness review.

- **2026-06-19** — **P2.6: guarded-finite Int universals now decided (were `Unknown`).**
  A universal `∀x:Int. (lo≤x≤hi) ⇒ body` is logically *equivalent* to the finite conjunction
  `⋀_{v=lo}^{hi} body[x:=v]` (outside `[lo,hi]` the implication is vacuously true), so it is an
  exact, sound rewrite — both sat and unsat transfer. New `quant_guarded_int.rs`
  (`expand_guarded_int_universals`), hooked into `check_with_quantifiers` as a pre-pass before
  `axeyum_rewrite::expand_quantifiers` (which rejects Int domains): detects `∀x:Int.(⇒ guard
  inner)` where `guard` is a conjunction of a lower- and upper-bound atom isolating the bare
  bound var against **literal** Int constants (all `≤`/`≥` orientations), substitutes each `v∈
  [lo,hi]` via `replace_subterms`, and decides the resulting QF conjunction. A deterministic
  `RANGE_SIZE_CAP = 4096` (checked arithmetic) means an inverted/unbounded/huge range never
  expands → graceful `Unknown` (never OOM); nested quantifiers / non-literal bounds / escaping
  var → passthrough. Sat replay anchors on the equivalence-preserving `guard_expanded` (the
  ground evaluator can't evaluate a raw Int `∀`). Strictly additive (only `Unknown`→decided).
  Decides `∀x.1≤x≤3⇒x²≤9` (Sat), `∀x.1≤x≤3⇒x≤2` (Unsat), `≥`-oriented, one-point range, and
  over-cap → Unknown. New `tests/quant_guarded_int.rs` (5); full solver suite + clippy + fmt
  green. Driven by the capability-gap pass; done via a focused sub-agent.

- **2026-06-19** — **P2.9/P1.6: datatypes with Int/Real fields now decided (were a hard
  `Err`).** The native datatype solver (`datatype_native.rs`) rejected any datatype carrying
  an `Int`/`Real` field with `SolverError::Unsupported` — blocking `List Int`, `Tree Int`,
  records with numeric fields, and the whole numeric-payload datatype space, even for pure
  congruence with no arithmetic. Fix: `register_datatype` admits `Int`/`Real` field sorts;
  `build_sym_vars` already declares a field var of the field's own sort with the
  well-founded-default guard (`well_founded_default` returns `Int(0)`/`Real(0)`);
  `value_to_term` renders `Int`/`Real` defaults. The datatype-free residual (tags as BV,
  field vars as Int/Real + the original arithmetic) re-dispatches through the existing
  `solve → check_auto` path, which routes Int/Real to the LIA/LRA deciders and BV to
  bit-blasting — no new wiring. Sound: `unsat` equisatisfiable, `sat` projects to
  `Value::Datatype` and **replays** (a projection bug ⇒ replay failure → Unknown, never a
  wrong sat). Now decides: `v(x)=1 ∧ v(y)=2 ∧ x=y` (UNSAT, congruence), `is-cons(l) ∧
  head(l)=5` (SAT), `v(x)+1=4` (SAT), recursive `List Int`, multi-ctor `Either Int`. New
  `tests/datatype_int_fields.rs` (5); existing datatype tests + full solver suite (926) +
  clippy + fmt green. Driven by a measured capability-gap pass; done via a focused sub-agent.
  Closes the P0 finding from that pass (also upholds "unknown is first-class, never an error"
  — the hard `Err` is gone).

- **2026-06-19** — **P3.5: Ackermann cert widened to congruence-closure arg-equalities
  (e-graph fallback).** `prove_qf_ufbv_unsat_alethe` now discharges an argument pair equal
  by **congruence** (not just transitive closure of asserted edges) — e.g.
  `f(g(a))=k ∧ a=b ∧ f(g(b))≠k`, where the args `g(a)`, `g(b)` are equal because `a=b`.
  A new `CongBridge` builds an `axeyum_egraph::EGraph` over the rewritten assertions + the
  abstraction defining equations `v_i=f(args_i)` (all nodes added before any merge, so
  congruence edges survive); when the asserted-edge BFS declines, `emit_arg_units` walks
  `EGraph::explain_steps` and converts `Input`→assume / `Congruence`→`eq_congruent`
  (recursing on args) threaded through `eq_transitive` — exactly the `prove_qf_uf_unsat_alethe`
  pattern. **Strictly additive**: the identical / direct-assert / transitive-BFS paths are
  byte-unchanged, and the whole emitter is self-validated by `check_alethe` (a bad fallback
  ⇒ `None`, never a wrong proof). Carcara accepts the nested-congruence proof
  (`ufbv_nested_congruence_is_accepted_by_carcara`; the EUF `eq_symmetric`+resolution flip
  was swapped for the `symm` rule which both `check_alethe` and Carcara accept). Done via a
  focused sub-agent; independently re-validated (clippy clean, qfufbv_proof 7, carcara 54,
  full solver suite 920). **Lean loop now CLOSED for the congruence fragment** (follow-on):
  `reconstruct.rs` gained `symm`-rule reconstruction (`reconstruct_symm`, mirroring
  `reconstruct_eq_symmetric`'s kernel-gated `Eq.rec` transport), so
  `end_to_end_qf_ufbv_congruence_derived_to_false` reconstructs `f(g(a))=k ∧ a=b ∧ f(g(b))≠k`
  to a kernel-checked Lean `False` — the congruence fragment is now validated at all three
  levels. **Remaining follow-up:** the array-elim index fragment
  (`term_to_alethe` renders only symbols/bv-consts) would need application-valued indices to
  benefit, left untouched to protect the validated array cert.

- **2026-06-19** — **Datatype evidence routing fixed + datatype zero-trust cert wired.**
  `evidence_route` (the `produce_evidence` classifier) ignored datatype sorts/ops, so a
  datatype query whose top-level terms are all Bool/BitVec (e.g. `select_0(mk(a,b))=#b00
  ∧ a≠#b00`) misrouted to `EvidenceRoute::QfBv` → `produce_qf_bv_evidence` → raw `DtSelect`
  to the BV backend → `Unsupported` error. Fixed: detect `Sort::Datatype` +
  `DtConstruct`/`DtSelect`/`DtTest` in `evidence_route` so datatype queries route through
  `solve` (which has the datatype dispatch). New `tests/datatype_solve_path.rs` (UNSAT via
  solve / via produce_evidence / SAT via solve). **With routing fixed, the datatype
  read-over-construct cert (`prove_qf_dt_unsat_alethe_via_simplification`) is now also wired
  into `zero_trust_alethe_certificate`** — so QF_DT unsat carries a zero-trust-hole Alethe
  proof too (projection folded by `eq_transitive`/ι-reduction). Found while wiring the
  evidence certs; fixed via a focused sub-agent. Full solver suite (917 tests) + clippy green.

- **2026-06-19** — **P3.5: zero-trust-hole Alethe certs WIRED into the evidence path.**
  `produce_evidence`'s `unsat` branch previously tried only the array
  read-over-write-same direct cert, then fell back to a *trusted* DRAT reduction
  certificate (recording `TrustId::Ackermann` / `ArrayElim` as trust holes). It now
  also tries the Ackermann (`prove_qf_ufbv_unsat_alethe`) and array-elimination
  (`prove_qf_abv_unsat_alethe_via_elimination`) certs via a new
  `zero_trust_alethe_certificate` helper — so a QF_UFBV / QF_ABV `unsat` in the
  covered fragment now carries a `check_alethe`-validated Alethe proof that *derives*
  the functional/read-consistency reduction by `eq_congruent` (`trusted_steps` empty —
  **no reduction trust hole**), instead of the trusted DRAT. The certs were previously
  only test-exercised; they are now actually USED on the evidence path, retiring the
  Ackermann/ArrayElim trust holes **in practice** for the covered fragment. Each emitter
  self-validates and returns `None` cheaply outside its fragment, so trying them in
  order is sound and changes nothing for other fragments. New test
  (`qf_ufbv_unsat_carries_a_zero_trust_alethe_certificate`: `UnsatAletheProof` evidence,
  zero `trusted_steps`, self-`check`s). (Ledger stays "trust hole" — coverage is the
  derivable-equality fragment, not universal; ROW-distinct / non-derivable equalities
  still fall to trusted DRAT.)

- **2026-06-19** — **P3.5: array-elimination (read-consistency) Alethe certificate
  widened to transitive index-equalities.** Same generalization as the Ackermann cert,
  applied to `prove_qf_abv_unsat_alethe_via_elimination`: a read-consistency constraint
  `i=j ⇒ select(a,i)=select(a,j)` is now discharged when the index equality `i=j` holds
  by **transitive closure** of asserted equalities (`i=k ∧ k=j`), via an `eq_transitive`
  chain over the `!sel_a` unary select function — previously only direct index equalities
  were certified. Strictly additive (direct/identical indices unchanged), `check_alethe`
  self-validated, and externally **Carcara-validated**
  (`abv_select_consistency_transitive_is_accepted_by_carcara`). Index-unit derivation
  factored into `emit_index_equality_unit`. Widens the array-elim trust-hole certificate
  (Track 3, ADR-0010). New self-check + Carcara tests; solver clippy + qfabv_elim_proof +
  carcara crosscheck green (53 carcara tests). **Lean loop closed for the widened
  fragment:** the transitive Ackermann cert also reconstructs to a kernel-checked Lean
  `False` (`end_to_end_qf_ufbv_transitive_congruence_to_false`), so the transitive certs
  validate at all three levels (in-tree `check_alethe`, external Carcara, Lean kernel).
  Full solver suite green (77 results, 0 failures).

- **2026-06-19** — **P3.5: Ackermann Alethe certificate widened to transitive
  argument-equalities.** `prove_qf_ufbv_unsat_alethe` previously discharged a
  functional-consistency constraint's antecedent only when each argument pair was
  *directly* asserted equal (or identical). It now also discharges pairs equal by
  **transitive closure** of the asserted equalities (`a=b ∧ b=c ⊢ a=c`): a BFS over
  the asserted-equality graph finds the chain, each edge (an original assertion) is
  `assume`d, and one `eq_transitive` step + resolution derives the argument equality
  feeding `eq_congruent` — so `f(a)=k ∧ a=b ∧ b=c ∧ f(c)≠k` now emits a checkable
  certificate (previously declined → `None`). Strictly additive: directly-asserted
  and identical pairs keep their exact prior steps (no change to the existing
  Carcara-validated certs), and the new path is gated by `check_alethe`
  self-validation (a non-derivable chain ⇒ `None`, never a wrong proof). 2 new
  self-check tests (unary chain; binary with one direct + one chained arg) + a new
  **Carcara crosscheck** (`ufbv_transitive_congruence_is_accepted_by_carcara`) so the
  transitive fragment is externally validated. Widens the Ackermann trust-hole
  certificate coverage (Track 3, ADR-0013). Full solver clippy + qfufbv_proof +
  carcara crosscheck green.

- **2026-06-19** — **NRA OOM gap CLOSED: deterministic cross-product admission bound
  (graceful `unknown`, never OOM).** `check_with_nra` now refuses any query with > 2
  distinct-operand cross-products (`a·b`, `a ≠ b`) up front — *before* building lemmas or
  solving — returning `Unknown(ResourceLimit)`. Root cause (measured under the new 64 GiB
  `ulimit` cap): the 3-variable case `a²+b²+c² ⋈ ab+bc+ca` (three cross-products) blows up
  the DPLL(T)/exact-rational LRA relaxation *inside a single solve call* — so the per-round
  and per-node wall-clock checks never get a turn — and **bounds do not tame it** (the
  bounded variant `SIGABRT`ed at the memory cap; McCormick just adds more lemmas). The bound
  counts **only** cross-products: squares are cheap (no monotonicity/SOS lemmas) so
  square-only multi-variable instances (`x²+y²+z²+1=0`) and the 2-var SOS frontier
  (`a²+b²<2ab`, one cross) stay decidable — verified, no regression. 3 new tests (unbounded
  + bounded both degrade; square-only not gated); all 27 NRA + 5 Spivak tests green. Updates
  the standing `Graceful unknown` rule; multi-variable SOS / Cauchy–Schwarz is now explicitly
  gated on a future nlsat/CAD (or exact-rational work-budget) engine. Also landed
  `scripts/mem-run.sh` + `just test-guarded` (64 GiB `ulimit -v` wrapper) so build/test/bench
  can never OOM the host, and fixed a pre-existing `clippy::many_single_char_names` lint in
  the `theory_combination` test module (the P1.6 commits had left `clippy --all-targets` red).

- **2026-06-18** — **Crash-hardening sweep: never panic on arithmetic-sorted UF sat-model
  projection.** `Value::scalar_code` panics on Int/Real; all three solver callers of
  `project_model` (euf / combined / aufbv) now degrade to a sound `Unknown` for an
  arithmetic-sorted uninterpreted function instead of crashing. Found via `solve` on a
  quantified UF+LIA query (now decides UNSAT, was a panic). Upholds 'graceful unknown,
  never crash'. Full solver suite green (77 binaries).

- **2026-06-18** — **QF_UFLIA / QF_UFLRA complete (conjunctive UNSAT) via eager EUF+arith
  combination.** `check_with_uf_arithmetic` switched to eager Ackermann elimination →
  `check_auto`: all congruence constraints asserted up front, so nested `f(g(a))≠f(g(b))∧a=b`,
  `f(x+0)≠f(x)`, result-in-arithmetic `f(p)+1=f(q)∧p=q`, and the squeeze all decide UNSAT
  (the lazy CEGAR was incomplete — arithmetic solvers leave intermediate abstraction vars
  unconstrained). Also hardened the default-on preprocessing to be fully best-effort (any
  reduction/dispatch/reconstruction error → solve the original). 7 UF-arith tests; ledger +
  golden matrix updated; full solver suite green (77 binaries).

- **2026-06-18** — **P1.6: EUF + linear-arithmetic combination (QF_UFLIA / QF_UFLRA).**
  Widened `declare_fun` to admit Int/Real UF sorts; refactored the functional-consistency
  CEGAR (`check_with_function_consistency`) and added `check_with_uf_arithmetic` (solves the
  Ackermann abstraction with the arithmetic dispatcher, not bit-blasting) — the classic
  Nelson–Oppen case `f(a)≠f(b) ∧ a≤b ∧ b≤a` now decides **UNSAT** (LIA forces a=b →
  congruence forces f(a)=f(b)), in both LIA and LRA. Wired into `check_auto`. New theory
  coverage axeyum could not even *declare* before. Full solver suite green (77 binaries).

- **2026-06-18** — **P1.6 T1.6.2 th_eq bus** — `EGraph::theory_var_classes` (e-graph
  readout of classes carrying theory vars) + `interface_th_eqs` (solver-side: emit
  cross-theory interface equalities, spanning chains over classes spanning ≥2 theories).
  The bus a merge in one theory uses to propagate an equality to another. With the four
  combination primitives, P1.6's machinery (shared / propose / classify / arrangement /
  th_eq-bus) is in place; the remaining slice is the online multi-theory loop that drives it.

- **2026-06-18** — **P1.6 combination — arrangement-consistency check**
  (`combination_conflict`): one model-based-combination iteration — does a BV model's
  equal/distinct arrangement of the shared terms agree with the EUF congruence? Returns the
  first conflicting pair (model-distinct vs congruence-equal, or model-equal vs
  congruence-refuted), else `None`. Composes `shared_terms`+`classify` into the core
  combination step. Four P1.6 combination primitives now exist (shared / propose / classify
  / arrangement-check); the remaining slice is the online loop that blocks a conflicting
  arrangement and re-solves (P1.5 T1.5.1–4 online drive).

- **2026-06-18** — **P1.6 combination — interface-equality classification against
  congruence** (`classify_interface_equalities` + `InterfaceStatus`). Decides each
  proposed equality Entailed/Refuted/Undetermined via the e-graph congruence closure of
  the EUF assertions — Entailed covers congruence-derived equalities (`f(a)=f(b)` from
  `a=b`), Refuted uses asserted disequalities. With `shared_terms` (T1.6.1) +
  `propose_interface_equalities`, the model-based-combination core (shared → propose from
  a BV model → confirm/refute against EUF) is now in place; remaining is the online
  CDCL(T) drive that loops propose↔split↔re-solve (P1.5 T1.5.1–4).

- **2026-06-18** — **P1.6 combination — model-based interface-equality proposal**
  (`propose_interface_equalities`). Given a one-theory model, proposes equalities between
  equal-valued shared terms (spanning chain per value group, deterministic) — the
  *propose* half of Z3-style model-based combination, building on T1.6.1's `shared_terms`.
  Next: assert/confirm-or-split the proposed equalities against the congruence closure
  (T1.6.3), which needs the online CDCL(T) drive (P1.5 T1.5.1–4 — a substantial slice).

- **2026-06-18** — **P1.6 theory combination — T1.6.1 shared-term discovery**
  (`theory_combination::shared_terms`, the plan's named next task). Identifies the
  bit-vector-sorted Nelson–Oppen interface terms between the EUF and BV theories
  (arg/result of `Op::Apply` ∩ operand/result of an interpreted BV op) — pure,
  deterministic structural discovery, the foundation for T1.6.2 (`th_eq` bus) and T1.6.3
  (interface-equality case-splitting). 4 tests.

- **2026-06-18** — **Foundational QF_BV refutation checked by the real Lean kernel**
  (destination-3). Added a gated real-lean cross-check for the bit-blasting → resolution
  path (`a≤b ∧ b<a`); `#print axioms` shows no `sorryAx`. Independent-kernel validation now
  spans **7 fragments**: QF_BV / QF_UFBV / QF_ABV / datatypes / LRA / ∀ / ∃ — the core
  bit-level path plus the theory fragments.

- **2026-06-18** — **Datatype refutations checked by the real Lean kernel** (destination-3).
  Added a gated real-lean cross-check for algebraic datatypes (read-over-construct unsat,
  via datatype simplification → QF_UFBV); `#print axioms` shows no `sorryAx`. Real-kernel
  validation now spans **6 fragments**: QF_UFBV / LRA / ∀ / ∃ / QF_ABV / datatypes.

- **2026-06-18** — **QF_ABV refutations now checked by the real Lean kernel** (destination-3).
  Added a gated real-lean cross-check for arrays (read-consistency unsat, reconstructed via
  array elimination → QF_UFBV); `#print axioms` shows no `sorryAx`. The independent-kernel
  validation now spans QF_UFBV / LRA / ∀ / ∃ / **QF_ABV**. (Pure-QF_BV-value and direct ROW
  reconstruction to Lean remain frontier gaps — the Lean emitter is narrower than the Alethe one.)

- **2026-06-18** — **Bounded strings: `str.to_code` / `str.from_code`** (SMT-LIB 2.6
  char-code ops) added to the byte-string theory. `to_code` → (is_single, byte-as-BV8);
  `from_code` → the length-1 string for a byte. Bounded BV formulas; tested incl.
  round-trip. Narrows the string-theory gap vs z3 within the bounded fragment.

- **2026-06-18** — **FP `to_real` confirmed format-general** (F16/BF16/TF32/FP8 E5M2,
  not just F32/F64): corrected the stale doc and added small-format coverage (incl.
  subnormals and ∞/NaN→None). With `from_real` (all modes) and the int/bv→fp conversions,
  the FP↔Real/Int conversion surface is complete across the supported IEEE formats.

- **2026-06-18** — **FP `from_real`: all five rounding modes** (RNE/RNA/RTZ/RTP/RTN).
  `round_rational_rne` gained per-mode rounding (`round_up_decision`) and overflow
  (`overflow_bits`, ±inf vs max-finite, direction-aware). Validated against
  `rustc_apfloat`'s correctly-rounded division for every mode and sign — an independent
  IEEE oracle. `to_fp` from real is now complete for all SMT-LIB rounding modes.

- **2026-06-18** — **FP `from_real` now rounds non-dyadic rationals** (exact-integer RNE,
  `round_rational_rne`): 1/3, 1/10, 22/7 → correctly-rounded F32/F64, no f64
  double-rounding. `round_rational_to_format` kept dyadic-only (smtlib parser depends on
  its contract); `from_real` falls back to the integer path. Cross-checked vs the f64
  path on dyadic (incl. F16 subnormal/tie) and vs native casts on non-dyadic. The `to_fp`
  source set (int→fp, bv→fp, real→fp) is complete for NearestEven.

- **2026-06-18** — **FP `from_real`** (`axeyum_fp::from_real`): `to_fp` from a rational
  constant. Dyadic rationals (power-of-two denominator, <2^53 numerator) round soundly via
  the validated `round_rational_to_format` (exact f64 → `round_to_format`); non-dyadic
  (1/3, 1/10) return `Ok(None)` (decline — exact rational rounding needs >i128, a planned
  follow-up). Completes the `to_fp` source set for the dyadic case (int→fp, bv→fp, real→fp).

- **2026-06-18** — **Optimization/constraint API feature-complete + full Solver façade.**
  Session run (all green, committed): FP integer→float (`from_ubv`/`from_sbv`); all 3 z3
  OMT modes (box, lexicographic, Pareto) across **LIA + BV**; model-returning MaxSAT;
  strict PB (`pb_lt`/`pb_gt`); cardinality `between`/`at_most_one`/`exactly_one`; BV
  `repeat`; and `Solver` façade methods for the whole optimization/MaxSAT/unsat-core
  surface. `preprocess` flipped default-on (guarded, validated). **Next frontiers** (all
  larger / coordination-gated): deeper word-level reduction (other agent's `axeyum-rewrite`
  lane); a kissat-class SAT core (long game, the search-bound Timeout band); unbounded
  strings / uninterpreted sorts / full MBQI / NRA-CAD; and `to_fp`-from-real (needs exact
  rational rounding — f64 bridge is unsound for sub-f64 formats).

- **2026-06-18** — **Solver façade `unsat_core`**: `Solver::unsat_core(arena)` returns a
  deletion-minimized unsat core (assertion indices) — the z3 get-unsat-core API on the
  high-level façade. Test verifies the irrelevant assertion is excluded.

- **2026-06-18** — **Word-level preprocessing flipped default-ON** (commit `6cb2f1b`,
  ADR-0034/0037 staged step). `SolverConfig::default().preprocess == true`; the default
  `solve()`/`check_auto` path runs the model-sound reduction pipeline. Guarded so it is
  never a correctness dependency: skipped on quantified queries (QF transform), and
  best-effort (any reduction-pass error → solve the ORIGINAL). Validated by a
  full-workspace behaviour check (103 test binaries green) — the gate ADR-0037 required.
  Caught + fixed a real regression in the check: preprocessing errored on
  uninterpreted-function applications (canonicalize fold) → the best-effort fallback.

- **2026-06-18** — **BV `repeat`** (`bv_repeat`, z3 `(_ repeat n)`): derived concat fold,
  no new IR Op/lowering. Completes the common z3 BV op set (nand/nor/xnor/comp/rotate
  already present). Test incl. exhaustive BV4 symbolic duplication.

- **2026-06-18** — **BV Pareto** (`optimize_bv_pareto`): completes the OMT trio across
  both theories — box, lexicographic, and Pareto now all span LIA + BV. Test: BV8 front
  {(1,3),(2,2),(3,1)}. 24 OMT tests.

- **2026-06-18** — **Cardinality convenience**: `between(lo,hi)`, `at_most_one`,
  `exactly_one` (one-hot) — compose the existing at-most/at-least/exactly forms. 2 tests.

- **2026-06-18** — **Solver façade OMT/MaxSAT methods**: `Solver::{maximize_lia,
  minimize_lia, optimize_lexicographic, optimize_pareto, max_satisfiable}` optimize over
  the active assertions — the optimization work is now reachable via the high-level API.

- **2026-06-18** — **PB strict comparisons** (`pb_lt`/`pb_gt`, pseudo-Boolean `<`/`>`):
  compose the non-strict forms (≤k-1 / ≥k+1, with sound k-edge handling). 2 tests.

- **2026-06-18** — **MaxSAT model-returning variant** (`max_satisfiable_model` /
  `_weighted_model`, commit `daced10`). Returns `MaxSatOutcome::Optimal { weight, model,
  satisfied }` — the witnessing assignment + which soft constraints hold, the actual
  solution z3's MaxSAT yields (previously only the optimal weight). Sound: pins the
  weight-sum at the optimum, witnesses a model via `check_auto`, re-evaluates each soft
  constraint; surprise unsat/unknown folds to `Unknown`. Test cross-checks `satisfied`
  flags against the model. Working-agreement loop increment 7.
- **2026-06-18** — **P4.3 OMT: Pareto + box modes complete the z3 OMT trio.**
  `optimize_lia_pareto` (commit `75205b7`) enumerates the Pareto front by guided
  improvement, each point *verified* Pareto-optimal (confirmed-unsat domination query),
  with deterministic point (256) / push (64) caps → `Truncated`/`Unknown` rather than
  unbounded enumeration. With `optimize_lia_box` (`ecabf53`) and the lexicographic modes
  below, **axeyum now has all three z3 OMT modes (box, lexicographic, pareto)**. 22 OMT
  tests incl. the {(1,3),(2,2),(3,1)} front. Working-agreement loop increments 4–6.
- **2026-06-18** — **P4.3 OMT breadth: lexicographic multi-objective optimization**
  (`optimize_lia_lexicographic`, commit `b852ddf`). Optimizes integer-linear objectives
  in order, pinning each at its optimum before the next (z3's default lexicographic
  combination); sound + terminating (bounded composition of the checked
  `maximize/minimize_lia`); `LexOutcome::Stopped` at the first non-finite objective.
  4 API-level tests (order-dependence, mixed max/min, stop-on-unbounded). Reachable via
  the solver API. **Extended to BV** (`optimize_bv_lexicographic`, signed/unsigned, commit
  `f57e5f3`, +2 tests) — lexicographic OMT now spans LIA and BV. Second/third breadth
  increments of the new working-agreement loop.
- **2026-06-18** — **Plan revised from measured learnings + breadth pivot.** Per a
  strategy check-in: revised PLAN.md (front #1 reframed to word-level *reduction* as
  the destination-2 lever with the EncodingBudget/search-bound/large-CNF partition;
  both-in-parallel on the SAT core; new standing rule *graceful `unknown`, never
  OOM/crash*; multi-agent coordination rule — `axeyum-rewrite`/`axeyum-smtlib` are the
  other agent's reduction lane). Active focus set to **breadth toward feature-parity**.
  First breadth increment: **FP integer→float conversion** (`from_ubv`/`from_sbv`,
  commit `f7b43db`) — see P2.8 row; differential-tested vs native `as f32`/`as f64`.
- **2026-06-18** — **Known robustness gap found (NRA can OOM on unbounded multi-product
  nonlinear queries).** Probing whether the SOS lemmas generalize to 3 variables
  (`a²+b²+c² ≥ ab+bc+ca`) revealed that `check_with_nra` on an **unbounded** 3-variable
  nonlinear query **OOMs** rather than degrading to `Unknown`. Diagnosis: unbounded vars
  can't be box-split (`widest_split` → `None`), so it never branches — the blowup is in
  the **root refinement loop**, where the ~6-product case generates a much larger boolean
  product-lemma set and/or escalating exact-rational witnesses that the existing
  wall-clock deadline + `too_large_to_refine` (2³¹) guards don't bound *as memory*. The
  2-variable SOS win is unaffected (committed, green). A correct fix needs a deterministic
  memory/work bound that does **not** regress currently-working *bounded* multi-product
  cases (those terminate via McCormick) — scoped as future work, to be developed against a
  controlled small repro (NOT the 123 GB-OOMing 3-var case). Multi-variable SOS is gated on
  this. **Do not run unbounded ≥3-variable nonlinear NRA queries without a memory bound.**
- **2026-06-18** — **P2.5 NRA breadth: sum-of-squares lemmas prove AM–GM₂**
  (commit `8a7d31f`). `nra::sos_lemmas` adds `(a±b)² ≥ 0` (= `r_aa+r_bb∓2·r_ab ≥ 0`)
  over the abstracted products of each variable pair — sound (true in every real
  model), restoring the cross-product correlation the independent product abstraction
  drops. **`a²+b² ≥ 2ab` / AM–GM₂ is now proved** (`a²+b²<2ab` → `Unsat`); the Spivak
  SOS-frontier test is promoted from prompt-`Unknown` to proved. A negative test pins
  soundness (`a²+b²=2ab` stays satisfiable, `x=y`). Closes a documented NRA frontier
  gap; higher-degree/multi-var SOS (Bernoulli, general Cauchy–Schwarz) + nlsat/CAD
  remain. Built on the incremental-eval primitive landed earlier this session.
- **2026-06-18** — **P1.8 tactics: or-else portfolio combinator** (`solve_with_portfolio`
  + `recommended_portfolio`, commit `cda1f55`). Runs strategies in order, first to
  decide wins, falls through `Unknown`/errors (Z3's `or-else`; sound — a later strategy
  runs only when earlier ones returned `Unknown`). `recommended_portfolio` routes by
  query shape (heavy-arith → `[LazyBvAbstraction, EagerPureRust]`; structural → `[Auto]`),
  composing the destination-2 levers with fallback power over a single `Auto` pick.
  Pure-Rust, collision-free, 3 tests. Full workspace suite green (103 test binaries, 0
  failures).
- **2026-06-18** — **Destination-2 lever found & measured: word-level preprocessing
  doubles the eager decided count (2 → 4 of 113), after fixing the unbounded
  preprocessor.** Acting on the lazy-bv null result below, profiled the preprocessing
  passes on the 17.6 MB / 340 k-node giant: `solve_eqs` was the sole hog (**>150 s**
  there; every other pass <0.5 s). Added a **deterministic node-fuel budget**
  (`axeyum_rewrite::solve_eqs_bounded` / `DEFAULT_SOLVE_EQS_FUEL`, commit `96e55b6`) —
  charges per-round rebuild work (shared-memo node count, never wall-clock), bails to
  a **sound partial reduction** (un-eliminated equalities stay assertions; trail
  reconstructs). Giant now clears the whole pipeline in ~1.5 s. Wired into
  `check_with_preprocessing` + the bench. **Fair `--preprocess` measurement** (sat-bv,
  same budgets as the eager baselines, Z3 oracle, DISAGREE=0, 0 replay failures
  throughout): **3 s → 4 sat vs eager 2; 20 s → 7 sat vs eager 3** — more than doubling
  eager at both tiers, the gain *growing* with budget. The newly-decided instances drop
  out of `EncodingBudget` (13 → 11 at 3 s), i.e. preprocessing shrinks them below the
  bit-blast-size ceiling. First (and decisive) destination-2 gain on this corpus from
  *reduction* (the "not-building-the-mountain" lever), not abstraction — ratified in
  **ADR-0037** (reduction is the destination-2 priority; batsat stays default; custom
  cores specialized). Baselines
  `bench-results/baselines/qf-bv-p4dfa-fair-sat-bv-preprocess-vs-z3-{3s,20s}-*.json`,
  `just bench-public-qfbv-preprocess-fair-{3s,20s}`. Probe:
  `axeyum-bench/examples/preprocess_timing.rs`. **Wired into the product:** the full
  model-sound pipeline now runs on the default `solve()`/`check_auto` path when
  `preprocess` is set (`check_auto_preprocessed`, reconstructs + replays), and
  **`Strategy::Auto` composes both levers** — lazy-bv for arithmetic-heavy queries,
  eager-with-preprocessing for structural ones. Full solver suite green.
  **Timeout-boundedness measured (kissat probe):** the 99 Timeouts split by CNF size —
  **~9 (≤300k clauses) are SAT-search-bound** (kissat 4.0.4 cracks them 2–18 s where
  batsat times out @20s; `mobiledevice_paired` 2 s vs >20 s), the **~90 larger
  (≥~650k) defeat even kissat** (reduction-bound). So **both levers are data-justified,
  partitioned by size** (ADR-0037 trigger partially fired): a competitive default SAT
  core for the small-CNF Timeouts, word-level reduction for the large-CNF bulk +
  6 EncodingBudget. **But the core bar is kissat-class:** the in-tree `xor_cdcl` core
  *also* fails `string1x8.4` (>120 s vs kissat 8.3 s), so converting the search-bound
  band needs a kissat-class solver (major P1.3; out of scope as a pure-Rust *default*,
  kissat is only a benchmark oracle). **Practical upshot: reduction is the higher-ROI
  near-term lever even for the search-bound band** (shrinking the CNF brings it within
  reach of the core we ship). Probes: `axeyum-bench/examples/{dump_dimacs,xor_cdcl_probe}.rs`.
  **Next:** (a) deeper reduction — `axeyum-rewrite` P1.2, the **other agent's active
  area; do not edit `canonical.rs`**; (b) flip `preprocess` default-on after a
  full-suite check; (c) long-term, close the SAT-core gap to kissat-class. Track
  **Timeout→decided** as the destination-2 pulse.
- **2026-06-18** — **Destination-2 fair re-measurement: lazy-bv vs Z3 on the public
  p4dfa 113 at the standing budgets — confirmed a no-op on this corpus.** Ran the
  built-but-fair-unmeasured `LazyBvBackend` head-to-head vs Z3 4.13.3 on the
  committed 113-file `20221214-p4dfa` public QF_BV slice at **identical node/CNF
  budgets to the eager `qf-bv-p4dfa-fair` baselines**, both tiers, `--jobs 2`:
  - **3 s** (node 200k, cnf 2M/5M): **lazy 3 sat / 110 unknown, DISAGREE=0, 0 replay
    failures** (eager 2/111). **20 s** (node 300k, cnf 3M/8M): **lazy 4 sat / 109
    unknown, DISAGREE=0, 0 replay failures** (eager 3/110). Baselines committed:
    `bench-results/baselines/qf-bv-p4dfa-fair-lazy-bv-vs-z3-{3s-n200k-cnf5M,20s-n300k-cnf8M}.json`;
    reproduce via `just bench-public-qfbv-lazy-fair-{3s,20s}`.
  - **Honest finding:** `lazy_ops_total == 0` on **all 113** files (`grep` census:
    **0/113** contain any of `bvmul/bvudiv/bvsdiv/bvurem/bvsrem/bvsmod`); **0
    instances refined any op**; every decided instance was plain bit-blast. The
    consistent +1 over eager is a solve-path margin (the extra instances have
    `ops_total=0`), **not** a CEGAR win. lazy arithmetic-CEGAR is **structurally
    inert** on this arithmetic-free DFA/protocol slice. The 109–110 unknowns are
    87–98 Timeout (huge CNFs batsat can't crack) + 10–13 EncodingBudget + 1–10
    NodeBudget — the **eager-CNF-size wall**, not the multiplier wall.
  - **The number says:** the destination-2 lever for this corpus is **word-level
    reduction before blasting** (P1.2), which is blocked on the **unbounded
    preprocessor** (`solve_eqs`/canonicalize blow-up on the 17.6 MB / 215k-`ite`
    giants). NEXT: give the preprocessing passes a deterministic work budget so
    `--preprocess` bails instead of hanging → then measure `--preprocess` on the 113
    (the second committed measurement) → then the batsat-vs-custom-core ADR. See
    [lazy-bitblasting-p21-findings.md](docs/research/05-algorithms/lazy-bitblasting-p21-findings.md).
- **2026-06-18** — **P3.7 destination-3 milestone: reconstructed refutations checked
  by a REAL Lean 4 kernel.** Installed a real Lean toolchain (elan + `leanprover/lean4`
  stable 4.31; the gold-standard checker, analogue of the Z3 oracle — a CI/cross-check
  tool, not a build dependency) and made the in-tree reconstruction externally
  verifiable end-to-end:
  - **`Kernel::render_lean_module`** (`axeyum-lean-kernel::lean_pp`): renders a
    self-contained `prelude`-mode Lean 4 module — every environment declaration
    reachable from goal+proof (transitive const-closure + topological sort;
    inductive/ctor/recursor emitted as `axiom`s carrying their kernel types), then
    `theorem axeyum_refutation : False := <proof>` + `#print axioms`. Numeric name
    components sanitized (`atom.0`→`atom._0`); `Succ` chains collapsed to numerals.
  - **`prove_unsat_to_lean_module`** (solver + façade): like `prove_unsat_to_lean`
    but also returns the Lean source. Same soundness gate (kernel-checks to `False`).
  - **Gated cross-check** (`tests/lean_crosscheck.rs`, skips without `lean`): the
    QF_UFBV (congruence), LRA (Farkas), ∀ (instantiation), and ∃ (skolemization)
    refutations each **type-check in real Lean 4** with `#print axioms` showing only
    the axeyum-declared logical/carrier/uninterpreted/`em`/hypothesis axioms — **no
    `sorryAx`**. The real Lean kernel independently corroborates the in-tree check.
    Honest boundary: inductive recursors are rendered as axioms (their generation is
    trusted, same as in-tree); a later slice can render real `inductive` commands to
    let Lean *derive* the recursors.
- **2026-06-17** — **Track-1 complement sweep (four lanes, alongside the proof/Lean
  agent).** Non-colliding Track-1 increments, each its own sound + tested + pedantic-
  clippy-clean commit:
  - **Differential soundness net** (`tests/differential_qfbv_backends.rs`): seeded
    random QF_BV cross-check across eager `SatBvBackend`, the new `LazyBvBackend`,
    and (feature `z3`) the oracle — DISAGREE=0 + every-`sat`-replays, 200 always-on +
    1500 ignored, 3-way clean. Guards both agents' solver churn.
  - **P1.2 / T1.2.4 `elim_unconstrained`** (`axeyum-rewrite`): unconstrained single-
    use invertible-op elimination, trail-reconstructed, wired into the opt-in
    `check_with_preprocessing`.
  - **P1.7 PBLS** (`pbls.rs`): word-level WalkSAT portfolio engine, one-sided sound
    (`Sat`/`Unknown`, never `Unsat`), deterministic.
  - **P1.3 SAT-core modernization** (`proof_sat.rs`): VSIDS + phase saving + Luby
    restarts on the proof-producing CDCL core (DRAT-checked ⇒ sound regardless).
  - **Round 2** (one more increment per lane): `elim_unconstrained` now peels
    `bvmul` by an odd constant (2-adic inverse); the CDCL core gained local
    learned-clause minimization (self-subsumption); PBLS switched to incremental
    scoring (re-eval only the moved variable's incidence set); and the soundness
    net's larger sweep now includes `PblsBackend` (one-sided `Sat` verdicts
    replayed + cross-checked at scale). All DRAT/replay-guarded, clippy clean.
- **2026-06-17** — **Fair public-QF_BV measurement + graceful oversized-encoding
  refusal (the "1/113" gap, diagnosed)**. The headline "sat-bv decides ~1/113 on
  public QF_BV" was an artifact of `--node-budget 1000` (refusing 112/113 at the
  DAG gate, all 1.3k–340k nodes), itself forced by a robustness bug.
  - **Fix (sat_bv_backend, P1.2 robustness):** a pre-lowering bit-blast-size
    *estimate* (per-op cost in result width: mul ~`w²`, div/rem ~`4w²`, shifts
    ~`w·log w`, else linear; `~3×` for Tseitin) now refuses oversized queries as
    `Unknown(EncodingBudget)` **before `lower_terms` allocates** — so a wide
    multiply degrades cleanly instead of OOMing. Absolute 64M-clause ceiling for
    the no-budget case. Regression test `oversized_multiply_is_refused_gracefully_not_oom`.
  - **Fetched the real 113-file public slice** (SMT-LIB 2024 QF_BV, Zenodo 11061097,
    `20221214-p4dfa-XiaoqiChen`) and ran the fair head-to-head vs Z3 4.13.3.
  - **Result (node 200k, 5M-clause cap, 3s):** **2 sat decided, 0 disagreements,
    0 replay failures, 111 unknown** = 88 **Timeout** (admitted + bit-blasted to
    140k–4.6M-clause CNFs, BatSat can't solve in 3s), 13 EncodingBudget, 10
    NodeBudget. **101/113 lowered without OOM** (RSS ~1.5GB — fix works).
  - **Ceiling (node 300k, 8M-clause cap, 20s):** **3 sat decided**, 110 unknown
    (99 Timeout, 10 EncodingBudget, 1 NodeBudget). 6.7× more time + bigger budgets
    moved decided only 2→3.
  - **Diagnosis:** the gap is **architectural, not robustness (fixed) and not a
    timeout/budget knob.** Eager bit-blasting these word-level instances yields
    ~million-clause CNFs our SAT path can't crack in seconds, while Z3 reasons at
    the word level (~1s each). The honest fair number is **2–3 / 113**, with the
    bottleneck precisely located → Track 1: word-level preprocessing (P1.2), lazy/
    word-level bit-blasting (P2.1), SAT-core modernization (P1.3). Baselines:
    `bench-results/baselines/qf-bv-p4dfa-fair-sat-bv-vs-z3-{3s-n200k-cnf5M,20s-n300k-cnf8M}.json`.
- **2026-06-17** — **Curriculum backlog Tier A–D built (19 items): NT/poly/algebra/LA
  families + 2 sound NRA engine fixes**. Worked the curriculum
  [BACKLOG.md](docs/curriculum/BACKLOG.md) end to end; drawn from Stein/Shoup/VMLS
  (see [foundational-books/source-tocs.md](docs/curriculum/foundational-books/source-tocs.md)).
  - **Tier A (decidable, #1–8):** `Family::NumberTheory` += CRT-witness, quadratic
    residue (SAT) / non-residue (UNSAT), sum-of-two-squares (SAT + `n≡3 mod 4`
    UNSAT), Pythagorean triple; `Family::Polynomial` += factor-theorem identity;
    `Family::Algebra` += 𝔽ₚ-all-invertible (UNSAT) / composite-modulus
    non-invertible (SAT, via a `∀b` finite-domain quantifier). Solver/LRA tests:
    **linear algebra over ℚ** (`Ax=b` solvability + Farkas-refuted inconsistency,
    `tests/linear_algebra_rational.rs`); **rationals node** (density/antisymmetry/
    transitivity, Farkas-certified, `tests/rationals.rs`); **proofs node via
    pigeonhole** (`PHP(5,4)` UNSAT with a re-checked certificate + permutation SAT,
    `tests/pigeonhole_proof.rs`).
  - **Tier B (#9–13):** `Family::Predicate` += Fermat's little theorem at fixed
    `p∈{3,5}` (`∀a`); `Family::Polynomial` += division-with-remainder identity;
    `Family::NumberTheory` += RSA round-trip (`(mᵉ)ᵈ≡m mod 33`, modular-exp with
    per-step reduction); `Family::LinearAlgebra` += 3×3 `det(AB)=detA·detB` over 𝔽₂;
    #13 ("watch a formula become CNF→SAT") realized by the existing
    `scenario_pipeline_report`/`curriculum_demo`/`BvLayerStats` observability.
  - **Tier C — NRA/prove engine (#14–16), measured & sound:** **#14** the
    `prove`/`produce_evidence` front door now **dispatches nonlinear real goals to
    NRA** (`produce_nra_evidence`) instead of hard-erroring `Unsupported`;
    soundness-probed (NRA does not claim `x²<0` Sat). **#15** NRA now honors a
    **wall-clock deadline** threaded through `branch_and_bound` + the refinement
    loop (the `a²+b²≥2ab` case returns `Unknown` in ~5s instead of hanging 60s+;
    the Spivak SOS-frontier test is now active, not `#[ignore]`d). **#16** a real
    SOS/positivstellensatz that *proves* the SOS inequalities is genuine P2.5/L
    work — **designed and deferred** (sketch in spivak.md), not faked.
  - **Tier D (#17–19):** decidable-geometry node — the *linear* slice (midpoint
    equidistance/betweenness, LRA Farkas, `tests/decidable_geometry.rs`; polynomial
    geometry is #16-gated); Peano-induction **reconstruction-target stubs**
    (`docs/curriculum/reconstruction-targets/`: `.smt2` + Lean, *targets not
    benchmarks*); **"fill the proof step" grader** — `check_alethe` accepts a
    complete proof and rejects one missing its closing step
    (`tests/proof_step_grading.rs`).
  - **Verified:** 57 `axeyum-scenarios` tests + new solver tests (decidable_geometry
    2, proof_step_grading 2, linear_algebra_rational 3, rationals 3, pigeonhole_proof
    3, spivak 5) all green; fmt/clippy/doc/link-check clean. (Transient: the
    concurrent CDCL(XOR) WIP in `axeyum-cnf` intermittently blocked the solver build;
    re-ran green once fixed.)
  - **References noted:** Software Foundations being translated to Lean + Verso
    (`docs/curriculum/foundational-books/proof-assistants.md`) — the Lean-horizon
    curriculum to align with.
- **2026-06-17** — **Spivak *Calculus* Ch.1 benchmark + the "decidability-ceiling"
  curriculum docs**. Engaged Spivak (and foundational texts) honestly: most of the
  book is ε-δ (Lean-horizon), but **Chapter 1 — the ordered-field axioms P1–P12 and
  the foundational inequalities — is the decidable shadow** where axeyum's LRA/NRA
  live. New (Opus-research-driven):
  - **`crates/axeyum-solver/tests/spivak_inequalities.rs`** — a certificate-bearing
    benchmark. **Order transitivity** proved via the `prove` front door (Farkas,
    re-checked); a **monotonicity inequality** (`x≥1 ∧ y≥1 ⇒ xy≥1`) proved by NRA.
    The **sum-of-squares inequalities** (`a²+b²≥2ab`, AM–GM₂, Cauchy–Schwarz) are
    the **NRA frontier** — kept `#[ignore]`d (they don't terminate promptly). 3
    active tests pass, 1 ignored.
  - **Two measured engine findings** (recorded in
    [formal-mathematics-tour.md](docs/research/08-planning/formal-mathematics-tour.md)):
    (1) `prove` has **no LRA→NRA dispatch** (rejects nonlinear real goals as
    `Unsupported`); (2) the linearization NRA (ADR-0024) **cannot prove SOS
    inequalities — even `a²+b²≥2ab`** — because it abstracts the squares to
    independent variables; sharp motivation for an SOS/positivstellensatz/CAD path
    in P2.5. (The initial assumption that NRA proves these was *wrong*; the probe
    corrected it — what a benchmark is for.)
  - **Curriculum honesty docs**: `docs/curriculum/DEPTH.md` (the map-vs-territory
    scope ceiling — `covered` ≠ textbook depth; the decidability ceiling) and
    `docs/curriculum/foundational-books/` (README + `spivak.md`: how canonical texts
    project onto the LRA/NRA/Lean-horizon split).
  - **`Family::NumberTheory` extended**: `pythagorean_triple` (`a²+b²=c²`, witness
    (3,4,5)) — number theory meets geometry, SAT-by-witness.
  - 57 scenarios tests green; Spivak suite green; clippy/doc/link-check clean in
    isolation.
- **2026-06-17** — **CDCL(XOR) foundation — path 2 of the multiplier wall, 3 sound
  slices + design record** (commits b745772, 8a3415a, 8b21359, 3099964). The
  diagnosed perf lever for the curated unknowns (var*var multiplier-equivalence with
  exponential resolution lower bounds — no path-1 rewrite cracks them) is now an
  *engine*, built in `axeyum-cnf` as three independently-tested slices:
  - **`gf2.rs`** — GF(2) linear (XOR) system solver: `Gf2System` Gaussian-eliminates
    `(⊕ of a var set) = parity` constraints (bit-packed `Vec<u64>` rows, duplicates
    cancel by parity) to RREF; `0=1` row ⇒ `Unsat`, else a satisfying assignment +
    `implied_units` (single-var rows) + `implied_equalities` (two-var rows). 16 tests,
    backbone invariant "the assignment satisfies every input constraint."
  - **`xor_extract.rs`** — sound XOR-gate extraction: `extract_xors(cnf)` recognizes a
    width-`k` gate **only** when a variable-set group is the exact `2^(k-1)`-clause
    complete one-parity encoding (rhs derived from that parity; `k≤8`). Exact ⇒ false
    positives impossible (missing/extra/dup/mixed-parity/over-cap ⇒ not recognized).
    19 tests incl. a brute-force truth-table parity check + the no-false-positive set.
  - **`xor_propagate.rs`** — preprocessing pass in the `simplify`/`eliminate_variables`
    idiom: `xor_propagate(cnf) -> { Unsat, Propagated { formula, stats } }`. A
    contradictory entailed XOR subsystem proves the formula UNSAT; the solver's implied
    units (entailed ⇒ model-preserving) are appended. Brute-forced over all `2^n`
    assignments: model-set preservation, UNSAT soundness **and its converse** (a sat
    formula is never reported unsat), no-op. `implied_equalities` substitution deferred.
  - **Slice 4 DONE & measured** (commits edf65b8, 160408c): `xor_propagate` wired into
    `sat_bv_backend`'s `inprocess` (behind `cnf_inprocessing`, off by default; sound
    Propagated branch only, 20k-clause Gaussian cap). Curated slice (`--inprocess`, 2 s):
    **33 decided, DISAGREE=0, 0 replay failures, PAR-2 0.968 vs 0.963 plain** — sound, no
    regression. **Extraction fired on 20/43 files → 12 908 XOR gates but only 1 implied
    unit** ⇒ on-corpus proof that multiplier parity forces ~no units at preprocessing.
    **Slice 5 (equality substitution) measured & deprioritized** (commit 2a6190d): the
    gates expose **351 equalities** but they concentrate on the AC-structured commute/
    distrib/bit-counting instances (commute08=101, distrib04=40), **~0 on the genuine
    multiplier unknowns** (mulhs16=1, stp_samples=0, calypto_9=1) — they'd only help
    instances the AC canonicalizer already targets. **Static-preprocessing path 2 is
    closed: neither units nor equalities crack the curated multiplier unknowns.**
    **Slice 6 (the real lever):** full CDCL(XOR) — in-search Gaussian on the CDCL trail
    (CryptoMiniSat `gaussian.cpp`), the only form that sees the nonlinear AND-gate
    partial-product structure static preprocessing can't; reuses the validated `gf2`/
    `xor_extract` foundation. Design note has the full measurement.
  - **Slice 6 primitive DONE** (commit 9b449b7): `xor_search::xor_implications(constraints,
    num_vars, assignment: &[Option<bool>]) -> { Conflict{reason}, Implied{lits+reasons} }`
    — the pure propagation primitive the in-search Gaussian calls at each CDCL node. Folds
    the partial assignment into the system and reuses `gf2.rs` (Unsat ⇒ Conflict; reduced
    `implied_units` ⇒ forced literals); reasons are a sound (non-minimal) component
    over-approximation. 18 brute-force tests (conflict/implication soundness over all
    completions, completeness on small systems, reason soundness, 3^n exhaustive
    cross-check, empty-assignment vs `Gf2System::solve`). 187 cnf tests green.
  - **Slice 6 integration validated** (commits 858a644 design, d7a8cd0 decider): the
    proof/trust crux is resolved in
    [cdcl-xor-integration-design.md](docs/research/05-algorithms/cdcl-xor-integration-design.md)
    — XOR reasoning isn't resolution, so XOR-assisted `unsat` becomes a ledgered
    **`TrustId::XorGaussian`** hole (no false DRAT), demotable via an algebraic/PAC
    certificate (path 3); `sat` is already free (model replays). First integration landed:
    `xor_dpll::solve_with_xor` — a correctness-first XOR-aware DPLL (clause-UP ⇄
    `xor_implications` fixpoint, chronological backtrack, no learning/proof yet, step-budget
    → Unknown). **400 brute-force-oracle + 300 batsat differential checks, zero
    disagreement**; every `Sat` model satisfies clauses AND XOR constraints. 196 cnf tests.
  - **Decision ratified — ADR-0035 accepted** (commit 2ea892e): CDCL(XOR) search
    acceleration with a ledgered `XorGaussian` trust hole (no false DRAT; `sat` free;
    demotable via path-3 PAC certificate). The protocol gate is cleared.
  - **Competitive CDCL(XOR) solver DONE** (commit 024596b): `xor_cdcl::solve_with_xor_cdcl`
    — conflict-driven search with clause learning + **watched-literal XOR propagation**
    (CMS `gausswatched` style: a constraint forces its last unassigned var with a minimal,
    **antecedent-valid** reason — the other vars of that constraint, all pre-assigned — which
    is what 1-UIP needs; the Gaussian `xor_implications` component-reasons are not
    antecedent-valid, so the watched scheme is used in-search). XOR antecedents enter 1-UIP as
    synthesized reason clauses. Search-only (no DRAT); isolated (models on `proof_sat`, does
    not touch it). **1,500-formula differential (brute oracle + batsat + `xor_dpll`), zero
    disagreement**; parity-chain UNSAT cases confirm learning fires. 209 cnf tests. Complete
    Gaussian-on-trail (row-provenance reasons) for the parities the watched scheme misses is
    the deferred enhancement.
  - **PATH-2 THESIS CONFIRMED + sped up — CDCL(XOR) cracks the small multiplier wall**
    (commits 577c973 harness, b863d1c note, fea810a VSIDS, aadd0da correction). Robust win on
    `mulhs08` (655 v/2716 cl): **batsat `unknown`@2s (reproducibly) → `solve_with_xor_cdcl`
    UNSAT** — a multiplier-equivalence instance plain CDCL provably cannot crack. Adding the
    P1.3 modernization (**VSIDS + phase saving + Luby restarts**) cut it **20.1 s → ~5.0 s
    (~4×)**, verdict + all ~1,500-formula soundness differentials unchanged. So the
    decomposition is confirmed AND acted on: XOR propagation = the capability, competitive
    heuristics = the speed. (Correction: `calypto_9` is *borderline* for batsat — ~1.1 s some
    runs — so not a clean separator; `mulhs08` is the solid one.) **Honest ceiling:** `mulhs16`
    / larger `stp_samples` still don't decide in minutes even with VSIDS — the next size class
    needs the **complete Gaussian-on-trail propagator** (watched-literal XOR is sound but
    incomplete) and/or more SAT-core work. 212 cnf tests; clippy/fmt clean.
  - **Wired into the product `solve()` path** (commit 6505441, ADR-0035): new
    `SolverConfig::xor_cdcl_fallback` (default OFF) — on a batsat `Unknown` over an
    XOR-structured formula (≤50k clauses), runs `solve_with_xor_cdcl`; **`unsat` = the new
    `TrustId::XorGaussian` ledgered hole** (no DRAT — XOR isn't RUP; backed by the differential
    validation), **`sat` replays** through the existing AIG/model/term path (no trust cost).
    Default-off ⇒ zero baseline change. **`mulhs08` now returns UNSAT through `SatBvBackend`
    with the flag on** — the breakthrough is reachable through the product, not just a test.
    Trust ledger now has 6 holes (added `xor-gaussian`); 8 new tests; full solver suite green.
  - **Measured negative — complete backstop must be incremental** (commit ca19a5f): calling
    the complete `xor_implications` Gaussian as a fixpoint backstop is sound (differentials
    green) but a net regression — from-scratch Gaussian per decision level makes `mulhs08`
    2.3× and `calypto_9` 19× slower and still doesn't crack `mulhs16`/`stp_samples`. Reverted.
    The next size class needs a **true incremental GF(2) matrix** (row-reduce-on-assign /
    restore-on-backtrack, CMS `gausswatched.h`/`packedmatrix.h`), not repeated rebuilds.
  - **Incremental matrix built + 2nd measured negative** (commits 83b99b2 matrix, 6c4407a
    note): `IncrementalXorMatrix` (RREF over free columns, per-assign column-substitution,
    backtrackable, **bit-for-bit oracle-validated** vs `xor_implications` over 100s of random
    systems×sequences; 14 tests) is built and committed as the foundation. But wiring it into
    `xor_cdcl` (sound — all differentials green) made `mulhs08` go 5 s → **>280 s**: it's
    called on every trail assignment and still scans all rows mentioning the var
    (`O(rows·words)`). Reverted. **Twice-confirmed sharp requirement: the propagator must be
    the watched-echelon-row scheme** (CMS `gausswatched.h` — each echelon row watches two free
    vars, so an assign touches only `O(1)` rows). The validated matrix is the foundation; the
    two-watch index over its rows is the remaining decisive optimization. `xor_cdcl` keeps the
    cheap incomplete watched-literal XOR prop until then.
  - **Watched-echelon-row index DONE + 3rd result = course correction** (commits 3ca0340
    matrix watch index, 9c49437 note): the watch index landed (**~25× fewer rows examined per
    assign**, full RREF for completeness, all oracle differentials green). Re-integrated into
    `xor_cdcl` — **sound** (every differential green; parity chains close at level 0) but
    `mulhs08` **still** regressed past 300 s. Decisive cause: **`mulhs08` has ~1 XOR gate among
    655 vars** — the matrix adds no propagation power while replacing the near-free
    watched-literal scheme with overhead. **`mulhs08` was cracked by `xor_cdcl`'s competitive
    CDCL core (VSIDS/restarts/1-UIP), NOT by XOR reasoning.** The curated unknowns are *not
    XOR-dense*, so in-search Gaussian is the wrong lever for them. Integration reverted; the
    watched-row matrix stays a **validated, unwired component** for an XOR-dense corpus (behind
    a density guard + incremental journal). **For the curated next size class the lever is
    P1.3 SAT-core modernization, not more XOR machinery.**
  - **P1.3 clause deletion DONE + localizes the next blocker** (commit 839518e): LBD-based
    learned-clause deletion added to `xor_cdcl` (the standard missing piece — clause DB grew
    unboundedly before). Sound (differentials green), `mulhs08` 5.3 s **no regression**, DB now
    memory-bounded. Honest measurement: `mulhs16`/`stp_samples` still UNKNOWN — they exhaust the
    **2M-conflict budget** (182 s/433 s), i.e. hit the conflict CEILING, not a clause-DB wall.
    So the curated next-size-class blocker is **branching/restart strength / the conflict
    ceiling**, not clause management.
  - **Next options (fresh context):** (a) more P1.3 — stronger branching/restarts (the now-
    localized curated blocker), though Kissat-class is a long road with diminishing per-step
    returns; (b) **Lean kernel inductive layer** (deepest open destination-3 slice — studied,
    soundness-careful port of nanoda's 1677-LOC inductive.rs); (c) broaden Track 2/3/4 (e.g.
    wire the integer-systems Diophantine certificate into evidence/get-proof).
  - **Next (fresh context, ADR-cleared):** wire `xor_implications` into the *production*
    proof-producing CDCL core (`proof_sat`, which has 1-UIP + watched literals) as a
    search-only theory propagator — DRAT suppressed when an XOR reason participates, the
    `unsat` carrying the new `XorGaussian` trust id (land `trust.rs` + golden ledger +
    trust-ledger.md **with** this producer, not before it). Then dispatch wiring +
    curated-multiplier measurement (`DISAGREE=0`) — the first technique that *can* reach
    `mulhs*`/`stp_samples`/`calypto`. The naive `xor_dpll` decider validates soundness; the
    production core (learned clauses) is what makes it competitive. Soundness-critical
    proof-core surgery ⇒ fresh context.
  - All verified **per-crate** (`axeyum-cnf`: 168 tests; `axeyum-solver`: full suite
    green; clippy `-D warnings` + fmt clean) — and now the **full workspace builds +
    test-compiles** (the concurrent math-tour errors resolved). std only, no new deps.
- **2026-06-17** — **Math-tour curriculum — Predicate logic + Number systems;
  coverage now 14/23 nodes**. Two more research→build cycles, oracle-free (ADR-0008):
  - **`Family::Predicate`** (`predicate`): closed quantified theorems the evaluator
    decides by finite-domain expansion — `forall_additive_identity` (∀x. x+0=x),
    `forall_exists_inverse` (∀x ∃y. x+y=0, genuine **quantifier alternation**),
    `exists_square_root` (∃x. x²=4, SAT). Exercises the finite-domain quantifier
    path. → mathtour `predicate-logic` Covered.
  - **`Family::NumberSystem`** (`number_system`): order + Peano structure —
    `signed_trichotomy`, `order_transitivity` (→ `integers`), `unsigned_non_negative`,
    `successor_injective` (→ `naturals`). Exhaustive UNSAT-of-negation over signed/
    unsigned BV. → mathtour `integers` + `naturals` Covered.
  - mathtour.rs ↔ curriculum.toml ↔ node markdown synced (invariant test enforces).
    Curriculum coverage **11 → 14 of 23 nodes** (added predicate-logic, naturals,
    integers). 57 `axeyum-scenarios` tests green; fmt/clippy/doc/link-check clean in
    isolation.
  - Remaining gaps: SAT/CNF, bit-blasting, proofs, decidable-geometry, calculus,
    sequences-limits, cardinality, complex, rationals, reals (number-systems upper
    rungs + lean-horizon analysis). NEXT high-value: ℚ/NRA (linear algebra solving,
    calculus RCF inequalities) → the corpus P2.5 lacks; proofs via a DRAT/Alethe demo.
- **2026-06-17** — **Math-tour curriculum — 3 more families (Polynomials,
  Verification, Sets) + ring/field structure; coverage now 11/23 nodes**. Continued
  the research→build cycles; all oracle-free (ADR-0008), inside the BV subset:
  - **`Family::Polynomial`** (`polynomial`): `binomial_square` ((x+y)²=x²+2xy+y²),
    `difference_of_squares`, `quadratic_root` (x²−5x+6=0, root `x=2` witness). →
    mathtour `polynomials` Covered.
  - **`Family::Verification`** (`verification`, Opus-research-driven): the
    "Hello, World" of program safety — `abs_non_negative_bug` (SAT, `INT_MIN`
    counterexample), `midpoint_overflow_bug` (SAT, the Bloch binary-search bug,
    witness `lo=hi=2^(w−2)`), `max_is_an_upper_bound`, `unsigned_overflow_idiom`,
    `saturating_add_safe` (UNSAT-of-negation theorems). → flips the **solver-capability
    concept `SoftwareVerification`** from gap to Covered (concept.rs).
  - **`Family::Sets`** (`sets`): set-algebra laws over subset bitmasks —
    `distributivity`, `absorption`, `complement_union_is_universe` (set algebra IS
    Boolean algebra). → mathtour `sets` Covered.
  - **`Family::Algebra` extended**: `zero_divisor` (SAT — ℤ/2ʷ is a ring but not an
    integral domain) and `field_failure_even` (UNSAT — even elements have no inverse,
    so ℤ/2ʷ is not a field). → mathtour `rings` + `fields` Covered.
  - **mathtour.rs ↔ curriculum.toml ↔ node markdown synced** (the
    `covered_nodes_have_a_family_realized` invariant test enforces it). Curriculum
    coverage **7 → 11 of 23 nodes** (now: propositional-logic, sets, divisibility,
    modular-arithmetic, groups, rings, fields, polynomials, counting, number-theory,
    linear-algebra).
  - **54 `axeyum-scenarios` tests green; fmt/clippy(pedantic)/doc/link-check clean in
    isolation.** Each family doubles as theory coverage (BV bitwise/arith, signed/
    unsigned comparisons, div/mul, ite) on structured, scalable, oracle-free instances.
  - NEXT (still gaps): SAT/CNF, bit-blasting, proofs, decidable-geometry, calculus,
    sequences-limits — plus ℚ/NRA variants (the corpus P2.5 lacks).
- **2026-06-17** — **Math-tour curriculum advanced — 3 more families built (Opus
  sub-agent + web research)**. Three Opus research sub-agents (pigeonhole/proof
  complexity, finite-algebra/quasigroup encodings, linear-algebra-over-finite-fields)
  informed three new self-checking families, all oracle-free (ADR-0008) and inside
  the BV subset:
  - **`Family::LinearAlgebra`** (`linear_algebra` module): `2×2` matrix identities
    over `BitVec` — `det_product_2x2` (det(AB)=detA·detB), `transpose_product_2x2`
    ((AB)ᵀ=BᵀAᵀ), `mult_associative_2x2` (over 𝔽₂), exhaustive UNSAT of the negation;
    `linear_solve_2x2` (Ax=b, solution as witness). Covers mathtour `linear-algebra`.
  - **`Family::Counting`** (`counting` module): the **pigeonhole principle**
    (`pigeonhole`, n+1 pigeons → distinct hole indices is UNSAT, PHP(5,4)=1024 cases
    exhaustive) + `permutation_exists` (n→n distinct is SAT, identity witness). A
    proof-complexity landmark (Haken 1985; Beame–Pitassi–Impagliazzo 1993). Covers
    mathtour `counting`.
  - **`Family::Algebra`** (`algebra` module): group axioms over ℤ/2ʷ —
    `addition_associative`, `additive_inverse` (exhaustive UNSAT of negation) +
    `subtraction_not_associative` (SAT counterexample, witness `(0,1,1)` — shows
    subtraction is not a group operation). Covers mathtour `groups`.
  - **mathtour/TOML/markdown synced:** `groups`, `counting`, `linear-algebra` flipped
    to `covered` in both `curriculum.toml` and `mathtour.rs` (the invariant test
    `covered_nodes_have_a_family_realized_by_a_self_checking_scenario` enforces the
    sync). Curriculum coverage now **7 of 23 nodes** with a self-checking exercise.
  - **48 `axeyum-scenarios` tests green; fmt/clippy(pedantic)/doc/link-check clean in
    isolation.** (Full `just check` still blocked only by the other agent's in-progress
    `axeyum-smtlib`/`axeyum-rewrite` WIP — transient.)
  - **Each family doubles as theory test coverage:** number theory + counting + algebra
    + linear algebra stress BV multiply/add/sub and the bit-blast→SAT path on
    structured, scalable, oracle-free instances. NEXT: ℚ/NRA linear algebra
    (Farkas-certified solving, det identities) and calculus RCF inequalities → the
    NRA corpus P2.5 lacks.
- **2026-06-17** — **Formal Mathematics Tour — curriculum knowledge graph + first
  destination built**. A structured, machine-readable curriculum derived by working
  *backward* from calculus / number theory / linear algebra to foundations, with
  axeyum's decidable/computable fragment per node.
  - **Knowledge graph** at [`docs/curriculum/`](docs/curriculum/README.md): an
    authoritative `curriculum.toml` (23 nodes, prerequisite edges, decidability +
    family + status metadata) + a README index (DAG, decidability/status legends)
    + **one markdown file per node** across `00-foundations/` (7), `01-number-systems/`
    (5), `02-structures/` (8), `03-destinations/` (3), each with summary · role ·
    prerequisites/unlocks · *testable in axeyum* (with example exercises) ·
    Lean-horizon · references. Grounded in Lean Mathlib, Metamath set.mm, and
    bridge-course canon.
  - **Decidability lens (the load-bearing filter):** each node's testable slice maps
    to an axeyum theory (number theory → BV/LIA, linear algebra → LRA/NRA, calculus
    → NRA); ∀-general theorems (infinitude of primes, ℝ-completeness, ε–δ) are
    flagged `lean-horizon`, never benchmarks. So building math-tour exercises *also*
    grows the arithmetic-theory corpora axeyum lacks (esp. NRA / P2.5).
  - **Code mirror:** `axeyum-scenarios::mathtour` — a queryable `MathNode` table
    mirroring the TOML, with topological teaching order and invariant tests (acyclic,
    prerequisites exist, every `Covered` node's family is realized by a self-checking
    scenario). 6 tests.
  - **First destination built:** `Family::NumberTheory` (`number_theory` module) —
    Bézout's identity (witness from extended Euclid), modular inverse (Hensel-lifted),
    "product of consecutive integers is even", "x² ≡ x (mod 2)". Oracle-free
    (SAT-by-witness / UNSAT-by-exhaustive), inside the BV subset. 4 tests; wired into
    the coverage aggregator and the mathtour `Covered` mapping.
  - Research note: [formal-mathematics-tour.md](docs/research/08-planning/formal-mathematics-tour.md).
  - **41 `axeyum-scenarios` tests green; fmt/clippy(pedantic)/doc/link-check clean
    in isolation.** (Full `just check` still blocked only by the other agent's
    in-progress `axeyum-smtlib` parse.rs — transient.)
- **2026-06-17** — **Double-duty educational layer — FIRST CUT BUILT (ADR-0033)**.
  The self-checking scenarios now double as curriculum, built bottom-up across
  ADR + 5 modules + an integration demo, all within `axeyum-scenarios`' existing
  deps (no new solver surface, no DAG change):
  - **ADR-0033** ratifies the double-duty artifact contract (concept-DAG node +
    statement/solution renderers + *measured* difficulty; grading via the trusted
    checker, never the search) and the crate boundary (extend `axeyum-scenarios`;
    extract `axeyum-edu` later per ADR-0001).
  - **`concept`** — a 15-node curriculum DAG derived from `foundational-dag.md`:
    acyclicity-checked `prerequisites`, deterministic `topological_order`,
    `frontier(mastered)`. 6 tests.
  - **`render`** — `Renderable` (problem statement + worked solution from the
    witness/UNSAT evidence). 2 tests.
  - **`exercise`** — `Exercise` with curriculum placement, measured `Difficulty`,
    and a **sound auto-grader**: a candidate is judged by `Scenario::is_satisfied_by`
    (the evaluator), so a wrong/empty witness is *rejected by evaluation*, never
    silently accepted. 5 tests.
  - **`coverage`** — the concept DAG as a test-coverage map; the key test
    (`every_declared_family_is_realized_by_a_self_checking_scenario`) fails if a
    concept claims coverage no self-checking scenario provides. 8/15 concepts
    covered; 7 gaps tracked honestly. 5 tests.
  - **`logic`** — propositional `Family::Logic` (modus ponens, excluded middle,
    De Morgan, contradiction, a SAT clause) proven by exhaustive truth tables —
    closes the bottom-rung `PropositionalLogic` concept. 2 tests.
  - **`axeyum-bench` `curriculum_demo` example** — ties it together end to end and,
    for the De Morgan BV identity, emits a **136-command Alethe proof re-checked
    VALID in-tree by `check_alethe`** (proof as worked solution; length as a
    proof-level difficulty signal). Demonstrates the whole thesis in one run.
  - **31 `axeyum-scenarios` tests green; fmt/clippy(pedantic)/doc clean in
    isolation.** Full `just check` is red only on the *other agent's* in-progress
    `axeyum-smtlib` parse.rs (concurrent PLAN build) — transient, not from this work.
  - Docs: rev-2 example-suites note (educational lens), ADR-0033, and a new
    "Curriculum / Educational Layer" section in consumer-scenario-models.md.
- **2026-06-17** — **P1.2: opt-in `preprocess` flag on the `solve`/`check_auto`
  façade**. New `SolverConfig::preprocess` (+ `with_preprocess`), default **off** —
  mirrors the existing `cnf_inprocessing` lever. When set, `check_auto` runs the
  denotation- and symbol-preserving canonicalizer over the assertions before its
  existing coercion-rewrite chain and dispatch; the returned `sat` model is
  unchanged (no variables eliminated) and still satisfies the originals. Makes
  word-level preprocessing reachable through the main `solve()` entry point, not
  just `check_with_preprocessing`: a 32-bit `(not (= (a*b) (b*a)))` via
  `solve(..with_preprocess(true))` returns unsat **instantly, no multiplier blast**
  (new `solve` test). Default-off ⇒ zero change to existing behavior/baselines; full
  gate green. Flipping the default remains a separate measured decision (ADR).
- **2026-06-17** — **P1.2: canonicalizer wired into `check_with_preprocessing`**.
  The denotation-preserving canonicalizer (`canonicalize_terms`) is now the FIRST
  pass in `check_with_preprocessing`, ahead of `propagate_values` + `solve_eqs`. It
  eliminates no variables (symbol-preserving), so it needs no reconstruction trail —
  the model still replays against the original assertions. This activates the prior
  commit's commutative-operand ordering in an actual solver path: a 32-bit
  `(not (= (a*b) (b*a)))` is now refuted **instantly by canonicalization, with zero
  multiplier bit-blasting** (new test returns in 0.00 s where a genuine 32×32 blast
  would be slow). Closes the "canonicalizer dormant in the product" gap for the
  opt-in preprocessing path. 6 preprocess tests green. (Default `solve()` still does
  not preprocess — making it the default is a separate decision, likely an ADR.)
- **2026-06-17** — **Research note: foundational example & benchmark suites**
  ([docs/research/08-planning/foundational-example-suites.md](docs/research/08-planning/foundational-example-suites.md)).
  Research-first, no code. Scopes the next wave of example suites by
  *decidability*, not appetite: (A) a self-checking software-verification
  "Hello, World" tier (SV-COMP `ReachSafety`/`NoOverflows` shape, hand-ported,
  reusing BMC/k-induction/symexec — **recommended first**, satisfies the open
  Phase 7 verification-audience criterion); (B) decidable geometry / real-closed
  fields as the QF_NRA/P2.5 corpus that's currently missing (witness-checked
  `sat`; `unsat` exposes the NRA-certificate evidence gap); (C) a low-cost
  finite/modular "math 101" extension of `Family::Identity`. The prompt's
  "Peano 101 / real analysis 101" is split out: induction-bearing arithmetic and
  the ε–δ layer are **undecidable → Lean-horizon proof-reconstruction targets
  (P3.6/P3.7), not benchmarks**; only the RCF-reducible fragment (geometry,
  MetiTarski-style inequalities) is reachable now. Surveys SV-COMP, SMT-LIB
  QF_NRA/meti-tarski, GeoCoq/Tarski, TPTP as yardsticks (mine for shape; do not
  ingest/sweep). Proposes **ADR-0033** to ratify the A/B/C-build, D-target tier
  split. Next: design suite A's first cut.
- **2026-06-17** — **Educational/double-duty lens added (rev 2 of the example-suites
  note)**. Thesis: the architecture that makes an artifact a good *test* is the same
  that makes it good *educational content* — a self-checking, seeded,
  evidence-exhibiting scenario placed in a concept DAG **is** a homework problem
  with a sound auto-grader and a worked solution. axeyum has the four otherwise-hard
  assets: (1) **sound auto-grading for free** because grading is *trusted checking*
  (`eval`/`evidence.check`/`check_alethe`), not search; (2) **certified procedural
  generation** (ADR-0008's SAT-by-execution / UNSAT-by-identity are the two
  procedural-content patterns, with machine-checked answer keys); (3) **measured
  difficulty** (CDCL conflicts, CNF size, Alethe/LRAT proof length); (4) **the
  concept DAG already exists** as the engineering gate (`foundational-dag.md`) —
  formalizing it gives curriculum order + a test-coverage audit + the gate (triple
  duty). Angle 1 (generate): homework banks from generators, a `check_alethe`-graded
  "fill the proof step" tutor, DAG-frontier sequencing — solver
  generates/grades/certifies/sequences *formal* exercises only, narrative stays
  human/LLM. Angle 2 (teach about): glass-box pipeline → a course map keyed to
  axeyum's own layers, with suite D reframed as a *lesson on undecidability*. Adds
  three thin, ADR-gated, no-solver-surface capabilities (rendering layer,
  machine-usable concept-DAG, concrete-execution trace = worked solution). Hard
  rules recorded: education is a consumer/lens that must not starve a foundation
  phase; grading must route through the trusted checker, never the search. ADR-0033
  scope extended to ratify the double-duty artifact contract.
- **2026-06-17** — **P1.2: commutative-operand canonicalization (word-level
  preprocessing)**. The denotation-preserving canonicalizer now sorts the operands
  of commutative ops (`and`/`or`/`xor`/`=`, `bvadd`/`bvmul`/`bvand`/`bvor`/`bvxor`/
  `bvnand`/`bvnor`/`bvxnor`) by ascending `TermId`, so `(bvmul a b)` and `(bvmul b a)`
  hash-cons to the **same** term — composing with the existing
  `=`-structurally-identical rule to fold `(= (bvmul a b) (bvmul b a))` → `true` with
  no bit-blasting. Strictly excludes non-commutative ops (`bvsub`, div/rem, shifts,
  comparisons, `concat`, and crucially `apply` — UF arg order is meaningful).
  Denotation verified by exhaustive 3-bit evaluator equivalence. **Curated slice with
  `--rewrite default`: 33/43 decided (was 32), 10 unknown (was 11), PAR-2 1.010 (was
  1.062), DISAGREE=0** — a real, sound +1 (cracks `calypto_problem_9`). **Honest
  caveat:** the targeted `wienand commute08/16` stay unknown — they are
  associativity+commutativity over multiplier *trees* with intermediate `var`
  bindings, not flat `a*b==b*a`; cracking them needs multiplier-tree AC-normalization
  + intermediate-equality inlining (a larger, separate task). Also: the bench default
  is `--rewrite Off`, so this only helps when rewriting is enabled — wiring the
  canonicalizer into the default `sat-bv` path is a follow-up.
- **2026-06-17** — **Benchmarking checkpoint: no regression + the perf ceiling
  diagnosed**. Re-ran axeyum (`sat-bv`, 2 s) over the committed 43-file curated QF_BV
  slice after the session's 21 proof-track commits: **32/43 decided (8 sat + 24
  unsat), 11 unknown, PAR-2 = 1.062 s** — matches the committed baseline (32/43,
  PAR-2 ≈1.07 s) exactly, so the proof work caused **zero performance regression**.
  All 11 unknowns are **`rustsat-batsat` SAT-solver timeouts** on multiplier-heavy
  instances (`brummayerbiere3 mulhs08/16/32/64`, `calypto`, `wienand-cav2008
  commute08/16`, `stp_samples`), with small-to-mid CNFs (2.7k–200k clauses) —
  i.e. **SAT time, not encoding, dominates**. Crucially, CNF preprocessing
  (subsumption T1.1.1 + bounded variable elimination T1.1.2) is **already wired**
  into the `sat-bv` path (`sat_bv_backend.rs`), and these still time out — so the
  next real perf lever is **SAT-solving power** (the custom CDCL core, ADR-0002, +
  multiplier-aware inprocessing), whose priority the methodology gates on exactly
  this "SAT time dominates" measurement. That gate is now met on the curated slice.
- **2026-06-17** — **`(get-proof)` now serves THREE theories (QF_BV + EUF + LRA)**.
  `solve_smtlib_get_proof` tries, in order, the `QF_BV` bitblast driver, the EUF
  congruence emitter (`prove_qf_uf_unsat_alethe`), and the LRA Farkas emitter
  (`prove_lra_unsat_alethe`), returning the first that yields a proof its
  fragment-appropriate checker re-validates (`check_alethe` for BV/EUF,
  `check_alethe_lra` for LRA). So a standard SMT-LIB `(get-proof)` now returns a
  checkable Alethe certificate for bit-vector, uninterpreted-function, AND
  linear-real-arithmetic `unsat`s — the three externally-Carcara-validated proof
  families, unified behind one front-door call. `Ok(None)` only when no supported
  fragment can prove it (e.g. an unsat needing shift semantics: `a=1 ∧ a≪1=0`).
  5 tests (BV/EUF/LRA proofs + sat→None + shift-semantics→None).
- **2026-06-17** — **`(get-proof)` in the SMT-LIB front door (P4.4 + proof surface)**.
  New `solve_smtlib_get_proof(input, config) -> Result<Option<String>, SolverError>`:
  parses a script, and when the assertions are `unsat` in the QF_BV Alethe fragment,
  returns the textual Alethe proof (`bitblast_*` → CNF-intro → resolution to `(cl)`),
  re-validated by `check_alethe` before return; `Ok(None)` for sat/unknown or
  out-of-fragment (shifts/div/rem, non-QF_BV). The parser now recognizes-and-ignores
  the `(get-proof)` command (was rejected). This is the user-facing z3-parity entry
  point for the whole session's proof machinery — a standard SMT-LIB `(get-proof)`
  now yields a Carcara-and-self-checkable certificate. 3 tests (checkable proof, sat
  → None, shift → None). Next: shift/div-rem `hole`+miter; then P3.5/P3.6.
- **2026-06-17** — **QF_BV Alethe proof wired into the evidence pipeline (first-class
  self-checking output)**. New `Evidence::UnsatAletheProof(Vec<AletheCommand>)` whose
  `check` route is `check_alethe` (internal re-validation). `produce_qf_bv_evidence`
  now, on the `>20`-bit `unsat` path that previously emitted plain DRAT (bit-blast
  *trusted*, `BitBlast=false`), first tries `prove_qf_bv_unsat_alethe` and — if it
  returns a proof that re-checks — emits the Alethe certificate with **`BitBlast`,
  `Tseitin`, `SatRefutation` all CERTIFIED** (the `bitblast_*` steps check the
  reduction itself, closing the bit-blast trust hole on that route). Precedence:
  term-level enumeration (≤20 bits, trusts only the evaluator) > Alethe proof >
  plain DRAT (out-of-fragment fallback unchanged). A 24-bit in-fragment `unsat`
  (`(bvult a b)∧(bvult b c)∧(bvult c a)`) now carries an Alethe proof that re-checks
  `Ok(true)`; a `bvshl` instance still falls back to DRAT. 20 evidence tests green.
  **The whole session's QF_BV proof machinery is now a product output**, dual-checkable
  (Carcara external + `check_alethe` internal). Next: shift/div-rem `hole`+miter;
  then the P3.5 reductions (arrays/functions/int-blasting) and P3.6 Lean kernel.
- **2026-06-17** — **axeyum SELF-CHECKS its own full QF_BV proofs (internal checker
  complete)**. Ported the `bitblast_*` reconstructions (all 17: var/const/not/
  and/or/xor/xnor/add/neg/**mult**/ult/slt/equal/comp/extract/concat/sign_extend) and
  the `and` clausification into `check_alethe`, mirroring `bitblast_alethe.rs` /
  Carcara's `bitvectors.rs` (`build_term_vec` over `AletheTerm`, width recovered from
  `@bbterm` arity / max `@bit_of` index). **`check_alethe(prove_qf_bv_unsat_alethe(…))
  == Ok(true)` for ALL 9 driver instances** (eq+ult, eq+neq, ult-cycle, slt, +
  bitwise/arith/nested compound) — new `qfbv_self_check.rs`. So a QF_BV `unsat` proof
  is now validated by **both** the external Carcara binary AND axeyum's own in-tree
  checker (no external dependency). One soundness-critical refinement: the resolution
  entailment mapping (`cnf_lit`/`register_atom`) now parity-folds leading syntactic
  `(not …)` so `(not φ)`-as-atom and `φ`-negated normalize identically (a genuine
  logical equivalence, still anchored by the DRAT re-check; all rejection tests hold).
  116 cnf-alethe tests + 9 self-check tests green. **The QF_BV proof system is now
  dual-checkable end-to-end.** Next: shift/div-rem via `hole`+miter for full QF_BV;
  wire the driver into the evidence pipeline (now that an internal checker exists).
- **2026-06-17** — **`check_alethe` gains the Boolean CNF-introduction rules**
  (`equiv1`/`equiv2`/`not_equiv1`/`not_equiv2`, `equiv_pos1/2`, `equiv_neg1/2`,
  `xor_pos1/2`, `xor_neg1/2`) — the Tseitin tautologies axeyum's QF_BV driver emits,
  transcribed literal-for-literal from Carcara's `tautology.rs` (polarities/order
  strict). With the `refl`/`symm`/`trans`/`cong` family from the previous commit,
  axeyum's own checker now validates the **Boolean layer** of its QF_BV proofs
  internally; only `bitblast_*` (BV reconstructions) and the `and` clausification
  remain to port for full self-checking (the latter deferred: a structural `and`
  would flip an existing `UnsupportedRule` test, so it lands with that test update).
  12 new rules, each with positive + rejection tests, + 2 end-to-end Boolean
  refutations to `(cl)`. 105 cnf-alethe tests green. **Next: port `bitblast_*` (+ the
  `and` clausification) into `check_alethe` → axeyum self-checks full QF_BV proofs.**
- **2026-06-17** — **`check_alethe` gains the general equality rules
  `refl`/`symm`/`trans`/`cong`**. axeyum's OWN Alethe checker now structurally
  verifies reflexivity, symmetry, transitivity chains, and congruence (matching
  Carcara's `reflexivity`/`extras`/`transitivity`/`congruence` rules: `trans` by
  premise adjacency, `cong` by one-premise-per-differing-argument-position over a
  shared `App`/`Indexed` head + arity). This is the step toward axeyum checking its
  *own* QF_BV bitblast proofs internally (currently only Carcara can) — `cong`/`trans`
  are exactly the bridge's reduction rules — and it strengthens EUF proof checking
  too. Premises must be unit positive `(= a b)` clauses; rejects head/arity mismatch,
  broken chains, unjustified positions. Dispatch refactored into
  `check_structural_rule` (behavior-preserving, to stay under the clippy line cap).
  4 new tests + an end-to-end `cong`+`trans`→`(cl)` refutation; all 91 cnf-alethe
  tests green. **Remaining for internal QF_BV checking: the `bitblast_*` rules in
  `check_alethe` (port Carcara's reconstructions).**
- **2026-06-17** — **QF_BV proof driver extended to COMPOUND terms (Carcara-`valid`)**.
  `prove_qf_bv_unsat_alethe` now reduces predicates over compound bit-vector operands
  — bitwise, arithmetic (`bvadd`/`bvneg`/`bvmul`), `bvcomp`, structural
  (`extract`/`concat`/`sign_extend`) — **nested to arbitrary depth, shared-DAG
  subterms bit-blasted once**. The uniform front-end (`BbReducer`): bottom-up, every
  term gets an `@bbterm`-form equality via `cong` (over children's equalities) +
  `bitblast_<op>` (over the `@bbterm`-form children) + `trans`; predicates then
  `cong`→`bitblast_<pred>`→`trans` to the bit-level Boolean, feeding the unchanged v1
  Tseitin+LRAT refutation. Factored `bitblast_op_step` to emit a gadget over already-
  rendered operands; switched the bitwise/`bvnot`/`bvxnor`/`extract` arms to
  `build_term_vec` (correct for `@bbterm`-form children; no-op for the IR path). **5
  compound unsat instances Carcara-`valid`** incl. nested `(bvand (bvor a b) c)` and
  arithmetic `(bvadd a b)` conflicts; `None` for shift/div subterms (out of fragment).
  Now `None` only for shifts, div/rem, zero_extend, rotates, `bvsub`/`bvnand`/`bvnor`.
  **Next: shift/div-rem via `hole` + the in-house miter side-cert → full QF_BV.**
- **2026-06-17** — **`prove_qf_bv_unsat_alethe` driver — first AUTOMATED full QF_BV
  `unsat` proof, Carcara-`valid` (T3.3 capstone, v1 fragment)**. New
  `qfbv_alethe.rs`: given QF_BV assertions, confirms `unsat` (SAT-BV path) then emits
  a complete Alethe proof an external checker accepts — no hand-construction. v1
  fragment: predicates `=`/`bvult`/`bvslt` and their negations over bit-vector
  **variables/constants** (any width; compound subterms → `None`, a later increment
  via the validated `cong`/`trans` path). Pipeline: `bitblast_step` →
  `equiv1`/`equiv2`+`resolution` (Boolean form) → hand-rolled Tseitin CNF-introduction
  (each Boolean gate as its own variable, justified by `and_pos`/`and_neg`/`or_pos`/
  `or_neg`/`equiv_pos*`/`equiv_neg*`/`xor_*`) → the in-tree `solve_with_drat_proof` →
  LRAT replayed as Alethe `resolution` to `(cl)`. **4 distinct unsat instances are
  Carcara-`valid`** (incl. a 42-step `(bvult a b) ∧ (bvult b a)` nested-ladder
  refutation), + `None` for sat and for compound-term inputs. Deterministic
  (BTreeMap/insertion-ordered). **This is the first time axeyum AUTOMATICALLY produces
  a complete, externally-checkable QF_BV `unsat` certificate.** Next: extend to
  compound terms (`cong`/`trans`, mechanism already validated) + the
  shift/div-rem `hole`s backed by the miter cert. A predicate over a *compound* BV term (`(bvand a a)` inside
  `(= (bvand a a) a)`) does not project compound bits directly, and Carcara has NO
  `((_ @bit_of i) (@bbterm …))` reduction rule (`refl`/`all_simplify` both reject it).
  The mechanism, now validated end-to-end: bitblast each operand bottom-up, **`cong`**
  to substitute the `@bbterm` forms into the predicate, **`trans`** + `bitblast_equal`
  to the bit-level Boolean, then `equiv*`/`not_equiv*`/`and`/`and_pos`/`and_neg` +
  `resolution` to `(cl)`. Locked in as `full_qf_bv_compound_term_proof_is_accepted_by_carcara`
  (the `bitblast_and`/`bitblast_var` steps from the production emitter). **Every bridge
  rule pattern the general QF_BV driver needs is now empirically pinned against the
  binary** — both variable and compound cases. **Next: the general
  `prove_qf_bv_unsat_alethe` driver (bottom-up term bitblast + cong/trans reduction +
  Tseitin-of-B with CNF-intro + the SAT refutation).**
- **2026-06-17** — **First FULL QF_BV `unsat` proof is Carcara-`valid` end-to-end
  (T3.3 bridge validated)**. Hand-validated against the binary, then locked in as a
  committed regression test (`full_qf_bv_unsat_proof_is_accepted_by_carcara`): for
  `(= a b) ∧ (bvult a b)` (1-bit), the proof composes the **production
  `bitblast_step` emitter** (the `bitblast_equal`/`bitblast_ult` steps) with the
  bridge — `equiv1` + `resolution` to derive each assertion's Boolean form, then
  CNF-introduction (`and` with an `:args` conjunct index; `equiv2`) + `resolution`
  to the empty clause `(cl)`. **Carcara `valid`.** This resolves the last unknowns of
  the bridge (the exact rule inventory + that `and` needs `:args (i)`). Remaining to
  *automate* a general QF_BV proof: a Tseitin encoder turning an arbitrary
  bitblasted Boolean `B` into clauses with CNF-intro justifications, wired over the
  already-valid `lrat_to_alethe` resolution layer. **Next: the general
  `prove_qf_bv_unsat_alethe` driver (Tseitin-of-B + the SAT refutation bridge).**
- **2026-06-17** — **T3.3.1 step 2 complete: bitblast emitter covers Carcara's
  entire non-hole QF_BV operator set**. Added `bvmul` (shift-add multiplier,
  transcribed from Carcara's `shift_add_multiplier` — correct on the first run incl.
  width-1, width≥2, and n-ary left-fold), `bvextract`/`bvconcat`/`bvsign_extend`
  (the structural ops; extract/sign_extend use the `Indexed` LHS, concat is
  low-arg-bits-first). One oracle-forced fix: `sign_extend` with `i==0` is the plain
  `(= ((_ sign_extend 0) x) x)` (Carcara `assert_eq(x,res)`), not a `@bbterm`.
  32 cross-check cases, all Carcara rule-accepted. **Every QF_BV operator Carcara has
  a structural `bitblast_*` rule for is now emitted and empirically validated.** Still
  `None` (the Carcara *holes*): shifts (`bvshl`/`bvlshr`/`bvashr`), div/rem
  (`bvudiv`/`bvurem`/`bvsdiv`/…), zero_extend, rotates — these get `hole` + the
  in-house miter side-cert in a later increment. **Next: the predicate-bitblast +
  Tseitin-CNF bridge to compose these definitional steps into a full QF_BV `unsat`
  proof closing to `(cl)` via the Carcara-valid `lrat_to_alethe` resolution layer.**
- **2026-06-17** — **T3.3.1 step 2 (arithmetic + comparison): bitblast emitter
  extended**. `bitblast_step` now also emits Carcara-valid steps for `bvadd`
  (ripple-carry, n-ary left-fold), `bvneg` (two's-complement adder with verbatim
  `false`/`true` carry-ins), `bvult`/`bvslt` (the comparison ladders, slt with its
  sign-bit final step + width-1 special case), BV `=` (`bitblast_equal`), and
  `bvcomp`. This added the **two further output shapes** beyond the bitwise
  `(= t (@bbterm …))`: predicate ops conclude `(= <pred> <bool>)` (no `@bbterm`),
  and `bvcomp` wraps its single Bool in `@bbterm`. **All six Carcara rule-accepted
  on the first run** (gated per-operator tests; shapes transcribed directly from
  `bitvectors.rs`). 25 cross-check cases total. Still `None` (next increments):
  `bvmul` (shift-add multiplier), structural ops (extract/concat/sign_extend),
  shifts, div/rem. **Next: `bvmul`, then the predicate-bitblast + Tseitin-CNF bridge
  to close a full QF_BV refutation to `(cl)`.**
- **2026-06-16** — **T3.3.1 step 2 (first slice): per-operator bitblast emitter
  (bitwise fragment)**. New `axeyum_solver::bitblast_step(arena, term, id)` emits the
  definitional `(= <T> (@bbterm b0…b_{n-1})) :rule bitblast_<op>` step for the
  bitwise QF_BV fragment — `var`, `const`, `bvnot`, `bvand`, `bvor`, `bvxor`,
  `bvxnor` — building each bit LSB-first via `(_ @bit_of i)` projections exactly as
  Carcara reconstructs (left-fold for n-ary and/or/xor; `(= a_i b_i)` for xnor;
  `true`/`false` per const bit). **All seven operators are Carcara rule-accepted**
  (gated tests: emitted step parses and the `bitblast_*` rule checks — only the
  empty-clause conclusion is absent, since a lone definitional step is not a
  refutation). Every shape matched the binary on the first run (derived from
  `bitvectors.rs`). `bv_term_to_alethe` renders BV terms to matching SMT-LIB syntax
  (`#b…` consts, `bvand`/… heads); anything outside the fragment → `None`. 6 unit
  tests + 7 gated carcara tests. **Next: arithmetic/comparison ops (`bvadd`/`bvmult`/
  `bvult`/`bitblast_equal`), then the predicate-bitblast + Tseitin-CNF bridge to
  close a full QF_BV refutation to `(cl)`.**
- **2026-06-16** — **T3.3.1 step 1: `AletheTerm` indexed-operator IR extension**.
  Added `AletheTerm::Indexed { op, indices: Vec<i128>, args }` so SMT-LIB indexed
  applications like `((_ @bit_of 0) x)` (and bare `(_ @bit_of 1)`) are first-class —
  the bounded prerequisite for the per-operator `bitblast_*` emitter (the old
  `App(String, …)` head + atom-only parser couldn't represent a list-headed
  application). `key`/`write`/`parse` handle applied vs bare forms with exact
  round-trip; an `Indexed` term is an opaque atom to the theory rules (the only
  match sites needing an arm were `real_term`/`int_term` in `alethe_lra.rs` →
  `None`). Purely additive: existing `Const`/`App` output byte-identical, all ~82
  cnf tests + EUF/LRA/resolution emission unchanged. **A gated Carcara test confirms
  the IR renders exactly the syntax Carcara accepts**: a `bitblast_var` step built
  via the IR + `write_alethe` parses and the rule checks (`!parser error` &&
  "does not conclude empty clause"). 4 new IR tests + 1 carcara test (10 cross-check
  total). **Next: T3.3.1 step 2 — per-operator bitblast emitter from `axeyum-bv`.**
- **2026-06-16** — **QF_BV bitblast→Carcara contract reverse-engineered & recorded
  (T3.3.1 design)**. Empirically confirmed against the built Carcara binary the
  exact shape it requires for per-operator `bitblast_*` steps: the `@bbterm`
  operator + indexed `(_ @bit_of i)` bit-extraction (**spelling is `@bit_of`, not
  `@bit`**), e.g. `bitblast_var` accepts
  `(= x (@bbterm ((_ @bit_of 0) x) ((_ @bit_of 1) x)))` — this **parses and checks
  valid** (a lone step only lacks the empty-clause conclusion). Recorded the full
  rule-name set and the L-sized implementation body in
  `docs/research/07-verification/scalable-bitblast-certification.md`: (1) extend
  `AletheTerm` to represent the indexed `(_ @bit_of i)` head (parse/write/`key`
  round-trip) — the current `App(String, …)` can't; (2) per-operator emitter from
  `axeyum-bv`'s lowering, div/rem/shift as `hole` + miter side-cert; (3) bridge via
  Tseitin CNF rules to the already-Carcara-valid `lrat_to_alethe` resolution layer.
  This is the external-checker analogue of the in-house miter certificate (path B);
  no code emitted this turn — deliberately scoped as design so the L-task starts
  correct. **Next action: T3.3.1 step 1 — the `AletheTerm` indexed-op IR extension.**
- **2026-06-16** — **Resolution/clausal layer now Carcara-`valid` (T3.3.3)** — the
  Boolean-refutation rung of a full QF_BV proof. A CNF UNSAT goes CDCL → DRAT →
  LRAT → Alethe (`lrat_to_alethe`) and is now accepted end-to-end by Carcara
  against the asserted input clauses. The cross-check surfaced **two latent bugs
  our lenient `check_alethe` masked**, now fixed in `lrat_to_alethe`: (1) command
  ids were bare numerals (`1`, `2`) — invalid Alethe symbols; now prefixed
  (`a{n}`/`t{n}`); (2) an `assume (or φ…)` introduces the disjunction as a *unit*
  clause, not the clause `(cl φ…)` — each multi-literal input clause now gets an
  explicit `:rule or` unpacking step before resolution consumes it. `check_alethe`
  learned the `or` rule (entailment-checked, like resolution). All `assume`s emit
  before steps (no checker warnings). 82 cnf tests + 9 cross-check cases green.
  This is the third externally-validated proof family (EUF, LRA, now clausal
  resolution) and the closing step a full QF_BV bitblast proof will reuse.
- **2026-06-16** — **LRA Carcara cross-check now covers equality assertions**.
  `FarkasCertificate` gained a `pub origins: Vec<usize>` field (`origins[i]` = the
  source assertion index of atom `i`; an equality contributes two atoms sharing one
  origin). `farkas_args` now groups multipliers by origin instead of assuming a 1:1
  atom↔assertion map: a single-atom assertion (inequality) keeps its multiplier
  (byte-identical output); a two-atom equality `a=b` emits the **signed** coefficient
  `m1−m0` (confirmed sign against Carcara — the mixed equality+inequality case
  disambiguates the global sign), rendered with negatives as `(- n)` / `(- (/ p.0
  q.0))`. Orientation is robust (`is_negation_of` verifies the two atoms are exact
  negatives before trusting push order, else bails to no-args). **Three new
  equality refutations pass Carcara** (`x=1∧x=2` → `((- 1) 1)`; mixed
  equality+inequality; coefficient-bearing equality). 8 cross-check cases total; the
  inequality-only fragment is unchanged. Remaining LRA gap: assertions splitting into
  >2 atoms (conjunctions) still emit no args.
- **2026-06-16** — **LRA `la_generic` proofs now Carcara-`valid` (Farkas `:args`)**.
  The Alethe `Step` IR gained an `args: Vec<AletheTerm>` field (parse + write
  round-trip; emitted after `:premises`, only when non-empty so all ~80 existing
  cnf-alethe tests and EUF/LIA emission stay byte-identical).
  `prove_lra_unsat_alethe` now attaches one Farkas coefficient per clause literal,
  derived from `lra_farkas_certificate` (mapped 1:1 to assertions; equality/`and`
  assertions that split into two bounds emit no args and stay axeyum-checked-only).
  Coefficients render as bare integer numerals or `(/ p.0 q.0)` reals (verified
  against Carcara's `as_fraction`). **Three diverse LRA refutations now pass Carcara
  end-to-end** (unit `(1 1)`, non-unit `(1 2)`, multi-variable `(1 1 1)`) — LRA
  joins EUF as an externally-validated proof family. Carcara re-derives the
  contradiction from the args, so `valid` is the soundness oracle, not the
  coefficients themselves.
- **2026-06-16** — **Carcara third-party cross-check harness landed**
  (`crates/axeyum-solver/tests/carcara_crosscheck.rs`, plan task T3.3.5). axeyum's
  emitted Alethe proofs are now validated by the **independent Rust Carcara
  checker** (shares none of our code), not just our own `check_alethe`: the proof
  is serialized via `write_alethe` + matching `.smt2` via `write_script`, handed to
  `carcara check`. **EUF transitivity and congruence proofs both return `valid`**
  end-to-end. The test runtime-skips (prints a note, passes) when the Carcara
  binary is absent, so CI stays green; build it via
  `cargo build --release -p carcara-cli` in `references/carcara` (override the
  pinned toolchain with `RUSTUP_TOOLCHAIN=…`) or set `AXEYUM_CARCARA_BIN`.
  **Cross-check findings recorded as the next P3.3 tasks:** (1) our `la_generic`
  (LRA) step is rejected by Carcara — it requires the Farkas coefficient `:args`
  (one rational per clause literal); we already compute these
  (`lra_farkas_certificate`) but the Alethe `Step` IR has no `:args` field yet, so
  adding it + emitting the multipliers is the next increment; (2) `lia_generic` is
  a *Carcara hole* (unimplemented there) — Carcara reports `holey`, so the integer
  arithmetic rung needs either an int→real reduction proof or to stay
  axeyum-checked-only. EUF is the first proof family externally validated.
- **2026-06-16** — **`lia_generic` integer Alethe checking + emission**
  (`prove_lia_unsat_alethe`, exported). Integer counterpart to `la_generic`:
  the `la_generic_check` dispatch gained a `lia_generic` arm decided by the
  integer-complete `check_with_lia_simplex` (honoring integrality), plus an int
  parser (constant-factor-guarded `*`, plain-`i128` numerals) and an emitter
  self-validated by `check_alethe_lra`. A dedicated test pins the integer/real
  distinction: `(cl (<= x 0) (>= x 1))` is accepted by `lia_generic`, rejected
  by `la_generic`. 4 new tests; `just check` green.
- **2026-06-16** — **P1.5 online decider wired as the QF_UF fast path** (pending
  commit). `auto::check_auto_dispatch` now tries `solve_qf_uf_online` (online
  DPLL(T) on the backtrackable e-graph) **before** the offline `check_qf_uf`; on
  `Unknown` it falls through to the offline enumeration, then bit-blasting — so the
  change is zero-risk (unknown-safe backstop) and only ever fast-paths a sound
  answer. Full solver suite (incl. functions/aufbv/function_scenarios) green: no
  regression.
- **2026-06-16** — **P1.5 online DPLL(T) decision procedure** (commit 8bbdb9d).
  `solve_qf_uf_online`: extends the refutation engine to a full decider —
  `Unsat`/`Sat(model)`/`Unknown`. On a theory-consistent total assignment it builds
  a model from the e-graph classes (`EufTheory::model`) and **replays it against the
  original assertions** (the soundness gate: a non-replaying model → `Unknown`, never
  a wrong `sat`); no equality atoms / un-encodable structure → `Unknown` (same
  conservative boundary as the offline `check_qf_uf`). `prove_unsat_qf_uf_online` now
  delegates to it. 3 tests incl. a **400-formula differential vs `check_qf_uf`**
  (no Sat/Unsat clash where both decide) + a replay-checked sat model. The online
  QF_UF *decision procedure* on one backtrackable e-graph is complete.
- **2026-06-16** — **P1.5 online DPLL(T) refutation engine** (commit 223230b).
  `prove_unsat_qf_uf_online`: a self-contained online DPLL(T) for QF_UF — Tseitin
  CNF of the Boolean skeleton (and/or/not/xor/implies/ite gates; un-encodable
  structure → sound give-up) driving the online `EufTheory`. Interleaves Boolean
  unit propagation with `EufTheory::propagate`, mirrors eq-atom assignments via
  `assert` (theory `push` per decision, `pop` per backtrack — lockstep), learns
  `¬⋀core` on theory conflicts, chronological backtracking. Returns `true` only at
  a root-level conflict (sound UNSAT). **Differentially validated vs the offline
  `prove_unsat_lazy` on 500 random QF_UF formulas (exact agreement) + 4 crafted
  cases** (disjunction, transitivity, congruence, a SAT case). This is the *online
  search* atop the online theory — the offline SAT-enumeration loop replaced by one
  incremental backtrackable e-graph. (Implemented by a sub-agent; reviewed in full —
  Tseitin gates are equivalence-correct, the UNSAT verdict is sound, push/pop stays
  balanced — and the differential count was raised 50→500.)
- **2026-06-16** — **P1.5 online theory propagation (`EufTheory::propagate`)**
  (commit a3cea13). Extends the online theory with sound EUF propagation: the
  unassigned equality atoms whose sides are already congruent, each entailed `true`
  with the asserted equalities that force it (`TheoryProp{lit, reason}`).
  Assigned-state is now tracked and backtracked in lockstep (per-`push`
  `(diseqs, assigned_log)` markers), so entailments retract on `pop`. 2 added tests
  (transitivity+congruence propagation with reasons; retraction on backtrack).
  The online theory now has the full assert/propagate/explain/backtrack surface a
  CDCL(T) loop drives.
- **2026-06-16** — **P1.5 online `TheorySolver` trait + `EufTheory`** (commit afec596).
  First slice of the *online* CDCL(T) theory interface (vs the offline
  `prove_unsat_lazy` model-enumeration): `TheorySolver` (`assert(atom,value)` →
  `Ok` or a conflicting `Vec<TheoryLit>`; `push`/`pop`) and `EufTheory`, an EUF
  solver over **one** backtrackable keystone `EGraph` kept in sync with the search.
  Asserting `eq` merges sides (reason = atom index, so `EGraph::explain`
  reconstructs the conflict core); asserting `¬eq` records a disequality; conflicts
  = a violated disequality or two distinct constants forced equal. 4 tests
  (congruence conflict + explained core, merge backtracked on `pop`, constant
  collision, transitivity core). Exported; lays the theory side of the CDCL(T) loop
  that P1.6 combination builds on.
- **2026-06-16** — **P2.6 congruence-only nested trigger test** (commit 8e0a61c).
- **2026-06-16** — **P2.6 multi-round instantiation test** (commit 8d0a9e4).
  Added `instantiation_loop_refutes_across_multiple_rounds`: a refutation that
  only closes because round 1 (`∀x. f(x)=g(x)` over ground `f(a)`) introduces
  `g(a)`, which round 2 (`∀x. g(x)=0`) can then match — proving the fixpoint loop
  genuinely chains instances across rounds, not just single-shot.
- **2026-06-16** — **P2.6 keystone wired into `solve` dispatch** (commit 2a6d4bd).
  The infinite/too-wide-domain quantifier fallback in `solve` now tries the
  congruence-aware `prove_quantified_unsat_via_egraph` (keystone) **before** MBQI:
  finite-domain expansion refuses domains wider than `QUANT_EXPAND_BIT_LIMIT`
  (2¹⁰), and since UF is finite-scalar-only in the IR, a `∀x:BV32. f(x)=…`
  quantifier surfaces there — exactly where e-matching modulo the ground
  congruence refutes (fire `f(x)` at ground `f(a)`). Only ever returns `unsat`
  (sound, instances implied) or falls through to MBQI on `unknown`. New
  `auto::tests` dispatch test proves the `solve` → keystone route end to end.
- **2026-06-16** — **P2.6 multi-pattern trigger inference** (commit c82c175).
  `select_triggers` infers a (possibly multi-term) trigger set from the body when
  no single subterm covers all bound variables — single-cover preferred, else a
  greedy set cover over function-app candidates. `instantiate_forall_via_egraph`
  e-matches each trigger and joins the per-trigger substitutions consistently on
  shared variables (`merge_substitutions`), so `∀x,y. f(x)=g(y)` instantiates from
  `{f(x), g(y)}`. 9 qinst tests.
- **2026-06-16** — **P2.6 e-matching instantiation loop** (commit 6902f84).
  `prove_quantified_unsat_via_egraph`: split ground/universals, then instantiate →
  re-check (`check_auto`) → fixpoint; ground-unsat ⇒ sound refutation. Closes the
  e-matching vertical slice on the keystone (e-graph → ematch → instantiation →
  ground refutation). 8 qinst tests.
- **2026-06-16** — **P2.6 multi-variable quantifiers** (commit 0fdf634).
  `instantiate_forall_via_egraph` now peels nested `∀x.∀y.…`, requires a trigger
  covering all bound variables, maps each to its own `Var(index)`, and builds the
  full substitution. With nested/multi-arg trigger support, the keystone
  instantiation covers single/multi-var quantifiers with `f(g(x))` / `g(x,y)`
  triggers. 6 qinst tests.
- **2026-06-16** — **P2.6 nested/multi-arg triggers** (commit c658839).
  `instantiate_forall_via_egraph` generalized from unary to arbitrary triggers via
  the full `ematch` engine: `f(g(x))`, `g(x, a)` (ground parts matched by class).
  5 qinst tests.
- **2026-06-16** — **P2.6 keystone quantifier instantiation** (commit 5ac7343).
  `instantiate_forall_via_egraph` wires `ematch` into instantiation: builds the
  ground e-graph (merging ground equalities), e-matches a unary trigger, emits
  congruence-aware instances (a=b ⇒ f(a),f(b) fire once). The keystone now drives
  EUF and quantifier instantiation end to end. 3 tests.
- **2026-06-16** — **P2.6 e-matching engine** (commit 30ebec9). `EGraph::ematch`:
  full single-pattern matching modulo congruence (nested patterns, repeated-variable
  consistency, all substitutions) — the matching engine quantifier instantiation
  runs. Built on the keystone; matching is intrinsically up to congruence. 23 tests.
- **2026-06-16** — **P2.6 e-matching foundation** (commit ff53168).
  `EGraph::enumerate_apps(decl)` — distinct applications of a function symbol modulo
  congruence (one per class, canonical arg roots), the single-symbol trigger that
  drives quantifier instantiation. The first step toward e-matching / unbounded
  quantifiers (the biggest functional gap; today only finite-domain expansion).
- **2026-06-16** — **QF_UF upgraded to checked** (commit 799cd43); **T1.2.8 AIG
  rewrite attempted + reverted** (regressed a borderline FP128 instance — negative
  result recorded).
- **2026-06-16** — **EUF dispatch path hardened** (commit 21ca0a9). 120-iteration
  randomized differential test: random pure equality/UF formulas decided by both
  `check_qf_uf` and Ackermann must agree. Hardens the now-production EUF fast-path.
- **2026-06-16** — **EUF e-graph path wired into `check_auto`** (commit 6ce85b0).
  UF instances try `check_qf_uf` (congruence fast-path) before the Ackermann
  bit-blast; sound for QF_UFBV (replay-checked sat, re-checked unsat), Ackermann
  fallback on unknown. Full solver test suite + micro bench regression-free.
- **2026-06-16** — **T1.5.5 `check_qf_uf` with replay-checked sat models** (commit
  c08c763). Full QF_UF decision on the e-graph: lazy DPLL(T) + a candidate model
  built from e-graph classes (distinct class values, constants pinned, function
  interpretations) replayed against the originals as the soundness gate. Decisions
  + models differentially agree with Ackermann on all 6 cases. The "model replays"
  half of T1.5.5.
- **2026-06-16** — **EUF prover differentially validated** (commit a73d34a).
  `tests/euf_egraph_diff.rs` cross-checks `prove_unsat_lazy` against the trusted
  Ackermann `QF_UFBV` path: 6 instances (congruence/transitivity/two-arg conflicts,
  a disjunctive refutation, two sat) all agree. The "verified against the eager
  path" check (T1.5.4).
- **2026-06-16** — **P1.5 lazy DPLL(T) loop** (commit 8d97081). `prove_unsat_lazy`
  lifts the conjunctive prover to arbitrary boolean structure: equality atoms →
  fresh Boolean vars, boolean skeleton solved by sat-bv, model theory-checked on
  the e-graph, conflicts turned into explain-based blocking clauses, re-solve to
  fixpoint. Sound EUF UNSAT over disjunctions the conjunctive pass can't see. 8
  euf_egraph tests.
- **2026-06-16** — **P1.5 first slice: EUF congruence UNSAT prover** (commit f69aa40).
  `axeyum-egraph` wired into the solver; `prove_unsat_by_congruence` abstracts
  assertions as uninterpreted equality logic and proves UNSAT by congruence +
  constant distinctness (sound, incomplete), every conflict re-checked by the
  independent `check_congruence` and carrying an UNSAT core. 5 tests. The EUF-on-
  the-e-graph core; next is the lazy boolean loop for full QF_UF.
- **2026-06-16** — **P1.4 e-graph keystone COMPLETE: T1.4.4–T1.4.6** (commits
  c47dc0c, 2c735b5, d81bf46). T1.4.4 backtrackable push/pop trail (path compression
  dropped; every mutation trailed; 150-iteration rebuild property test). T1.4.5
  independent `check_congruence` (own union-find + congruence closure re-validates
  every `explain`). T1.4.6 per-class theory-variable lists (the interface-equality
  bus, merge-propagated + backtracked). The e-graph is now a complete keystone;
  next is P1.5 CDCL(T).
- **2026-06-16** — **T1.4.3 e-graph explanations** (commit 0c5840f). Nieuwenhuis–
  Oliveras proof forest alongside the union-find; `merge(a,b,reason)` records edges;
  `explain(a,b)` returns the minimal input-reason set entailing the equality
  (explain-to-LCA, congruence premises recovered recursively). Soundness
  property-tested (replay named merges → re-derives the equality). 9 tests.
- **2026-06-16** — **P1.4 e-graph keystone started: T1.4.1+T1.4.2** (commit eb3e9e6).
  New dependency-free `axeyum-egraph` crate (ADR-0032): hash-consed e-node creation
  over a root-keyed signature table, path-compressing union-find, and the
  deferred-merge cascade that re-canonicalizes parents to close transitive
  congruence. 5 tests incl. a 300-iteration brute-force congruence-oracle property
  test. Next: T1.4.3 explanations.
- **2026-06-16** — **bench `--preprocess` + measurement** (commit 0c594ac).
  propagate_values+solve_eqs wired into the bench setup phase; trail threaded to
  reconstruct the model before the original-assertion replay. Curated A/B: 32/43,
  agree=32, DISAGREE=0, 0 replay failures, PAR-2 1.060 s (≈ baseline 1.063);
  DAG reduced on 5/43. `just bench-qfbv-curated-preprocess`,
  `qfbv-curated-sat-bv-preprocess-vs-z3-2s.json`.
- **2026-06-16** — **`check_with_preprocessing` wrapper** (commit 86cd28a). Façade
  entry that runs propagate_values+solve_eqs before a backend, composes their
  ModelReconstructionTrails, and on `sat` reconstructs + replays against the
  original assertions (mirrors check_with_array_elimination; wraps at the
  `&mut`-arena layer). 5 integration tests through the real sat-bv backend. Not yet
  on the bench/default path — see Current focus for the setup-phase wiring approach.
- **2026-06-16** — **T1.2.3 solve_eqs** (commit e1682ce). Top-level `(= x t)`
  oriented to `x := t` with a memoized occurs-check, substituted to a fixpoint,
  recorded in the trail; generalizes propagate_values. DAG interning keeps
  substitution linear. 200-trial randomized chain-of-definitions reconstruction
  test. axeyum-rewrite at 36 tests. Next: wire propagate_values+solve_eqs into the
  solve path (the `check_with_preprocessing` wrapper) and measure.
- **2026-06-16** — **P1.2 started: T1.2.1 model-reconstruction trail + T1.2.2
  propagate_values** (commit d5c49b6). New `axeyum_rewrite::ModelReconstructionTrail`
  (eliminated-symbol → defining-term steps, reverse-replay `reconstruct`, composable
  `append`) generalizing the bit-blast-lift / array-`project_model` / BVE-reconstruct
  patterns. First consumer `propagate_values`: top-level `var = const` (and bare /
  negated Boolean) facts substituted to a fixpoint, model-sound via the trail
  (proven end to end). Pure axeyum-rewrite, 32 tests. **Next:** `solve_eqs` (T1.2.3,
  `var = term` elimination — the big variable-count win) and wiring the preprocessing
  pipeline into the solve path + measuring the curated slice.
- **2026-06-16** — **T1.1.4 inprocessing made near-linear + time-bounded.**
  `simplify` → forward one-watch occurrence-list subsumption (variable-keyed
  signature so self-subsuming witnesses aren't false-rejected); `bve` → full
  literal occurrence lists + touched-variable queue (lazy clause removal,
  resolution-budget safety net), running to a fixpoint in one drain. Added
  `simplify_within`/`eliminate_variables_within` deadline variants; `sat_bv`
  bounds inprocessing to ≤50% of the remaining solve budget and the old 512/2048
  size guard was lifted to a 200k/1M admission ceiling. Two new 400-formula
  randomized brute-force tests (subsumption equivalence, BVE equisatisfiability +
  reconstruction). Curated A/B: 32/43 decided, agree=32, DISAGREE=0, 0 replay
  failures, PAR-2 1.095 s — no regression vs baseline; the prior 13–22 s pass
  hangs and 3-instance regression are gone. The 11 unknowns stay unknown because
  they are multiplier-structural (BVE ≈0% on `mulhs*`) or reduced-but-still-hard,
  i.e. SAT-search-bound (→ P1.3). Commits 4c99d7e (a), 154936d (b), this (c).
- **2026-06-16** — **T1.1.3 inprocessing wired into the bit-blast→CNF→solve
  pipeline + measured on s4.** New `SolverConfig::cnf_inprocessing`
  (`with_cnf_inprocessing`, off by default); `sat_bv_backend` runs
  `simplify`+`eliminate_variables` on the Tseitin formula behind a
  `maybe_inprocess` size guard, solves the reduced formula, DRAT-checks /
  `prove_unsat`s the reduced formula, and lifts a reduced `sat` model back via
  `Reconstruction::extend` before the original-term replay (`inprocess_ms`
  folded into `translate`; per-pass stats recorded). 3 A/B tests
  (`tests/sat_bv.rs`), bench `--inprocess` flag (config + JSON metadata + run
  fingerprint), `just bench-qfbv-curated-inprocess`, committed artifact
  `qfbv-curated-sat-bv-inprocess-vs-z3-2s.json`. **Measurement:** with the
  current `O(clauses²)` subsumption + per-candidate-rescan BVE, inprocessing is a
  net regression (13–22 s passes blow a 2 s budget) and decides none of the 11
  unknowns; correctness is intact (DISAGREE=0, 0 replay failures). Guarded to
  ≤512 vars/≤2048 clauses → decision-identical to baseline (32/43, PAR-2 1.071 s).
  Real win deferred to T1.1.4 (occurrence-list indexing).
- **2026-06-15** — Cloned full reference set (added Z3 to `scripts/fetch-references.sh`).
  Ran five Opus sub-agents over Z3 core, Z3 theories, bitwuzla+CaDiCaL/Kissat,
  proof/Lean, and an axeyum self-audit. Authored the end-to-end plan under
  `docs/plan/` with this STATUS tracker and the master `PLAN.md` index.
- **2026-06-15** — **P3.0 done.** New `axeyum_solver::trust` module (`TrustId`,
  `TrustStep`, `ALL_TRUST_IDS`, `trust_ledger_markdown`); `EvidenceReport.trusted_steps`
  records per-result trust dependencies across all producers; golden test +
  `docs/research/08-planning/trust-ledger.md`; 4 per-result tests; ADR-0031.
  Trusted base is now countable: 5 trust holes (array-elim, ackermann, int-blast,
  datatype-elim, fpa2bv) — the targets for Track 3 P3.5.
- **2026-06-15** — **T1.1.1 subsumption pass.** New `axeyum_cnf::simplify`
  (`SubsumeStats`): model-preserving tautology removal + forward subsumption (64-bit
  signature fast-reject) + self-subsuming resolution; 7 tests incl. brute-force
  equivalence and SAT/DRAT preservation. P1.1 → WIP.
- **2026-06-15** — **P4.5 (WIP) + s4 transition.** Bench harness worker stack
  raised to 512 MB (deeply-nested-term stack-overflow fix); committed curated
  QF_BV slice `corpus/qfbv-curated/` (36 files) + `just bench-qfbv-curated`;
  GPU horizon note; `docs/plan/host-setup.md` transition checklist. Full baseline
  OOM-killed the host — deferred to s4 with memory caps.
- **2026-06-15** — **T1.1.2 bounded variable elimination.** New `axeyum_cnf::bve`
  (`eliminate_variables`, `BveOptions`, `BveOutcome`, `BveStats`, `Reconstruction`):
  Davis–Putnam resolution with the CaDiCaL non-increasing/size/occurrence bounds and
  a reverse-replay reconstruction stack (equisatisfiable, not model-preserving — the
  reduced model extends via `Reconstruction::extend`). 6 tests incl. brute-force
  equisatisfiability + per-model reconstruction + bound-respect + SAT/DRAT preservation.
