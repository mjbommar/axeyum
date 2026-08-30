# Notes: 285-inventory-gate-rot

Detail moved out of [`../status/285-inventory-gate-rot.md`](../status/285-inventory-gate-rot.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

3. **`lane-turn-controls` — STALE FIXTURE, tool (`check-lane-turn.sh`) sound.**
   Cases 1-3 passed; case 4 ("a pre-existing failure is attributed, not
   blamed on the lane") failed both its assertions. That case corrupts
   `docs/plan/generated/theorem-production-ledger.md` in a scratch worktree
   and expects the corruption to be attributed `FAIL (NEW)`. It reads
   `FAIL (PRE-EXISTING …)` instead — correctly: `python3
   scripts/gen-theorem-production-ledger.py --check` is ALREADY red
   (`distinct theorems ROSE 1448 -> 1770`) with a byte-identical
   `theorem-production-ledger.md` and byte-identical `crates/` tree at both
   `HEAD` and `merge-base(HEAD, origin/main)` — confirmed by diffing both
   paths across the two commits, not assumed. The gate genuinely is
   pre-existing broken at both ends of the comparison the tool makes, so the
   tool's attribution is correct and the test's expectation was wrong.
   Fixed the fixture: check the target gate's baseline in the worktree before
   corrupting it, and SKIP case 4 with an explicit message when it is already
   red, instead of asserting a false `FAIL (NEW)` expectation. Verified
   end-to-end with a real nested worktree + real cargo builds:
   `LANE_TURN_CONTROLS|pass=7|fail=0`.

4. **`lra-hypothesis-binding` — BROKEN, and NOT caused by today's growth.**
   This is the soundness-adjacent one, so it got the most care. Its 268
   pinned instances (135+38+66+7+5+17, all six manifests recounted by hand
   and matching the docstring exactly — no drift in the pins themselves) are
   unaffected by corpus growth in general, since the checker only processes
   pinned instances, never a live glob. Ran the full real checker
   (`python3 scripts/check-lra-hypothesis-binding.py --verbose`, ~35 minutes
   of real `lean_hypothesis_binding_dump` re-solves/re-renders under lane
   contention). It crashes partway through, always at the same instance:

   ```
   artifacts/examples/math/number-theory-v0/smt2/diophantine-gcd-obstruction-conflict.smt2:
   the dumper failed:
   lean_hypothesis_binding_dump: prove_unsat_to_lean_theory_module: malformed
   `lean_module_size` step: Diophantine produced a 96297506-byte Lean module,
   over the 67108864-byte cap. ... Declining is the honest outcome
   ```

   The query is trivial: `14*x + 21*y = 5` has no integer solution because
   `gcd(14,21)=7` does not divide 5 — every intermediate value in the
   certificate (`g=7`, `r=5`, `q=0`, reduced coefficients `2` and `3`) is a
   single-digit number, nowhere near `DIO_UNIT_MAX` (4096,
   `crates/axeyum-solver/src/int_reconstruct.rs:1439`), the bound this
   renderer already checks and declines against for oversized inputs. So the
   96 MB module is not "large inputs, correctly declined" — it is a real,
   unexplained blow-up in `crates/axeyum-solver/src/int_reconstruct/
   diophantine.rs`'s Lean-module construction for this specific
   small-coefficient case, caught only because `MAX_LEAN_MODULE_BYTES` (64
   MiB, added in `cfc5f8078` on 2026-08-20) refuses to hand back an
   oversized module instead of returning it.

   **Confirmed this is pre-existing, not introduced by this lane or by
   today's merge**: `git diff --stat 182377c3f HEAD -- crates/` and
   `-- artifacts/examples/math/number-theory-v0/` are both EMPTY — the
   reconstruction code and the query file are byte-identical between `HEAD`
   and `merge-base(HEAD, origin/main)`. Reran the dumper standalone
   (`./target/release/examples/lean_hypothesis_binding_dump
   artifacts/examples/math/number-theory-v0/smt2/diophantine-gcd-obstruction-conflict.smt2`)
   and got the identical 96297506-byte failure, deterministically. This
   instance was pinned as BOUND on 2026-08-18 (`e57eb085e`); the size cap
   landed two days later (`cfc5f8078`, 2026-08-20) — so this either
   regressed sometime in that window or (more likely, given the whole point
   of that commit was to catch existing pathological cases such as the 625
   MB / 2.38 GB `BvAlternationCounterexample` modules it documents) has
   silently been this large since it was pinned, and nothing had run this
   checker to completion since to notice.

   There is a second, separate problem, squarely in `scripts/` but NOT
   touched: `check-lra-hypothesis-binding.py`'s `render_module()`
   (line ~2431) treats ANY nonzero exit from the dumper as an unconditional
   fatal `SystemExit`, aborting the ENTIRE run at the first such instance
   instead of recording it (the checker already has a `DECLINED` category
   and pin file for "no verdict grips this instance" — an oversized-module
   refusal is exactly that shape) and continuing to assess the other 267.
   So today, this single instance blocks the checker from producing ANY
   verdict about the rest of the corpus.

   **Did not touch either problem.** Fixing the Diophantine renderer is a
   `crates/` change, explicitly out of scope for this lane, and I do not
   have a root cause narrow enough to hand off as a one-line fix (the
   bound checks the renderer already has, `g`/`r`/`q`/`m_coeffs` against
   `DIO_UNIT_MAX`, all pass fine on this instance's tiny values, so the
   blow-up is somewhere later in the proof-term construction — most likely
   a missing-sharing / repeated-embedding pattern rather than a numeral-size
   one). Changing `render_module`'s abort-on-error behavior touches the
   error-handling contract of a soundness-adjacent checker without a
   specialist's review, which the task explicitly asked me to be careful
   with rather than fast about. Reclassifying the pin (BOUND -> DECLINED)
   was considered and rejected: that would make the gate pass by hiding a
   real defect instead of fixing or reporting it, which is exactly the
   "adjust a baseline to make it pass" move the task forbids.

## Commits

- `04a77fbf6` — regenerate the example-inventory markers (fixes #1, #2).
- `dcc100cc6` — regenerate `PLAN.md` (downstream of the same fix).
- `e72119787` — fix `lane-turn-controls` case 4's stale fixture (fixes #3).
- (this status file) — no further code commit for #4: diagnosed and left
  unchanged, see above.

## Files

- `docs/documentation-plan.md`, `docs/plan/global/30-workstream-state.md`,
  `PLAN.md` — regenerated counts.
- `scripts/tests/test-check-lane-turn.sh` — case 4 baseline-checked before
  corrupting.
- `crates/axeyum-solver/src/int_reconstruct/diophantine.rs` (read-only,
  investigated, NOT edited) — the likely location of #4's module-size defect.
- `artifacts/examples/math/number-theory-v0/smt2/diophantine-gcd-obstruction-conflict.smt2`
  (read-only) — the trivial query that reproduces the 96 MB module.

## Out of scope, explicitly not touched

- `docs/plan/generated/theorem-production-ledger.md` and its gate
  (`theorem-production-ledger` in `scripts/check.sh`) — genuinely
  pre-existing stale (real theorem-count growth, `1448 -> 1770`), one of the
  coordinator's twelve sibling-lane gates, not one of the four assigned here.
  Regenerating it was not necessary to fix any of the four assigned gates
  (the `lane-turn-controls` fix works by detecting its staleness, not by
  curing it), and doing so risked stepping on whichever lane owns that gate.
- `crates/axeyum-solver/src/int_reconstruct/diophantine.rs` — the likely
  home of #4's real defect. Investigated (read-only) far enough to rule out
  the renderer's own `DIO_UNIT_MAX` (4096) bound checks as the cause (every
  value in this instance's certificate — `g=7`, `r=5`, `q=0`, reduced
  coefficients `2`,`3` — is single-digit and passes them), but not far enough
  to hand off a fix. This is a `crates/` change and explicitly out of scope
  for this lane.
- `scripts/check-lra-hypothesis-binding.py`'s `render_module()` — its
  abort-on-any-dumper-error behavior is arguably too coarse (one oversized
  instance blocks assessment of the other 267), but changing a soundness-
  adjacent checker's error-handling contract under time pressure, without a
  specialist's review, is exactly what the task asked me to be careful with
  rather than fast about. Left as-is.
- `scripts/lra-hypothesis-binding-instances.txt` (the BOUND pin) — this
  instance was considered for reclassification to DECLINED, which WOULD make
  the gate pass, and was rejected: it would hide a real solver defect rather
  than fix or report it, which is the "adjust a baseline to make it pass"
  move the task explicitly forbids.
- `crates/`, `artifacts/kernel-stack-envelope.tsv`, `artifacts/autogenesis/`,
  `scripts/tests/test_check_fact_depends_derived.py`,
  `scripts/tests/test_check_control_tests_reachable.py` — per instructions.
