# Notes: 187-drat-evidence-route

Detail moved out of [`../status/187-drat-evidence-route.md`](../status/187-drat-evidence-route.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

| query | before | after |
| --- | --- | --- |
| `neg-fp8-add-monotone-rne.smt2` | 25m46s (ledger figure) | **5.028 s end to end**, of which 2.555 s checking; `certified=1 recheck=ok` |
| `neg-fp16-add-monotone-rne.smt2` | decide 11.09 s; check ~95 steps/s -> ~2.4 h extrapolated, **never observed to finish** | **125.098 s end to end**, of which 82.302 s checking (10,048.8 steps/s over 827,048 steps); `certified=1 recheck=ok` |

**fp16 now certifies.** The search is *unchanged* — 424,601 conflicts, 27.748 s,
the same 827,048 steps and 193,214,020 bytes as every previous run — and the
whole difference is the stage that reads the proof back: ~106x on the checking
rate, from a stage that had never been observed to terminate to one that takes
under ninety seconds.

**`F:fp16-add-monotone-rne` is still recorded `open`, deliberately.** The
measurement is written into its `notes` and the stale "certifying costs multiple
hours" text there is now explicitly marked as history — leaving that in place
would be exactly the stale-obstacle failure `CLAUDE.md` documents. But
`epistemic_status` is a claim about what the ledger can *show*, and showing it
needs an `evidence` row with a `checker_command` whose exit status depends on the
finding, plus a verified negative control. That row does not exist; this lane was
scoped to notes on that file and did not write it. **The obstruction being gone
and the evidence existing are different claims, and only the first is
established.** Writing that evidence row is the obvious next task and is now
unblocked.

**Soundness discipline.** The load-bearing fixture is over **satisfiable**
formulas, because on an unsatisfiable one every accepted proof is sound
vacuously. `never_certifies_a_satisfiable_formula` attacks random SAT instances
(counter asserted `>= 20`) with a borrowed refutation, a truncated proof, a bare
unjustified empty clause and random garbage ending in an empty clause. The
bare-empty-clause shape is the one that kills a missing `check_lrat` gate:
`elaborate_drat_to_lrat_backward` answers `Ok(vec![])` when there is no
refutation, and an empty LRAT proof is `Ok(false)` to the trusted checker, *not*
an error — so a composition returning `Certified` on elaboration success alone
would certify a satisfiable formula from an empty proof. Mutation-verified: that
is exactly what the mutant does.

**Mutation results, stated precisely rather than rounded to "exactly one":**

| guard deleted | tests that died |
| --- | --- |
| the `check_lrat` gate | 3 — soundness plus two decline-reason precision tests |
| the `check_drat_backward` conjunct in `recheck` | 2 |
| the whole budget gate | 3 |
| the deadline half of the budget gate only | **1** |

Only the deadline half carries exactly one claim, and exactly one test dies for
it. The others kill more than one because the guard carries more than one claim;
saying so is more useful than a number that looks tidier.

**What the next lane needs to know.**

- **The RAT gap is now on the hot path.** `LratStep` cannot carry a pivot or
  negative hint blocks, so a RAT core lemma declines the fast route and drops
  back onto the superlinear one. Our CDCL core emits RUP-only proofs so this is
  rare today, but a future RAT-emitting technique (blocked-clause addition,
  symmetry breaking) would silently lose the whole improvement. The fix is an
  LRAT step that can express RAT — not another checker.
- **The backward stage is not step-interruptible**, so it is admitted only when
  the budget can accommodate it whole. A live deadline admits it and can be
  overshot by that stage's cost; an overshoot that certifies is a genuine
  verification, never a timeout promoted to a pass.
- `CheckingProgress` gained a `BackwardLratCertify` variant reporting exactly
  twice (opening, closing). Any exhaustive match needs an arm; `smtcomp_cli` was
  the only other consumer.
- **Four accepting `check_drat` sites are left, and the audit is done for you:**
  `sat_bv_backend.rs:1961` (native CDCL inline check), `:1489` (pure-Gauss XOR
  certificate), `:2049` (`verify_unsat_proof`, the `prove_unsat` gate), and
  `bitblast_miter.rs:152` (faithfulness miter). All four are *verdict-only* —
  three discard the proof, the fourth publishes `dimacs`/`drat` with no LRAT
  field — so each converts to the exporter's shape: try `certify_unsat_via_lrat`,
  fall back to `check_drat` on a decline. Left unconverted only to keep this diff
  reviewable, not because anything blocks them. `:2049` is the one with the most
  reach, since it is on the default `prove_unsat` path.

**Pre-existing failures seen while gating, confirmed NOT mine** (each reproduced
with my four source files reverted to `main` in the same worktree, which is the
cheap discriminator when a suspect diff touches no code the failing test calls):

- `reconstruct::arithmetic::monomial_bound::*` overflows its stack in `--release`
  as well as debug — so by the documented discriminator this is runaway
  recursion in that Lean-reconstruction module, not a stack-margin problem.
  `RUST_MIN_STACK=512M` clears the whole `-p axeyum-solver --lib --features full`
  sweep to **1438 passed, 0 failed**.
- `axeyum-bench --test qfbv_proof_export`, both tests, failing on
  "must be a flat assertion script without push/pop/reset/check-sat-assuming".
  Identical on `main`, and touches no DRAT code.
- `clippy` errors in `axeyum-cnf/src/cube.rs:1574` (`chunks_exact` -> `as_chunks`)
  and three warnings in `reconstruct/arithmetic/axreal_call_site_guard.rs`. This
  host's toolchain, not this diff; my own files are clippy-clean.
