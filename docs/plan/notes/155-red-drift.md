# Notes: 155-red-drift

Detail moved out of [`../status/155-red-drift.md`](../status/155-red-drift.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

| suite | class | evidence |
| --- | --- | --- |
| `test_prove_tock_log2{,_v2,_v3,_v4}` | **stale pin** | `crates/axeyum-verify/tests/tock_log2_external.rs` gained 20 lines of doc comments in `d4ffe2a54` (no constant changed) after `7c3960c9b` froze the four registrations' `producer_files_hash`. |
| `test_validate_glaurung_llvm_loop_semantic_census` | **broken detector** | Pins the SHA-256 of the WHOLE workspace `Cargo.lock` as a "producer file" for a narrow `axeyum-verify` census. `Cargo.lock` changed 12+ times since the manifest froze, all from unrelated new crates (`axeyum-cas`, `axeyum-py`, `pyo3`, `rustpython`, `toml`, `chrono`, ...) that never touch `axeyum-verify`'s dependency subtree. The pin cannot hold in an active monorepo. |
| `test_check_autogenesis_official_gcd_balanced_bezout_{generic_base,official_kernel}_result` | **stale pin** | `crates/axeyum-lean-import/examples/official_gcd_balanced_bezout_composition.rs` was gutted to a small `include!` shim in `e3a8611b4` (clippy `missing_docs`/`E0753` fix); its 697-line body moved verbatim to `support/official_gcd_balanced_bezout.rs`. No logic changed, but both checkers' `SOURCE_SHA256` pins predate the move. |
| `test_check_autogenesis_nat_fib_gcd_surface_plan` | **broken detector (test bug) — FIXED** | The checker's real fact-drift fallback (`byte_digest(fact_path) != target["fact_file_sha256"]` -> re-read the live fact) is genuinely exercised on the committed data, because the target fact progressed since the plan froze. Two mutation tests globally patched `json.loads` (`return_value=changed`) so that fallback's SECOND `json.loads` call also returned the mutated PLAN dict, masking the specific error message each test wanted. Not a checker bug. |
| `test_check_autogenesis_nat_gcd_fib_add_self_qualification` | **stale pin / real drift, worse than recorded** | Even the unmutated, committed manifest fails with `dispatch_baseline identity changed` — not only the mutation-message tests, as the prior triage's note implied. The checker pins `artifacts/autogenesis/mathlib-nursery-dispatch-baseline-v1.json`'s SHA-256; that shared file has moved under many later autogenesis commits (most recently `3ade08628`). Subject/checker owned by the autogenesis lane. |
| `test_check_autogenesis_nat_gcd_greatest_plan` | **stale pin — and the outcome that justifies the cleanup** | Even the unmutated, committed plan fails with `target fact identity or open state changed`. The plan required `F:ml430-nat-gcd-greatest-0a04214a` to still be `open`; it is now `proved` (`proof_route: kernel-lean`, `axiom_footprint: []`, one checked kernel-term evidence entry). **`Nat.gcd_greatest` got proved after this plan froze — the detector caught real progress nobody recorded a closure for.** |
| `test_gen_autogenesis_mathlib_stable_statement_comparison` | **broken detector, and not content drift at all** | `verify_inputs()` runs `git -C /nas3/.../mathlib-v4.32.1-checkout rev-parse HEAD` and treats ANY nonzero exit as `current-stable checkout identity changed`. On this host that call fails with "detected dubious ownership" (NFS-shared checkout, different uid) — not because HEAD moved. `git -c safe.directory='*' -C <checkout> rev-parse HEAD` prints exactly the pinned `520045ab14e26149ee970e2e617ca04b09bde5d6`. The checker should pass `-c safe.directory=<path>` itself rather than depend on ambient git config (which this repository's own rules forbid changing globally in a shared checkout). |
| `test_check_autogenesis_balanced_bezout_euclidean_update_dependency_audit_plan` | **environmental, not a bug** | Needs `target/debug/examples/theorem_footprint_batch_audit`, which no fast gate builds. Reason in `control-optout.tsv` was already accurate; confirmed, left as-is. |

**1 of 12 fixed** (`test_check_autogenesis_nat_fib_gcd_surface_plan`, all 4
sub-tests now pass against the real, committed data). **11 remain excluded**
because the fix is a subject or a checker script outside this lane's scope
(`crates/axeyum-lean-import`, `crates/axeyum-verify`, `artifacts/autogenesis/`,
`docs/consumer-track/verify/`, and four `scripts/check-autogenesis-*.py` /
`scripts/validate-glaurung-*.py` / `scripts/gen-autogenesis-*.py` checker
scripts). `control-optout.tsv` now carries the precise root cause for each,
with commit SHAs, so the owning lane does not have to re-derive it.

## The fix that landed

`scripts/tests/test_check_autogenesis_nat_fib_gcd_surface_plan.py`: the two
failing mutation tests (`test_capsule_hash_mutation_fails`,
`test_submission_budget_mutation_fails`) scoped their `json.loads` patch to the
exact PLAN text via `side_effect`, instead of `return_value=changed` for every
call. Mutation evidence (scratch copy, `artifacts/` symlinked read-only, never
the shared checkout): removing the capsule-hash guard in the checker kills
exactly `test_capsule_hash_mutation_fails`; removing the budget guard kills
exactly `test_submission_budget_mutation_fails`; the unmutated checker passes
all 4 as a control.

## Also fixed: `scripts/check-shell-antipatterns.sh`

Was red on `main` (`render/check.sh` and `scripts/tests/test-lane-commit.sh`
both used `grep -q` in a pipeline under `pipefail`, absent from the baseline).
`scripts/tests/test-lane-commit.sh` line 111 (`git log --oneline -1 | grep -qv
base`) rewritten to `[ "$(git log --oneline -1 | grep -vc base)" != 0 ]` —
same discrimination, confirmed with a standalone probe covering all three
cases (real commit / placeholder "base" commit / nonzero helper rc). Full
integration suite (`bash scripts/tests/test-lane-commit.sh`) still passes,
9/9. `render/check.sh` is not in this lane's scope (not under `scripts/tests/`);
its one occurrence is now named in `scripts/check-shell-antipatterns.baseline`
(`render/check.sh 1`) so the gate is green and the known issue stays visible
for its owner, matching the existing baseline's own convention for
out-of-lane files.

## Found, out of scope, reported rather than fixed

`scripts/run-python-controls.py`'s catch-all sweep turned up a NEW red suite
not among the 12: `test_smtcomp_full_population` (2 errors,
`ContractError: full-preparation origin revision is not integrated`). Root
cause confirmed via `git merge-base --is-ancestor origin/main HEAD`: this
worktree's `HEAD` is **17 commits behind** `origin/main` (0 commits ahead), so
`full_readiness.py`'s live ancestry check (`origin/main` must be an ancestor
of `HEAD`) correctly reports non-integration for a worktree that has not
fetched/merged recent `origin/main` activity. This is worktree staleness, not
a defect in the suite or in this lane's 3-file diff — none of the touched
files (`test_check_autogenesis_nat_fib_gcd_surface_plan.py`,
`control-optout.tsv`, `check-control-registration.sh`,
`test-lane-commit.sh`, `check-shell-antipatterns.baseline`) touch
`scripts/smtcomp_repro/` or `scripts/tests/test_smtcomp_full_population.py`.
Not fixed here: per the brief, this lane merges LOCAL `main` only, never
`origin/main`; the coordinator's own merge/push flow will resolve the
ancestry before this reaches `origin`. Re-check after that integration rather
than "fixing" a live git-ancestry assertion.
