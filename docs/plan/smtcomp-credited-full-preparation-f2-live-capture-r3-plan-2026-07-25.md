# SMT-COMP credited full-population F2 live-capture R3 plan

Status: preregistered; implementation and live F2 remain prohibited

Date: 2026-07-25

Parent: [F2 live-capture plan](smtcomp-credited-full-preparation-f2-live-capture-plan-2026-07-24.md)

Prior corrections:
[R1](smtcomp-credited-full-preparation-f2-live-capture-r1-plan-2026-07-24.md)
and
[R2](smtcomp-credited-full-preparation-f2-live-capture-r2-plan-2026-07-24.md)

Implementation audit:
[F2 live-capture implementation](smtcomp-credited-full-preparation-f2-live-capture-implementation-2026-07-24.md)

## Why this correction exists

The R2 full gate exited zero, but its ordinary workspace tests rewrote five
tracked progress-frontier JSON files because their hardware-relative
`solve_ms` observations are emitted directly under `bench-results/frontier/`.
Those timing-only changes were restored after the gate. That manual cleanup is
valid for topic validation but cannot occur inside the reviewed live operator:
`capture_live_readiness` requires a clean exact main before the gates and again
after each gate, and it must never restore or overwrite repository work.

The issue reproduced independently on clean topic commit `06ba59fa` with:

```sh
cargo test -p axeyum-solver --all-features --test progress_frontier \
  frontier_bv_reduction -- --exact --nocapture
```

The test passed at frontier 40 over baseline 30 and then changed 39 removed and
39 added rows in `bench-results/frontier/bv_reduction.json`, solely in measured
`solve_ms` values. Therefore an otherwise green registered `just check` makes
the source worktree dirty and the live C0 readiness capture necessarily
rejects before C5. No host, sentinel, F2 attempt, NAS mutation, admission,
allocation, or solver wave was used to discover this defect.

R3 closes only this gate-output isolation defect. It does not weaken the
clean-worktree rule, the exact local/tracking/live-remote main rule, either
registered gate, the frontier ratchets, or any C5 requirement.

## R3.1: explicit volatile frontier-artifact destination

The progress-frontier test writer may accept one narrowly named environment
override for its artifact directory. The override must be a nonempty absolute
path. With no override, existing developer and measurement behavior remains
unchanged: the five JSON artifacts continue to be written under the committed
`bench-results/frontier/` directory.

The registered readiness gate runner must create a unique temporary directory
outside the repository and set the override itself for the child gate. It must
replace any inherited value rather than trust it. The command remains exactly
`just check` or `./scripts/check-smtcomp-resume.sh`; solver behavior, frontier
construction, pass/fail ratchets, stdout, stderr, and exit status remain
unchanged. Only the volatile JSON destination changes.

Temporary timing curves are not credited measurement evidence and are deleted
with the temporary gate directory. The operator must not use `git restore`,
`checkout`, `reset`, a reverse patch, or any automatic repository cleanup. A
temporary-directory creation failure rejects before the gate runs.

## R3.2: mutation and integration gates

Focused coverage must prove:

1. the Rust artifact-directory selector preserves the historical default and
   accepts only a nonempty absolute override;
2. the readiness gate environment replaces an inherited override with the
   unique registered temporary path;
3. a real targeted frontier test writes its timing JSON beneath that temporary
   path while leaving the committed frontier artifact byte-identical; and
4. all existing clean-tree, exact-main, gate-order, output-seal, and no-launch
   controls remain unchanged.

The correction must add this plan to the immutable readiness path set and pass:

```sh
PYTHONWARNINGS=error python3 -m unittest \
  scripts.tests.test_smtcomp_full_population
cargo test -p axeyum-solver --all-features --test progress_frontier \
  artifact_directory_override_is_explicit_and_absolute -- --exact
./scripts/check-smtcomp-resume.sh
just check-scope origin/main
./scripts/check-links.sh
```

Before integration, the final topic must also pass `just check` with a clean
post-gate worktree. The test-generated temporary curves must not be committed.

## R3.3: authorization boundary

This plan authorizes only the minimal source and test changes above. It does
not authorize a live capture from the topic branch. The integration owner must
first land R3 with the earlier F2 stack, repair and green exact main, and rerun
the registered gates through the corrected non-mutating path. C5 must still
rehash all selected payload bytes, build the exact integrated Axeyum binary,
revalidate repaired P0 and external roots, capture all three host and thermal
observations, and execute all eight sentinels inside the frozen window before
publishing only `launch_authorized=false` completion last.
