# SMT-COMP credited full-preparation R5 implementation

Status: implemented and fixture-verified on the isolated topic; integration,
live F2, and every solver action remain prohibited

Date: 2026-08-06

Implementation commit: `e4bb854bf`

Canonical current authority: [`../../PLAN.md`](../../PLAN.md)

Preregistered contract:
[`smtcomp-credited-full-preparation-f2-live-capture-r5-plan-2026-07-25.md`](smtcomp-credited-full-preparation-f2-live-capture-r5-plan-2026-07-25.md)

## Verdict

R5's source-to-binary authority gap is closed in the isolated
`agent/smtcomp/a2-readiness-port` topic. Live capture no longer accepts
`--axeyum-binary` or an Axeyum entry in its solver-source inventory. Before an
attempt directory can exist, the registered operator now performs one private
locked/offline two-job release build of the `axeyum-bench` `smtcomp_cli`
example, rechecks exact integrated main, and carries the output bytes in memory
until the attempt can be created.

This is an implementation result, not live readiness. The topic has not been
integrated into main, no F2 root exists, and no host, sentinel, NAS, F3,
allocation, or solver action was performed.

## Implemented authority chain

[`full_build.py`](../../scripts/smtcomp_repro/full_build.py) owns the new build
boundary:

1. resolve the repository-selected Cargo and Rust compiler to canonical,
   executable, non-proxy paths in one toolchain directory;
2. hash both tools before execution;
3. create a unique Cargo target outside both the repository and shared root;
4. construct the complete non-secret environment from a positive allow-list;
5. execute exactly
   `cargo build --release --locked --offline -p axeyum-bench --example smtcomp_cli`
   with `CARGO_BUILD_JOBS=2`, the private `CARGO_TARGET_DIR`, and the sealed
   compiler in `RUSTC`;
6. require exit zero and the exact regular, executable, non-symlink output;
7. recheck exact integrated-main identity and both tool hashes; and
8. remove the private target after retaining the binary and exact stdout/stderr
   bytes in memory.

After the pre-attempt checks pass, staging installs read-only stdout/stderr
sidecars, an executable Axeyum binary, and one sealed
`axeyum.smtcomp-credited-full-axeyum-build.v1` observation. Preparation schema
v3 links that observation to readiness, the staged binary, the derived
`integrated-release-<source-commit>` version, the run manifest's solver hash,
the complete artifact ledger, and completion-last publication. Durable replay
rehashes the retained observation, sidecars, binary, run identity, and
completion link without claiming that mutable compiler installations were
copied into the preparation.

The readiness path list now includes the R5 plan and `full_build.py`, so a gate
observation cannot describe a pre-R5 source surface as current readiness.

## Rejecting evidence

The focused fixture suite grew from 47 to 52 tests and adds 82 named subtests.
It rejects:

- caller-selected or fallback Axeyum input;
- a non-registered live builder or runtime hook;
- command, offline/locked flag, two-job, target, environment, Cargo, or Rust
  compiler drift;
- ambient compiler, wrapper, loader, target, proxy/network, incremental,
  Python, and credential injection;
- nonzero build exit, missing output, directory output, non-executable output,
  symlink output, empty output, and output-path escape;
- dirty source, source-commit drift, tracking/remote ref drift, or tool mutation
  before shared mutation;
- every build-observation identity class, both output sidecars, staged binary,
  derived version, run identity, readiness commit, schema-v3 completion link,
  and artifact-ledger mutation; and
- any attempt namespace created after repaired-P0 or build failure.

The existing oracle hashes, eight-sentinel order/outcomes, thermal/deadline
checks, completion-last rule, empty execution namespaces, and AST-level absence
of admission/allocation/solver-wave calls remain covered unchanged.

## Evidence at this checkpoint

```text
PYTHONWARNINGS=error python3 -m unittest scripts.tests.test_smtcomp_full_population
  52 tests, OK

./scripts/check-smtcomp-resume.sh
  165 tests, OK (1 expected live-host skip)
  supporting suites: 6/6 + 30/30 + 6/6 + 5/5 + 2/2

python3 scripts/gen-smtcomp-resume-contract.py --check
  version=2, invariants=18, scenarios=28, accept=5, reject=23

registered build smoke, fixture boundary only
  exit=0, binary=14,208,408 bytes, stdout=0 bytes, stderr=3,053 bytes,
  target removed, CARGO_BUILD_JOBS=2

just check-scope origin/main
  52 pytest cases / 82 subtests and the 165-test aggregate passed
```

The smoke used the real registered locked/offline command and constructed
environment but deliberately did not create or publish a preparation. Because
the implementation worktree was not integrated exact main, it carries no live
F2 credit.

## Remaining topic and integration gate

Before proposing integration:

1. update the canonical tracker and workstream handoff;
2. pass links, plan authority, and the scoped/aggregate gates from a clean
   committed topic;
3. push the exact topic commit and verify the remote ref;
4. run one final `just check` with the R3 frontier-artifact destination outside
   the repository, and verify both worktree and tracked frontier bytes remain
   clean; and
5. hand the branch to the integration owner for conflict preview, review,
   merge, and a combined exact-main gate.

Even after integration, live C0/F2 is a separate reviewed action. Do not probe
hosts, run sentinels, mutate NAS state, construct F3 acceptance, allocate
resources, or execute a solver from this result.
