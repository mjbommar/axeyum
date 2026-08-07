# SMT-COMP credited full-population F2 live-capture R2 plan

Status: implemented and gated on pushed commit
`b02c486b1711ca3612816b1921c0adbb8086b3a2`; no live F2 action was taken,
and live capture remains conditional on integration into exact clean green
`main`

Date: 2026-07-24

Parent: [F2 live-capture plan](smtcomp-credited-full-preparation-f2-live-capture-plan-2026-07-24.md)

First correction: [F2 live-capture R1 plan](smtcomp-credited-full-preparation-f2-live-capture-r1-plan-2026-07-24.md)

Implementation audit: [F2 live-capture implementation](smtcomp-credited-full-preparation-f2-live-capture-implementation-2026-07-24.md)

Preregistration commit: `3992935c`

## Why this correction exists

A post-implementation, pre-integration audit found three narrow gaps between
the source-first contract and commit `57482ad0`. None has produced live
evidence: the topic is not integrated, and no host, sentinel, or NAS capture
was touched.

1. The sentinel runner passed the complete inherited coordinator environment
   to each solver while sealing only the three registered solver variables.
   An unrecorded variable such as `LD_PRELOAD`, a solver-specific option, or a
   locale setting could therefore affect the observed result without changing
   `environment_sha256`.
2. The publisher accepted a caller-supplied `prepared_at_ns` before validating
   and hashing the complete artifact ledger. A completion installed after the
   30-minute window could retain an earlier in-window timestamp.
3. The operator checked live local/tracking/remote-main equality after the
   sentinels but not at the final completion-last install. Artifact validation
   and inventory can be nontrivial, so remote `main` could advance between the
   last check and publication.

These are evidence-integrity defects, not reasons to weaken the window,
environment, or exact-main requirements. R2 closes only these gaps.

## R2.1: exact sentinel subprocess environment

The eight sentinel subprocesses receive exactly the registered mapping:

```text
AYU_THREADS=1
OMP_NUM_THREADS=1
RAYON_NUM_THREADS=1
```

They do not inherit arbitrary coordinator variables. The sealed
`environment_sha256` remains the digest of this exact mapping and therefore
becomes a complete subprocess-environment identity rather than an identity for
only three overrides. The executables and inputs are already canonical absolute
paths beneath the attempt, so no inherited `PATH` is required.

A focused control must seed the test process with conflicting and unrelated
environment variables, intercept every runner call, and prove that each of the
eight calls receives exactly the registered mapping.

## R2.2: finalization-time deadline authority

For a live preparation, `prepared_at_ns` may not be supplied by a caller. The
publisher must:

1. perform the existing component, binary, preflight, empty-execution, and
   artifact-ledger validation;
2. obtain a fresh wall-clock timestamp only after that inventory is complete;
3. replay the preflight deadline against that fresh timestamp; and
4. use that same timestamp in the completion installed immediately afterward.

Fixture-only callers may retain an explicit deterministic timestamp. A live
caller-supplied timestamp rejects. Tests must prove that an in-window early
check cannot authorize an out-of-window finalization and that expiry leaves the
attempt without `complete.json`.

## R2.3: exact main at completion-last publication

The exact-main inspector moves to the readiness layer so both the live operator
and the publisher use one implementation. It must still require a clean
worktree and exact equality among local `HEAD`, local `origin/main`, and live
`git ls-remote origin refs/heads/main`. At completion it additionally requires
that exact value to equal the readiness `head_commit`.

Immediately after artifact inventory and before the final timestamp/deadline
check, a live publisher reruns that inspector. Ref uncertainty or advancement
rejects before `complete.json` exists. Retained files make the attempt
explicitly incomplete; no cleanup, overwrite, or retroactive completion is
allowed.

Focused controls must prove that local, tracking, or remote advancement at this
boundary prevents completion and that the final authority check precedes both
the final timestamp and `complete.json` installation.

## R2.4: gates and authorization boundary

The correction must add itself to the registered readiness paths and pass:

```sh
PYTHONWARNINGS=error python3 -m unittest \
  scripts.tests.test_smtcomp_full_population
./scripts/check-smtcomp-resume.sh
python3 scripts/gen-smtcomp-resume-contract.py --check
just check-scope main
./scripts/check-links.sh
```

The final topic must pass `just check` before integration. This R2 correction
does not authorize host probes, sentinel execution, NAS mutation, F3
acceptance, allocation, or a solver wave. Live F2 remains conditional on the
exact corrected topic being integrated into clean green `main`.

## Closure result

Commit `b02c486b1711ca3612816b1921c0adbb8086b3a2` implements the registered
correction:

- each sentinel subprocess now receives only the exact three-variable sealed
  environment;
- live callers cannot inject `prepared_at_ns`, and the publisher samples the
  completion timestamp only after the complete artifact inventory;
- the shared exact-main inspector rechecks clean local/tracking/live-remote
  equality against the readiness commit immediately before the final
  timestamp/deadline decision; and
- ordering and mutation controls prove that remote drift, caller timestamps,
  or deadline expiry reject before `complete.json` is installed.

The corrected code passed 45 focused tests, the 158-test portable resume gate
with one expected live-host skip, all runner/scoring/pipeline/selection/
provenance subgates, `just check-scope main`, and the complete workspace
`just check`. The full gate exited zero after formatting, strict all-feature
Clippy, workspace tests and doctests, the two registered ignored CAS families,
warning-denied documentation, the 162-file Glaurung regular gate, foundational
resources, generated contracts, parity checks, and `all links ok`. Five
frontier JSON files changed only in runtime `solve_ms` values and were restored
to their committed bytes after the successful gate.

This closes the source correction and removes the integration hold on the
corrected topic. It does not authorize live work from the topic branch: the
integration owner must first land the exact corrected stack, establish clean
green exact `main`, and rerun the registered authority checks before any host
probe, sentinel, or NAS mutation.
