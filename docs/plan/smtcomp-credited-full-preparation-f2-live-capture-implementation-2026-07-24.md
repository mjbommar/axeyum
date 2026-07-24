# SMT-COMP credited full-population F2 live-capture implementation

Status: implementation complete on pushed topic commit `57482ad0`; not yet
integrated, and no live F2 capture is authorized or claimed

Date: 2026-07-24

Plan: [F2 live-capture plan](smtcomp-credited-full-preparation-f2-live-capture-plan-2026-07-24.md)

Correction: [F2 live-capture R1 plan](smtcomp-credited-full-preparation-f2-live-capture-r1-plan-2026-07-24.md)

## Result

Commit `57482ad05a3caf5ce27aef95abae52790a97ffcd` adds the missing
no-launch operator and pushes it on
`origin/agent/smtcomp/full-preparation-live`. The implementation was exercised
only through temporary fixtures. It did not probe `s5`, `s6`, or `s7`; take a
live thermal sample; execute a live incident sentinel; build or stage a live
release binary; create a NAS preparation root; publish an acceptance record;
start an allocation; or launch a solver wave.

The implementation consists of:

- `scripts/prepare-smtcomp-credited-full.py`, the executable no-launch entry
  point;
- `scripts/smtcomp_repro/full_capture.py`, the F2 orchestration and read-only
  verification module;
- preparation-schema-v2 thermal validation in
  `scripts/smtcomp_repro/full_preflight.py`;
- exact readiness-source registration in
  `scripts/smtcomp_repro/full_readiness.py`; and
- the focused positive, rejection, mutation, ordering, and static-boundary
  controls in `scripts/tests/test_smtcomp_full_population.py`.

## Implemented contract

The operator fails before attempt creation unless the worktree is clean and
local `HEAD`, local `origin/main`, and live remote `main` are the same commit.
It then runs both registered gates, rechecks exact main after each gate, and
requires a sealed readiness conclusion.

Before any attempt directory is created, it also derives the repaired-P0
comparison from the named completed preparation and all three external result
roots, validates those roots, and requires canonical equality with the
committed generated comparison. Missing, drifted, substituted, or unsafe P0
evidence rejects without a NAS mutation.

After those guards, the operator:

1. creates a fresh non-overwriting safe attempt root;
2. physically rehashes and stages the exact 45,905-file selection, source
   bundle, corpus audit, three solver binaries, and three sentinel inputs;
3. captures the exact `s5`, `s6`, and `s7` host observations and reconstructs
   the environment plus registrations;
4. composes and replays all three process-free cells and all 432 commands;
5. captures exactly three first-wave-bound thermal observations in host order,
   including the raw `sensors -j` bytes and a strict temperature below
   90,000 mC;
6. runs and seals exactly the eight bounded incident sentinels in registered
   order; and
7. publishes `complete.json` last with `status=prepared-no-launch` and
   `launch_authorized=false`.

Incomplete attempts remain append-only and are neither cleaned up nor resumed.
Read-only verification replays every staged identity and rejects post-completion
mutation or any execution-evidence namespace content. Non-fixture dependency
injection is rejected. A static AST control rejects allocation/admission
imports and calls, so the module has no F3 or solver-wave path.

## Gates

The following passed on the implementation tree and commit:

```text
PYTHONWARNINGS=error python3 -m unittest \
  scripts.tests.test_smtcomp_full_population
44 tests, OK

./scripts/check-smtcomp-resume.sh
157 tests, OK (one expected live-host skip)
runner 6/6; scoring 30/30; pipeline 6/6; selection 5/5;
provenance 2/2; generated contracts, OK

just foundational-resources
137 concept rows and 174 example packs, OK

./scripts/check-links.sh
all links ok

just check-scope main
exit 0; scoped gates PASSED

just check
exit 0; formatting, all-feature Clippy, workspace tests and doctests,
documentation, foundational resources, generated contracts, parity checks,
and link checks passed
```

The long `just check` session's exact terminal result was recovered as exit
code zero; its final output includes the complete-parity generator, the
remaining generated ledgers/contracts, parity documentation, and `all links
ok`.

## Integration and authorization boundary

This commit is implementation evidence, not a live F2 result. The integration
owner must land `57482ad0` and this result, then establish an exact clean green
`HEAD == origin/main == git ls-remote origin main` state. Only after that may
the separately reviewed C5 procedure build the release binary and invoke this
operator with the exact repaired-P0 preparation.

Any resulting `launch_authorized=false` root remains review input only. It must
be independently verified, documented, and integrated byte-for-byte before a
separate F3 acceptance is constructed. No allocation or solver launch is
authorized by this implementation checkpoint.
