# SMT-COMP credited full-population F2 preparation implementation

Status: process-free implementation and explicit host/sentinel preflight
integrated by `origin/main` merge `1b8ae016`; live preparation remains
outstanding

Date: 2026-07-23

Plan: [credited full-population execution](smtcomp-credited-full-population-plan-2026-07-23.md)

## Result

The repository now has a fail-closed publisher and replay validator for an F2
preparation candidate. This increment ran only temporary fixtures. It did not
probe `s5`/`s6`/`s7`, execute a sentinel, build or stage a live release binary,
write a live NAS preparation root, create a resource session or allocation
attempt, or start a solver.

The candidate requires:

- a readiness record for one exact clean `HEAD == origin/main` state;
- exact successful observations for `just check` and
  `./scripts/check-smtcomp-resume.sh`, bound to that commit and worktree-status
  digest;
- exactly three replay-valid `s5`/`s6`/`s7` host observations, the reconstructed
  environment manifest and host registrations, and coordinator/host Python byte
  identity;
- the exact ordered eight-row incident-sentinel matrix with frozen input,
  solver-binary, command, environment, stdout, stderr, timestamp, and safe
  termination identities;
- completed `unsat` FP sentinels for all three solvers, completed `sat` cvc5
  QF_AUFLIA, and only the preregistered Axeyum QF_AUFLIA outcomes;
- publication after the captured observations but no later than 30 minutes from
  the capture start;
- byte identity between every registered preparation source and `origin/main`;
- the frozen 45,905-row accepted selection and full list/manifest identities;
- all process-free input manifests under the candidate attempt root;
- a content-addressed, immutable runner source bundle with its own file ledger,
  completion seal, and source identity;
- executable Axeyum, cvc5, and Bitwuzla bytes under the attempt root, with each
  digest matching its run manifest and the two oracle digests matching the
  preregistration; and
- three replay-valid cells containing the exact common schedule and all 432
  allocation command manifests.

Publication first installs sealed copies of the selection, composition,
readiness, and full-preflight records. It then inventories every file under the
attempt root and installs `complete.json` last. Preparation schema v2 binds the
preflight record seal in the completion. The completion state is
`prepared-no-launch`, and `launch_authorized` is always `false`.

## Replay and mutation boundary

Replay checks the recorded Git commits directly, so a valid historical
candidate does not become unverifiable merely because the repository later
advances. Current-state inspection remains mandatory when readiness is first
built and when a candidate is published.

The validator rehashes the accepted selection, staged source bundle, source
identity, run/plan/schedule/command records, binaries, copied component records,
host observations, reconstructed registrations, environment manifest,
sentinel inputs and byte sidecars, and complete artifact namespace. It rejects:

- a stale gate, changed conclusion, dirty or non-main live source state;
- missing, reordered, external, or mutated preparation inputs;
- source-bundle, binary, run-manifest, selection, or command drift;
- missing, duplicate, reordered, stale, externally rooted, or mutated sentinel
  evidence;
- host observation, registration, environment, coordinator-Python, timestamp,
  termination-class, or semantic-outcome drift;
- a second or pre-existing completion;
- any nonempty `multi-host-attempts`, `multi-host-terminals`, `records`, or
  `resource-sessions` namespace; and
- any file added, removed, or changed after completion.

The fixture intercepts the publisher's atomic installs and proves that
`complete.json` is the final call. It also reseals reordered, missing,
duplicate, host-drifted, semantically unsafe, and expired preflight mutations;
all reject. Post-completion execution evidence, sentinel stdout mutation, and
solver-binary mutation also reject on replay.

## Gates

The following passed on implementation commit `43f871ad`, which is integrated
by `origin/main` merge `1b8ae016`:

```text
python3 -m unittest scripts.tests.test_smtcomp_full_population
28 tests, OK

./scripts/check-smtcomp-resume.sh
115 tests, OK (one expected live-host skip)
runner/scoring/pipeline/selection/provenance checks, OK
generated resume contract, selection authority, and repaired-P0 comparison, OK
```

The explicit preflight implementation and readiness-source registration are
integrated. Independently, the branch-wide gate is not green:
`cargo fmt --all --check` reports existing
format drift in the bench/CAS lane, which this increment did not edit. Lean R7
is now integrated by merge `9fe5cab6`; its focused frozen-source test passes.

## Authorization boundary

This result proves only the process-free candidate mechanism and semantic
preflight replay. It is not an F2 live result and does not authorize F3. Live F2
remains conditional on a clean, green, byte-identical `origin/main`, fresh
accepted-population rehash, reviewed host/environment/thermal probes, the exact
repaired-P0 incident sentinels, and completion of an empty
`launch_authorized=false` preparation inside the frozen capture window. F3
remains forbidden until that exact live F2 result is integrated by the mainline
owner.
