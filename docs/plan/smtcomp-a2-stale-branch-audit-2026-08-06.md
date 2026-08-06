# SMT-COMP A2 stale-branch audit and process-free port

Status: process-free port checkpoint complete; live preparation and launch remain prohibited

Date: 2026-08-06

Canonical priority and resume authority: [`../../PLAN.md`](../../PLAN.md)

## Scope and verdict

The old `agent/smtcomp/full-preparation-live` branch was audited against
current `origin/main` at `7567ff82771fc1303f1db265fc97a560e8e924a7`. Its
head, `3e53ca631a5369eee1543b5510bee134dfe79847`, was 19 commits ahead of its
merge base and 401 commits behind current main. It is not mergeable as a unit.

The branch contains a useful no-launch F2 capture stack, but its mutable root
trackers and several integration statements describe July refs. More
importantly, the operator still accepts a caller-selected `--axeyum-binary`.
The preregistered R5 correction requires the operator to build and retain
provenance for `smtcomp_cli` from the exact clean integrated source. Until R5
is implemented, mutation-tested, integrated, and independently reviewed, the
operator is not live-ready.

No host was probed, no NAS path was inspected or mutated, no allocation was
created, and no solver was launched during this audit or port.

## Commit disposition

| Old commit(s) | Disposition | Reason |
|---|---|---|
| `3e53ca631` | already integrated | Patch-equivalent solver regression is already present on current main. |
| `57482ad0`, `b02c486b`, `fe32194d`, `30287148` | ported | Process-free capture, completion authority, volatile gate-artifact isolation, and constructed gate environment remain valid. The Rust frontier-artifact change from `fe32194d` was already on main, so only the SMT-COMP portion was retained. |
| `7444ab60`, `185f64d7`, `61ad2712`, `39929350`, `892da372`, `6919ec72`, `0b89c5c8`, `8b6a11f4`, `7993786f` | ported as design/history | These plans and closure updates define the contracts enforced by the retained implementation. Stale root `PLAN.md`/`STATUS.md` changes were excluded. |
| `85748e5d` | ported as blocking preregistration | R5 accurately identifies the remaining exact-source build-provenance defect; its implementation is still absent. |
| `9cec37eb`, `79f5d31d`, `06ba59f2`, `b4f6b0bd` | historical only, not ported | These blocker, preview, input-audit, and stale-snapshot notes bind old refs or external snapshots and are not current execution authority. |

## Retained port evidence

The isolated port branch is `agent/smtcomp/a2-readiness-port`, based on exact
current `origin/main`. The retained functional commits are:

- `9f21cf9b5`: no-launch F2 capture;
- `3a0143824`: completion-time authority closure;
- `c052ae449`: external volatile gate-artifact isolation;
- `7cd7f1791`: constructed readiness-gate environment; and
- `6554db96a`: clean-checkout test repair, removing an assumption that a
  repository-local `target/` directory already exists.

The port passes:

```text
PYTHONWARNINGS=error python3 -m unittest scripts.tests.test_smtcomp_full_population
  47 tests, OK
./scripts/check-smtcomp-resume.sh
  160 tests, OK (1 expected live-host skip), plus 6 + 30 + 6 + 5 + 2 supporting tests
python3 scripts/gen-smtcomp-resume-contract.py --check
  version=2, invariants=18, scenarios=28, accept=5, reject=23
./scripts/check-links.sh
  all links ok
```

These are focused and lane-aggregate results. They are not a full workspace
`just check`, an integrated-main result, remote CI, a live F2 root, or launch
authorization.

## Exact next slice

Implement the source-first R5 plan in this same isolated lane:

1. remove the live `--axeyum-binary` input;
2. build the release `smtcomp_cli` from exact clean integrated source with a
   unique external target, locked/offline dependencies, two jobs, and a
   constructed environment;
3. retain and replay the build observation, output sidecars, tool identities,
   source commit, staged binary, run identity, and completion links;
4. add rejecting mutations for every authority edge; and
5. rerun focused, aggregate, scope, link, and full clean gates before any
   integration proposal.

Stop before any host probe, sentinel execution, shared-root mutation, F3
acceptance, allocation, or solver wave. Those require a later, separately
reviewed authorization after the corrected process-free stack is on exact
green main.
