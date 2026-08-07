# SMT-COMP A2 stale-branch audit and process-free port

Status: process-free R1--R5 stack integrated and combined-main green; live
preparation and launch remain prohibited

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
CARGO_BUILD_JOBS=2 just check
  every code, solver, doctest, ignored moment-proof, rustdoc, profile,
  reflection, benchmark, foundational-resource, rules-as-code, and
  SMT-COMP resume stage passed; the aggregate then exited 1 in parity-docs
  after the direct frontier stage rewrote tracked hardware-relative curves
just parity-docs plan-authority links
  clean replay after restoring the exact committed frontier curves, exit 0
```

The direct full-workspace run provides broad passing evidence but is not a
green `just check`: without the R3 environment override, its frontier stage
writes volatile timing curves to the historical tracked location, so the later
scoreboard consistency check correctly rejects that transient state. The five
curves were restored byte-for-byte to the branch commit and no measurement
change was retained. The clean tail replay passed. This reproduces the exact
failure mode that R3's external artifact directory closes in the constructed
readiness gate.

R5 is now implemented at `e4bb854bf`. The focused suite is 52 tests / 82
subtests, the resume aggregate is 165 tests with one expected live-host skip,
the scoped gate is green, and a real fixture-boundary invocation of the
registered locked/offline build produced a 14,208,408-byte binary and removed
its private target. See the
[`R5 implementation result`](smtcomp-credited-full-preparation-f2-live-capture-r5-implementation-2026-08-06.md).

The exact pushed final topic
`2925efea556cab59251e690c9e4e449468865d2c` then carried the uninterrupted
R3-isolated `CARGO_BUILD_JOBS=2 just check` with exit 0. The five generated
frontier JSON artifacts were confined to a unique external directory; the
worktree and tracked curves remained clean, and the local and remote topic refs
were equal.

Integration-owner review later confirmed that exact topic `2925efea5` was 20
commits strictly ahead of main with no divergence. A synthetic merge preview
completed without conflicts, and merge
`8ed5ad089bd54590b590f797fe6132b21d2f47e7` integrated the reviewed stack.
Focused post-merge gates passed the 52-test readiness suite, the 165-test
resume aggregate, resume-contract generation, plan authority, links, and
`git diff --check`.

That exact merge then passed one uninterrupted
`AXEYUM_PROGRESS_FRONTIER_ARTIFACT_DIR=<external> CARGO_BUILD_JOBS=2 just check`
with exit 0. The run passed all workspace tests and doctests, 9/9 frontier
tests, both order-255 CAS moment proofs in 939.24 seconds, warning-denied
rustdoc, both 162-file Glaurung policies with zero disagreements, generated
resources, rules-as-code, SMT-COMP resume, Lean/process-free contracts, parity
docs, plan authority, and links. All five frontier JSON artifacts stayed in
the external directory and the tracked tree remained clean.

This is an integrated-main result, but not remote CI, a live F2 root, or launch
authorization.

## Exact next slice

A2 is complete. Preserve this integrated process-free boundary and return to
the canonical A3 QF_NIA census. A later explicit review is still required
before C0 or any live F2 action.

Stop before any host probe, sentinel execution, shared-root mutation, F3
acceptance, allocation, or solver wave. Those require a later, separately
reviewed authorization after the corrected process-free stack is on exact
green main.
