# SMT-COMP credited full-population F2 live-capture implementation

Status: corrected implementation is pushed and fully gated through
`b02c486b1711ca3612816b1921c0adbb8086b3a2`; it is ready for the integration
owner, but no live F2 capture is authorized or claimed before exact clean green
mainline integration

Date: 2026-07-24

Plan: [F2 live-capture plan](smtcomp-credited-full-preparation-f2-live-capture-plan-2026-07-24.md)

Correction: [F2 live-capture R1 plan](smtcomp-credited-full-preparation-f2-live-capture-r1-plan-2026-07-24.md)

## Result

Commit `57482ad05a3caf5ce27aef95abae52790a97ffcd` added the missing no-launch
operator. A pre-integration audit then preregistered the R2 closure at
`3992935c`, and commit `b02c486b1711ca3612816b1921c0adbb8086b3a2` implemented
that correction. The complete stack is pushed on
`origin/agent/smtcomp/full-preparation-live`. It was exercised only through
temporary fixtures. It did not probe `s5`, `s6`, or `s7`; take a live thermal
sample; execute a live incident sentinel; build or stage a live release binary;
create a NAS preparation root; publish an acceptance record; start an
allocation; or launch a solver wave.

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

R2 additionally seals the final evidence boundary. Sentinel processes receive
exactly `AYU_THREADS=1`, `OMP_NUM_THREADS=1`, and `RAYON_NUM_THREADS=1`, without
arbitrary inherited environment state. Live callers cannot supply the
completion time. After artifact inventory, the publisher rechecks clean exact
local/tracking/live-remote main against the readiness commit, samples a fresh
timestamp, revalidates the 30-minute deadline, and only then installs
`complete.json` last. Focused ordering controls prove that remote drift,
caller-supplied time, and expiry all reject without a completion.

## Gates

The following passed on the implementation tree and commit:

```text
PYTHONWARNINGS=error python3 -m unittest \
  scripts.tests.test_smtcomp_full_population
45 tests, OK

./scripts/check-smtcomp-resume.sh
158 tests, OK (one expected live-host skip)
runner 6/6; scoring 30/30; pipeline 6/6; selection 5/5;
provenance 2/2; generated contracts, OK

just foundational-resources
137 concept rows and 174 example packs, OK

./scripts/check-links.sh
all links ok

just check-scope main
exit 0; scoped gates PASSED

just check  # corrected code commit b02c486b
exit 0; formatting, all-feature Clippy, workspace tests and doctests, both
registered ignored CAS families, documentation, the 162-file regular Glaurung
gate, foundational resources, generated contracts, parity checks, and link
checks passed; final line: all links ok
```

The long `just check` session's exact terminal result was recovered as exit
code zero; its final output includes the complete-parity generator, the
remaining generated ledgers/contracts, parity documentation, and `all links
ok`.

## Integration and authorization boundary

This corrected stack is implementation evidence, not a live F2 result. The R2
environment, deadline, and completion-bound exact-main defects are closed and
fully gated, so the integration hold applies only to the obsolete `57482ad0`
checkpoint by itself. The integration owner may land the exact corrected topic
and this result, then must establish an exact clean green
`HEAD == origin/main == git ls-remote origin main` state. Only after that may
the separately reviewed C5 procedure build the release binary and invoke this
operator with the exact repaired-P0 preparation.

Any resulting `launch_authorized=false` root remains review input only. It must
be independently verified, documented, and integrated byte-for-byte before a
separate F3 acceptance is constructed. No allocation or solver launch is
authorized by this implementation checkpoint. Commit `57482ad0` by itself is
not ready to land; the corrected stack through `b02c486b` is the minimum code
boundary for integration.

## Post-closure integration audit

The audited implementation/result closure is pushed through
`892da3767e306f4e72cdfae2ea13370038ea55e9`; at audit time, local, tracking,
and live remote topic refs were equal and the worktree was clean. That
checkpoint has no pull request and is not an ancestor of exact `origin/main`
`08af3665e553aa1266e45aa46b6467f1ebc5551b`.

Main is independently unfit to authorize C5. Its docs workflow is green, but
CI run `30122366840` is red in two non-SMT-owned controls. Rust 1.97 rejects the
two `assert!(seen_syn_sent == 1)` sites in
`crates/axeyum-verify/tests/protocol_fsm_examples.rs` under
`manual_assert_eq`; commit `a4a041d2` allowed `manual_assert`, which is a
different lint. The stable
`one_level_fixed_mbqi_retry_closes_seed_111` test also returned
`Unknown(ResourceLimit)` with an exhausted MBQI instantiation budget. Neither
failure changes the bounded F2 source result, but either one keeps exact-main
authorization false.

A requirement-by-requirement C0--C5 audit found no additional owned
no-launch implementation defect. The current live command is the parent C5
command augmented by R1's mandatory `--repaired-p0-preparation` argument, and
its printed root must then be passed to a distinct read-only `--verify-root`
process. Those commands remain prohibited until the current clean remote topic
through at least `9cec37e4` is integrated and the resulting
local/tracking/live-remote main plus both registered gates are green.

The subsequent
[synthetic integration preview](smtcomp-credited-full-preparation-f2-integration-preview-2026-07-24.md)
combines exact main `08af3665` with audited topic `9cec37e4` without touching
the integration checkout. It has no conflicts and passes the complete scoped
SMT-COMP gate, parity documentation, and link checks. This removes a bounded
integration uncertainty but does not override main's failed CI or authorize
live F2.

The subsequent read-only
[external-input audit](smtcomp-credited-full-preparation-f2-input-audit-2026-07-24.md)
also revalidated every C5-consumed frozen artifact available before
integration: all 45,905 accepted ledger rows and selected-file sizes, the
corpus audit and its three retained dependencies, the repaired-P0 comparison,
both oracle binaries, and all three sentinel inputs. The F2 attempt namespace
remained absent. This reduces input-drift uncertainty only; it deliberately
did not build or run Axeyum, rehash the 15.1 GB selected payload, probe hosts,
or run sentinels, and therefore does not satisfy C0 or C5.

## R3 gate-output-isolation closure

The source-first
[R3 correction](smtcomp-credited-full-preparation-f2-live-capture-r3-plan-2026-07-25.md)
is implemented and pushed through
`fe32194dc43eceb5dc67137819862dc949cc3c6d`. The readiness runner now gives
the unchanged registered gates a unique external destination for volatile
progress-frontier timing JSON, replaces any inherited destination, and still
rejects every source mutation without cleaning it up.

The final evidence includes 47 focused Python tests, the complete nine-test
frontier suite, the 160-test SMT-COMP aggregate with one expected live-host
skip, `just check-scope origin/main`, and a terminal exit-zero full
`just check`. The full gate passed both registered ignored CAS families,
generated resources/contracts, parity documentation, and links. It created
exactly the five expected JSON files under the external temporary directory,
left `bench-results/frontier` byte-clean, left the topic worktree clean, and
ended with `all links ok`; the temporary files were then removed explicitly.

This closes the owned C0 gate-output-isolation defect only. Exact remote main
remains `08af3665`, main CI `30122366840` remains red on separately owned
failures, and no pull request exists for the topic. No host probe, sentinel,
NAS mutation, F2 attempt, admission, allocation, or solver wave was performed
or authorized.
