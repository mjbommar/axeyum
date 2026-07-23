# Lean U2 TL0.6.3 M2 offline implementation checkpoint

Status: **pure contract, completion store, and one-shot runner implemented,
validated, committed, and pushed; no live harness discovery or test process has
run**

Date: 2026-07-22

Frozen plan:
[M2 shard-0001 execution plan](lean-u2-official-execution-tl0.6.3-m2-shard-0001-plan-2026-07-22.md)
at SHA-256
`4cef4ba9c57820f5bff82e4cfdfdc524b3d0d54665a947cf2b27560767ec81dd`.

## 1. Publication boundary

The source-first plan was committed and pushed at `16bd6f08` before any M2
implementation. Commit `9783ba9306bcc95a6dee894e16e96af2b0e25bd5` then
implemented, validated, committed, and pushed the pure contract. The local and
remote `agent/docs/lean4-complete-parity` refs were equal at that commit.

That first checkpoint deliberately added no live process-launch command. It
created no live harness, ran no discovery command, launched no CTest process,
and published no attempt or case outcome. A separately committed one-shot
runner remained a precondition for the plan's single authorized attempt.

Commit `57dcf343daf4e294bdd8cc89307ab19f3a3182bd` subsequently
implemented, validated, committed, and pushed the completion-last evidence
store. It also exposes only offline `--check`; the launch boundary is unchanged.

Commit `d1f144d46aad67a88e2dce195911ca851b143695` then corrected the
dependency direction before launcher publication: the 64 case records bind
spec/terminal/JUnit and can be installed before post/projection, as the frozen
plan requires.

Commit `431d3959ae5c3d7bbabf25c1d3a3aa6ab88f6f4c` subsequently
implemented, validated, committed, and pushed the one-shot runner. Local,
tracking, and remote refs were equal at that revision. The command exists but
has not been invoked.

## 2. Exact implementation identities

| Source | SHA-256 |
|---|---|
| `scripts/lean_u2_official_execution_m2.py` | `8c62eacf4303cb7def34703d158f2e199c1aebc441cf2b55ff9a338280f678d3` |
| `scripts/tests/test_lean_u2_official_execution_m2.py` | `3a33a6e3fd7e1cd42bf25127442b59f57c495226fed3edc19768c4cd2704f710` |

The module validates the frozen inputs and lowest-ordinal zero-history shard,
resolves all 64 registrations, renders the environment wrapper and direct
CTest file, normalizes discovery, parses exact pass/fail JUnit, validates
generated-source closure, and projects only bounded local shard credit. Its
CLI exposes only offline `--check`.

## 3. Validation retained before publication

The exact parity-docs command surface was invoked directly because `just` was
not installed in the execution environment. Results:

- 258 Python tests passed with one intentional skip;
- all parity authority generators and `--check` validators passed;
- the complete-parity registry retained 0 complete populations, 0 complete
  axes, 0 paired cells, and 0 satisfied terminal gates; and
- `check-parity-docs.py` retained 992 SMT-LIB fixture files, 753 decisions, 680
  comparisons, and zero recorded disagreement within those named fixtures.

The thirteen M2-focused tests reject:

1. resealed spec command, environment, resource, case, parent, or credit drift;
2. wrong shard selection, ordering, count, command, or CTest property;
3. skipped/disabled, missing, reordered, malformed, or aggregate-inconsistent
   JUnit;
4. terminal/JUnit disagreement;
5. undeclared, missing, malformed, or incomplete generated artifacts;
6. malformed source manifests;
7. forged JUnit summaries or JUnit/post linkage; and
8. frozen repository-input or lowest-zero-history rule drift.

The offline check reports:

```text
LEAN_U2_M2_CONTRACT|cases=64|first=compile/uint_fold.lean|last=docparse/block_0004.txt|live_execution=false|outcomes=0|pairs=0|parity=0
```

### 3.1 Completion-store checkpoint

| Source | SHA-256 |
|---|---|
| `scripts/lean_u2_official_execution_m2.py` at `57dcf343` | `cb57a133f8208df089b6f303d703fcaaca673c0ace4e564ca94b36e7427519a5` |
| `scripts/lean_u2_official_execution_m2_store.py` | `70cf04d2207afcbc86a6448cf38478ecad6541057da781a56bdc51669aee006f` |
| `scripts/tests/test_lean_u2_official_execution_m2_store.py` | `8d878a8abdd8e6258a70852896a5a2d5630ee342a50ad3338563c1efd2579cda` |

The store freezes 15 JSON record paths, four raw payload paths, two harness
artifact paths, `cases/0000.json` through `cases/0063.json`, the exact generated
artifact namespace, and `completion.json` last. It verifies canonical seals,
read-only regular files, raw descriptors, harness/discovery/JUnit/post links,
exact per-case reconstruction, generated payload hashes, namespace closure,
and the final dependency digest. Four focused tests cover successful round-trip
plus missing/extra records, nested extras, early completion, case/raw/generated
mutation, symlink/mode drift, overwrite conflict, and resealed completion
tampering. The full parity-doc surface passed 262 tests with one intentional
skip and every generator/check.

```text
LEAN_U2_M2_STORE|json=15|raw=4|artifacts=2|cases=64|live_execution=false|outcomes=0|parity=0
```

### 3.2 One-shot runner checkpoint

| Source | SHA-256 |
|---|---|
| `scripts/lean_u2_official_execution_m2_run.py` | `bb6d484f542369c42679c816deb5d7cce132dc57df22f1bbc64320026f4961e4` |
| `scripts/tests/test_lean_u2_official_execution_m2_run.py` | `1c86f48e432ba1988e7905239f766f458ea0ac051bda8a9b3e60072256292f2d` |

The runner enforces a clean full implementation revision equal to its tracking
ref, new work/evidence roots, exact frozen authorities, `git archive` at the
pinned Lean tree, all selected source/sidecar/runner identities, the released
toolchain and bundled-compiler probe, local tool identities, exact harness/
discovery semantics, observed platform and storage class, frozen lane/shard/
run/prelaunch records, process-group cleanup, strict terminal/JUnit agreement,
case-before-post ordering, generated-artifact closure, and final store
validation.

Five focused tests cover exact synthetic discovery and records, discovery
mutation before process creation, run/prelaunch linkage and resealed drift,
fake exited and launch-failed terminals plus telemetry/exit mutation,
selected-source drift, and explicit CLI gating. No test invokes CTest. The full
parity-doc surface passed 267 tests with one intentional skip and every
generator/check.

```text
LEAN_U2_M2_RUNNER|cases=64|store_cases=64|lane=official-ctest-local-8g-lean-j1-shard64-v1|run_command=true|live_execution_observed=false|outcomes=0|parity=0
```

## 4. Exact non-claims and next step

This checkpoint does not establish a CTest discovery, an official case
outcome, completion of shard `0001`, a parent-selection completion, provider
reproduction, an Axeyum outcome, a matched pair, performance, an axis, a gate,
or Lean parity.

Next revalidate the committed runner's external preflight inputs from the clean
pushed revision: exact Lean source repository/tree, released toolchain root and
compiler closure, local tool identities, new work/evidence roots, storage
class, and unchanged authorities. Invoke `run-m2` at most once only if every
preflight remains exact. Any mismatch stops before live harness discovery; any
post-launch failure is retained without retry under this plan.
