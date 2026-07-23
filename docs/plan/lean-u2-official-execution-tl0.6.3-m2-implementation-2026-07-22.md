# Lean U2 TL0.6.3 M2 offline implementation checkpoint

Status: **implemented, validated, committed, and pushed; no live harness
discovery or test process has run**

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

This checkpoint deliberately adds no live process-launch command. It creates
no live harness, runs no discovery command, launches no CTest process, and
publishes no attempt or case outcome. The separate launch/store runner remains
a precondition for the plan's single authorized attempt.

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

## 4. Exact non-claims and next step

This checkpoint does not establish a CTest discovery, an official case
outcome, completion of shard `0001`, a parent-selection completion, provider
reproduction, an Axeyum outcome, a matched pair, performance, an axis, a gate,
or Lean parity.

Next implement the launch/store runner only from the frozen plan and this pure
contract. It must reuse the accepted process/store primitives, retain exact
source/toolchain/discovery/raw/JUnit/artifact/terminal records, remain
completion-last, and expose at most the single preregistered attempt. Commit and
push that implementation before any live harness construction or discovery.
