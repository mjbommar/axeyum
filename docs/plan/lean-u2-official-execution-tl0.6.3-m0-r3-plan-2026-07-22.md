# TL0.6.3 M0 R3 plan — close the direct-entry contract

Status: **preregistered; no R3 runner, harness, or official test process has run**

Date: 2026-07-22

Parent work:

- [`M0 plan`](lean-u2-official-execution-tl0.6.3-m0-plan-2026-07-22.md)
- [`R1 result`](lean-u2-official-execution-tl0.6.3-m0-r1-result-2026-07-22.md)
- [`R2 plan`](lean-u2-official-execution-tl0.6.3-m0-r2-plan-2026-07-22.md)
- [`R2 result`](lean-u2-official-execution-tl0.6.3-m0-r2-result-2026-07-22.md)
- [`TL0.6.3`](lean-system-implementation-plan-2026-07-21.md#tl06-u2-official-test-execution-slices)

## 1. Decision boundary

R3 permits one new attempt of the same registered official case, source,
released toolchain, CTest filter, resource envelope, bundled-compiler contract,
artifact closure, and zero-credit boundaries. It corrects one adapter defect:
the published runner must be directly executable from the repository root
without relying on an ambient `PYTHONPATH` or changing the invocation to
`python -m`.

No R3 runner or official process may run until the R2 invocation authority,
R2 result, and this plan are committed and pushed. The R3 implementation and
offline direct-entry smoke tests must then be committed and pushed separately
before attempt 004.

R3 can add at most one local official-case outcome. It cannot complete the
3,678-case parent, reproduce an official provider, create an Axeyum outcome or
pair, publish performance, advance A0--A11, satisfy G1--G10, or establish Lean
4 parity.

## 2. Frozen three-attempt history

R3 must retain and validate all earlier attempts without reinterpretation:

| Attempt | Sequence | State | Official outcomes |
|---|---:|---|---:|
| `attempt-001` | 1 | incomplete resource/evidence-adapter failure | 0 |
| `attempt-002` | 2 | complete local official failure | 1 |
| `attempt-003` | 3 | failed before R2 runner import | 0 |

The R2 invocation authority is frozen at:

| Field | Value |
|---|---|
| authority physical SHA-256 | `662f9e399660c0cca676988e7b4a7f9ba3a0f2dd3469e0b6313e09c56d6a18fc` |
| authority record SHA-256 | `efcf5236090d712923ac083c470f407d56cb26b7a67a83724ba89ba02b5194ed` |
| R2 implementation revision | `660915572968435f68b7a08fd95e737db6ef7762` |
| R2 runner physical SHA-256 | `c9fa1a2b54decb03486c43514c632713337768b471971a9e2359c5c1d8dca03b` |
| terminal | exit 1; 0-byte stdout; 265-byte stderr |
| roots / harness / CTest | absent / not prepared / not launched |

Attempt 003 remains a process attempt but contributes no official outcome.
If R3 reaches a decided outcome, the final history must count four process
attempts, two incomplete attempts, two decided official outcomes, attempt
002's retained failure, and attempt 004's result.

## 3. Direct-entry correction

R3 uses attempt ID `attempt-004`, sequence 4, and lane
`official-ctest-local-8g-lean-j1-bundled-cc-v4`. Its entry file may add only
the resolved repository root to `sys.path` before importing repository
packages. It must not:

1. edit the frozen R1 or R2 runners;
2. set `PYTHONPATH`, depend on user site packages, or select a different
   interpreter after launch;
3. replace direct-file execution with `python -m` for the official command;
4. alter the R2 wrapper correction, bundled compiler/static-library checks,
   case/filter, source/toolchain, task-stack policy, workers, limits, watchdog,
   artifact closure, or immutable-store rules; or
5. reuse an earlier attempt ID, sequence, work root, evidence root, or result
   authority.

This follows Python's specified path initialization: direct-file execution
prepends the script directory, while `-m` prepends the current directory.
[Python command-line interface](https://docs.python.org/3/using/cmdline.html#interface-options)
and
[`sys.path` initialization](https://docs.python.org/3/library/sys_path_init.html)
are the primary references.

## 4. Required offline gates

Before execution, normal offline tests must:

1. validate the exact R2 invocation authority, embedded stdout/stderr bytes,
   record seal, physical digest, root-absence claims, and zero credit;
2. execute `python3 scripts/lean_u2_official_execution_r3.py --help` from the
   repository root with a minimal explicit environment and require exit zero;
3. reject entry bootstraps that insert any path other than the resolved
   repository root or that run after repository-package imports;
4. prove R1 and R2 runners remain byte-identical and replay the R1 authority;
5. validate the exact four-attempt/credit aggregation for both possible R3
   outcomes;
6. reject any `LEAN_CC`, `PYTHONPATH`, worker, stack, resource, command,
   selection, source, compiler, artifact, completion, or claim drift; and
7. remain offline and never run CTest implicitly.

The implementation may run a fresh compiler-only probe while developing the
R3 contract, but no CTest discovery, harness preparation, or official case
process may occur before the implementation commit is pushed.

## 5. Attempt and result identities

Attempt 004 must use fresh private and evidence roots. Its spec must bind the
R3 plan digest, preregistration commit, implementation commit, R2 invocation
authority physical/record digests, and cumulative attempt-history digest.
The final R3 authority and generated summaries must be new files; neither the
R1 result nor R2 invocation record may be overwritten.

A pass still requires the exact R2 bundled-compiler proof, terminal/JUnit
agreement, pass-side artifact closure, original-source replay, immutable
completion-last installation, and a reaped process group. A genuine case
failure may add one official failure only if the same contracts validate.

## 6. Stop conditions

Stop and retain R3 if direct entry, any frozen dependency, compiler selection,
process closure, JUnit relation, source/artifact closure, or immutable-store
step fails. Do not silently switch invocation mode, install packages, change
resources, alter the case, or retry again without a separately published R4
plan.

Even if attempt 004 passes, complete Lean parity remains at zero complete
populations, zero axes, zero matched cells, and zero gates until the complete
framework contract is fulfilled.
