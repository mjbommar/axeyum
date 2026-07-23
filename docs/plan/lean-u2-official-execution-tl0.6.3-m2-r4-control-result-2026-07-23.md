# Lean U2 TL0.6.3 M2 R4 control result

Status: **blocked at no-credit resource control; selected attempt 003 remains
unconsumed**

Date: 2026-07-23

Parents:
[R4 plan](lean-u2-official-execution-tl0.6.3-m2-r4-attempt-003-plan-2026-07-23.md),
[implementation](lean-u2-official-execution-tl0.6.3-m2-r4-attempt-003-implementation-2026-07-23.md),
and [fanout R1 correction](lean-u2-official-execution-tl0.6.3-m2-r4-fanout-control-r1-implementation-2026-07-23.md).

## 1. Clean invocation boundary

The corrected controls ran from clean pushed revision
`628c59110ecf1886290426fcb62d8d3ff9b79705`, with local, tracking, and remote
refs equal. Both frozen selected roots were absent before and after the
controls:

- `/home/mjbommar/.cache/axeyum-tl063-m2-r4-628c5911`;
- `docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m2-shard-0001-r4-attempt-003/`.

Offline validation first reconstructed 64 cases, 124 generated paths, and the
17,179,869,184-byte limit with zero selected processes/outcomes/pairs/parity.
The direct environment probe then exited zero and observed `524288` from
released Lean.

## 2. Fanout result

The corrected 274-byte fanout source has SHA-256
`1896ef8218e617aff7557e1c1bcd14790207029e0c7ce3850d9403f2d1df1db3`.
It elaborated and began constructing nine dedicated tasks under the exact
16 GiB limit and stack environment, but emitted the exact 24-byte stderr
payload `failed to create thread\n` (SHA-256
`49bde1c1e0120362695937d03a4de3644ad331a42e9c670f6b47338e358dc39b`).
Stdout remained empty (SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`).

A read-only `/proc` snapshot while the control was blocked observed:

| Field | Value |
|---|---:|
| `RLIMIT_AS` soft/hard | 17,179,869,184 bytes |
| `VmPeak` | 16,504,496,128 bytes |
| current `VmSize` | 4,626,194,432 bytes |
| current `VmRSS` | 492,204,032 bytes |
| current thread count | 3 |

These process values diagnose the local address-space failure; they are not
performance evidence. The 120-second control watchdog reaped the process group
and a subsequent group/PID check found no survivor. The current adapter raises
on a failed control and removes its temporary directory, so this observation
does not claim a completion-grade retained control record. That evidence gap is
itself part of the result and must be closed before another lane is selected.

## 3. Credit and next boundary

The fanout control had an empty selected-case set and failed before authorizing
`run-r4`. No official source capture, work/evidence root, harness, discovery,
prelaunch record, CTest, JUnit, case, post, projection, or completion exists.
Therefore:

- selected attempt 003 and sequence 3 remain unconsumed;
- R4 grants zero official, provider, Axeyum, pair, performance, population,
  axis, gate, or parity credit;
- the 16 GiB lane is rejected for this exact 512 MiB-stack/nine-task control;
- the selected shard remains forbidden under R4.

The next step is a new source-first resource qualification. It must retain
failed-control terminal evidence, preserve the exact stack/shard/command/store,
and choose any larger address-space lane before observation. It may reuse
attempt 003 only because no selected process, discovery, or selected root was
created.
