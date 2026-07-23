# Lean U2 TL0.6.3 M2 R3 attempt-002 result — retained wall timeout

Status: **attempt consumed; watchdog timeout retained and group reaped; zero
official outcome or parity credit**

Date: 2026-07-23

Authority:
[`lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-result-v1.json`](lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-result-v1.json)

## 1. Bounded verdict

From clean, tracking-equal, remote-equal revision
`0a4d5daa966bd6029885edeb46bdeaa63e81b545`, exact external preflight
validated the new roots, pinned source/toolchain, frozen plan/module/test
hashes, R1/R2 history, 323,066,023,936 available bytes, and a harmless direct
Lean probe that observed `LEAN_STACK_SIZE_KB=524288`. `run-r3` was then invoked
once.

CTest printed seven passes and started `compile_bench/channel.lean`. That test
completed its first zero-capacity SPSC measurement, then its work-root-only
capture reported `failed to create thread`. The partially created producer set
blocked on the zero-capacity channel after a required dedicated thread was not
created. CTest never advanced, emitted no JUnit, and hit the preregistered
one-hour watchdog.

The runner sent SIGTERM to process group 710880, reaped the direct child, and
observed no live non-zombie member. It retained terminal class `wall-timeout`
at 3,600,038 ms and stopped before JUnit, case, post, projection, or completion
records. Attempt 002 is consumed and cannot retry.

## 2. Exact retained evidence

| Field | Value |
|---|---|
| run / attempt / sequence | `tl0.6.3-m2-release-linux-shard-0001-v2` / `attempt-002` / 2 |
| work root | `/home/mjbommar/.cache/axeyum-tl063-m2-r3-0a4d5daa` |
| evidence root | `docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m2-shard-0001-r3-attempt-002` |
| retained state | 17 read-only files / 4,908,035 bytes |
| evidence manifest | domain `axeyum-lean-u2-official-execution-m2-r3-incomplete-evidence-v1`; `bc128116c467b95f31502a83223c2e44f953bf5defe21cd08cb52f2a5aa95db8` |
| prelaunch record | `61fe738d0984730cf5af005c73e8c4f9a68d8fc33a04c442de474e4107bcaae8` |
| terminal record | `c228a80ef0dec5204a2cd1d9478faef8273f778bf36c12c6d2fbd31262b7c6f6` |
| raw CTest stdout | 1,009 bytes; `bbbdc413a709f75c5ec3ebd564fd1fc8f972c3fcd434eb6385f325872cb38475` |
| raw stderr | 0 bytes |
| JUnit / cases / post / projection / completion | absent / 0 / absent / absent / absent |

The retained CTest stream is sufficient to identify seven printed passes and
the eighth started case, but not to credit any of them. The 62-byte channel
capture remains a work-root diagnostic, not a payload in the immutable
evidence root; its SHA-256 is
`56a2a5f4c31cbf501018a65497cfaccc34ad2b4fb8d26abdf71962cc0b28e790`.

## 3. Correction learned and non-claims

The universal environment correction worked: the released runtime probe saw
512 MiB, the five compile cases and first two compile-bench cases passed, and
the channel test created more dedicated threads than R1 did. It was not enough
to close the channel benchmark under the unchanged 8 GiB address-space lane.
The terminal's 20,058,112-byte peak RSS is a direct-CTest-child sample only and
is not a descendant-aware performance measurement.

Current cumulative U2 credit therefore remains the M0 history: two decided
official outcomes for one unique case. There are now six consumed process
attempts—four M0, invalid M2 R1, and timeout M2 R3—with zero credited M2 cases
or shards. There is still no official provider completion, Axeyum outcome,
matched pair, performance row, complete population, complete axis, satisfied
gate, or Lean parity.

Any later work must first publish this exact failure and use a new source-first
plan. It may study a smaller universal stack, a larger address-space lane, or
family-aware isolation/timeout, but R3 authorizes none of those changes and no
retry.
