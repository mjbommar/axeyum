# Lean U2 TL0.6.3 M2 R5 diagnostic-closure result

Status: **complete invalid-attempt diagnostic; zero processes, zero outcomes,
zero parity credit**

Date: 2026-07-23

Parents:
[R5 incomplete result](lean-u2-official-execution-tl0.6.3-m2-r5-attempt-003-incomplete-result-2026-07-23.md)
and [diagnostic implementation checkpoint](lean-u2-official-execution-tl0.6.3-m2-r5-diagnostic-closure-implementation-2026-07-23.md).

## 1. Authorized append

The implementation and documentation checkpoints were pushed separately at
`08f23ee4` and `836538af`. Local `HEAD`, tracking ref, and remote branch were
equal at full revision `836538af5cc9828c05da60ecf08294bdcf1a5299` before the
append. `prepare-check` revalidated the frozen 83-file root, unchanged source,
exact 123-row generated tree, 66 retained payloads, 56 metadata-only rows, and
64-pass JUnit record
`38aa3325b66b41ff9333dcffd9ecc6fe4caf1f8877d7f9470b1a6fd9c52a6302`.

One `append` then installed only the previously absent `diagnostic/` namespace.
It launched zero Lean, CTest, harness, discovery, or selected processes.

## 2. Completion-last result

The append adds 68 files / 149,513 bytes:

- 66 exact `.out.produced` and CTest-log payloads / 83,858 bytes;
- one sealed 51,185-byte `post.json`, record
  `d30423aa444dd6b44538b984a6178fff64dc7dda1f2aad1fb09d715b51f186b0`;
- one sealed 14,470-byte `completion.json`, installed last, record
  `2d5d43a7787ccf4333b152be8794a12b45edc7527e32732abb2cf1cce1ffce3c`.

The completion dependency set is bound by
`e01a08ba28547bbd354a23ddecfc81667084e476e762cfb9a1c60d2167bbb680`.
The combined evidence root is 151 files / 5,228,286 bytes. Portable validation
passes from ordinary Git modes, while the live root also passed the exact
read-only-mode check at append time.

## 3. Credit and next action

`LastTestsFailed.log` is explicitly bound as conditionally absent because JUnit
has zero failures. The post still marks attempt 003 invalid under the original
unconditional 124-path contract. Its 64 case rows remain diagnostic only:
official outcomes, shard/provider completions, Axeyum outcomes, pairs,
performance rows, populations, axes, gates, and parity credit are all zero.

R5 is now closed and must not be rerun. The next action is a new source-first
attempt-004 plan that preregisters conditional CTest failure-log semantics,
fresh work/evidence roots, the already-qualified 32 GiB/512 MiB lane, exactly
one selected process, and no retry or retroactive R5 promotion.
