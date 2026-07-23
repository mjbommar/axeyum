# TL0.6.3 M0 R3 result-projection amendment

Status: **preregistered after execution; no result adapter implemented and no process rerun permitted**

Date: 2026-07-22

Parent work:

- [`R3 plan`](lean-u2-official-execution-tl0.6.3-m0-r3-plan-2026-07-22.md)
- [`R2 result`](lean-u2-official-execution-tl0.6.3-m0-r2-result-2026-07-22.md)

## 1. Frozen execution result

Attempt 004 ran once from committed and pushed implementation revision
`d0390561a3044ccd6785cb1fdb0a3be2fb41d0bb`. The exact official
`compile/534.lean` case passed and its evidence validates read-only. No official
process may be rerun as part of this amendment.

| Field | Frozen value |
|---|---|
| attempt / sequence | `attempt-004` / 4 |
| implementation revision | `d0390561a3044ccd6785cb1fdb0a3be2fb41d0bb` |
| R3 runner physical SHA-256 | `061a7eca2e54f274c7289de4217d80db9a02f8e6f611f31667f7f01f059d835d` |
| R3 test physical SHA-256 | `73d7aa1f3facb2572c632a1804cbfdc24a7dc6f5c53d3e6e34314dc1e660cb90` |
| evidence files / bytes | 24 / 8,953,979 |
| evidence manifest | `982c0481784bf487995d76b6caf5c27e24d7c170115a114dccfa53d054327c78` |
| terminal record | `f3d04115b62a582122fb3fa5dee1f9818cf5e44791e928475bcd2a10a4874607` |
| JUnit record | `1cb384c6b4fd9655e79387a2d1aaa7845535fd621b2922f8a3ecf2c6a66dde0d` |
| case record | `64fbf989ec5e458f6e8b69bad71c4c6532cd73e4be70baa998ffae4f702289eb` |
| completion record | `a997934b49ef1fbb2be6322b49279dc3f183c22c2436e6fe05e211f722dcd240` |
| outcome | passed |

The retained pass includes the exact generated 9,713-byte C file from R1 plus
a 4,155,184-byte executable, the produced-output sidecar, two pass-side CTest
logs, bundled compiler/linker evidence, source replay, completion-last
installation, and a reaped process group.

## 2. Post-execution projection defect

Evidence validation passed. Result generation then stopped before writing any
authority or summary because the R3 result validator required every claim to
be false. The underlying result builder correctly retained two bounded positive
facts:

- `official_lean_case_observed = true`; and
- `local_shard_complete = true`.

It kept `parent_profile_complete`, `official_provider_reproduced`,
`axeyum_observed`, `matched_pair_formed`, `performance_measured`, and
`lean_parity_established` false. The validator confused bounded observation
claims with terminal parity claims. This is a post-execution result-projection
defect, not an execution, evidence, or semantic failure.

## 3. Permitted correction

A separate result adapter may be implemented only after this amendment is
committed and pushed. It must:

1. leave the R1, R2, and R3 execution runners, tests, plans, and every retained
   evidence byte unchanged;
2. freeze the implementation revision, runner/test digests, evidence manifest,
   terminal/JUnit/case/completion records, and `passed` outcome above;
3. call the frozen R3 evidence/result builder without launching CTest;
4. require exactly the two bounded positive claims and all six terminal-scope
   claims false;
5. publish a new result schema whose source inputs include the adapter and its
   tests; and
6. retain four process attempts, two incomplete attempts, two decided official
   outcomes, one pass, one failure, one unique observed case, zero Axeyum
   outcomes, zero pairs, zero performance rows, and zero parity credit.

Normal CI must replay the result offline and must never execute the official
case.

## 4. Stop conditions and non-claims

Stop without publishing a result if any frozen byte, record, attempt relation,
claim boundary, source input, or evidence closure differs. Do not edit the
execution harness or evidence and do not rerun attempt 004.

One local pass plus one earlier local failure for the same singleton does not
complete the 3,678-case parent, reproduce an official provider, observe Axeyum,
form a semantic pair, measure performance, advance A0--A11, satisfy G1--G10,
or establish Lean 4 parity.
