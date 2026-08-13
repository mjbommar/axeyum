# QF linear A5 IDL DL scan telemetry v1 result — 2026-08-11

## Outcome

The [preregistered telemetry](qf-linear-a5-idl-dl-scan-telemetry-v1-preregistration-2026-08-11.md)
is result-invariant on all four named cases and exposes the actual DL shapes.
The failed v1 extended-slice predicate used the wrong side of the equality
boundary: both lost targets are large and equality-heavy, while the protected
fallback control is moderate and equality-heavy.

## Identity and gates

Exact local source was
`27644b0264d7675a31799e69cabdd182561b3a75`, whose only code change appends
already-computed counts to post-scan timeout details. The 11,873,168-byte
release binary had SHA-256
`8c47faf1872b955f25368badf537bc697b73cd29ca39be49dd03651162bc29f4`.
Focused telemetry, zero-budget, and UNSAT tests passed with nonzero counts;
strict full-feature solver-library Clippy passed; and the complete solver
library passed 1,092/1,092 tests.

The group started at `2026-08-11T22:19:38Z` with one-, five-, and
fifteen-minute loads 6.16, 6.31, and 6.30. Every 24,000 ms / 8 GiB worker exited
0 with zero stderr. After replacing only the appended `dl-online` timeout
detail with one marker, each record was byte-identical to its unchanged
`d0e0d6cea` counterpart.

| Case | Verdict / terminal route | DL atoms | Numeric equality gates | Boolean equality gates | CNF vars / clauses | Wall / peak RSS |
|---|---|---:|---:|---:|---:|---:|
| BubbleSort loss | `unknown` / `lia-dpll` | 7,095 | 2,028 | 712 | 88,179 / 239,829 | 42.97 s / 182,668 KiB |
| GraphPartitioning loss | `unknown` / `lia-dpll` | 2,199 | 855 | 2,065 | 15,430 / 34,078 | 18.05 s / 28,356 KiB |
| `lpsat-goal-18` control | UNSAT / `lia-dpll` | 906 | 350 | 0 | 18,695 / 49,274 | 23.02 s / 63,824 KiB |
| maze gain | UNSAT / `lia-dpll` | 724 | 1 | 3,455 | 23,589 / 56,002 | 19.17 s / 45,404 KiB |

The JSONL SHA-256 values in table order are
`19ac7279ad62a57360123b262153cf4ebf269a97c4f23c6289dda1d7a1ac75bd`,
`fa44e6bb94ab4d30a9fbeb3faf99e47a85cabaf43311d6e073559b1b8d8d6aae`,
`13652b5e67c9777c4450fbd5a6797f3c3c91c7a8fe78ad7d65f74f230b414f39`,
and `2a90fe18f0f21ee29d0c1adfa746f1a2c6742fc65f27121802ecdb14ea7c8275`.
Full files remain under
`/home/mjbommar/.cache/axeyum/a5-idl-dl-telemetry-v1-matrix`.

## Decision

Retain the timeout telemetry: it changes no result or search behavior and
prevents another proxy-based threshold. The next candidate may extend only the
large equality-heavy shape (`atoms > 1,024` and `equality_gates >= 128`), while
the 906/350 `lpsat` class must remain on the accepted 12-second split and every
other class keeps its existing maximum. Proceed only under the separately
preregistered v2 candidate.
