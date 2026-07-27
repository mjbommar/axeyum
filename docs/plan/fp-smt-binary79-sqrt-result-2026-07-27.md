# SMT `(15,64)` symbolic square-root validation — 2026-07-27

## Bounded verdict

Axeyum now admits symbolic square root for SMT-LIB `(_ FloatingPoint 15 64)`
through the existing pure-Rust wide-BV circuit. An exact dyadic oracle validates
correct rounding in all five SMT modes, including directed-rounding boundaries
and tie behavior. Both public rows which selected this increment move from
format-validation refusal to replay-checked SAT and agree with Z3.

This is an operator-specific extension accepted by ADR-0370. The common
arithmetic allowlist is unchanged, and symbolic `(15,64)` FMA remains directly
tested unsupported.

## Implementation and exact oracle

Implementation commit: `ab4b580310d4cbe2755e34a40ebf0a3083e1cfba`.

The sqrt-specific gate admits exactly `(15,64)` in addition to the established
formats. Its 138-bit intermediate uses the existing C-free wide-BV path; no IR,
solver-trait, model-replay, dependency, or evidence boundary changes.

Because `rustc_apfloat` has no sqrt operation, the private oracle decodes inputs
and candidates as exact dyadics and compares arbitrary-width integer squares.
Nearest-even and nearest-away use exact squared midpoints with their distinct tie
rules. Toward-positive requires the candidate square to bound the input from
above; toward-negative and toward-zero require the positive root to bound it
from below. NaN, negative, infinity, and signed-zero cases follow their
SMT/IEEE special rules.

The all-mode `(15,64)` sweep covers 12 structured and 512 deterministic random
inputs per mode: 2,620 input/mode cases, zero rejection. For every applicable
positive finite result, both adjacent encodings are also required to fail the
oracle. The existing native-F64 RNE sweep and F128 RNE sweep pass through the
same generalized checker.

## Exact gains and retained set

The newly admitted rows are:

| row | expected/current | cold total |
|---|---:|---:|
| `sqr_longdouble-flow/query.1.smt2` | SAT | 0.755 s |
| `sqr_longdouble-noflow/query.1.smt2` | SAT | 2.592 s |

The combined retained artifact includes all six ADR-0368/0369 gains: four SAT /
four UNSAT, zero unknown / unsupported / error, 8/8 agreement with Z3 4.13.3,
zero model-replay failures, and PAR-2 mean 0.932 s.

Local artifact:
`/tmp/axeyum-qfbvfp-binary79-sqrt-retained-20260727.json`, SHA-256
`86a395872cd2414a106b7661d6d59a6e0141b70018bfa084a99a287dc3146f87`
(not committed, so not durable evidence by itself). The release benchmark and
SMT-COMP CLI binary digests were recorded with the local run; the artifact is
supporting local evidence rather than a committed immutable result.

The frozen 108-family process diagnostic reports 88 correct, zero wrong, 18
unknown, and two process timeouts. Relative to the immediate post-division run,
only the two exact sqrt rows are credited; aggregate variation remains
host-load-sensitive. No selected row contains `(15,64)` FMA, so this result does
not authorize speculative FMA implementation.

## No-loss and verification

The fresh serial ESBMC process gate is 34/34 UNSAT with zero wrong or unknown
outcome. Under an unrelated high-CPU Java workload, 33 rows passed in the first
sweep and `Float4_1-main.smt2` hit the 30-second outer limit; its immediate
standalone rerun passed in 4.01 s at 97% CPU. The ESBMC corpus contains no
`(15,64)` declaration, so the new format gate is structurally unreachable there.
The timeout is retained as host-contention evidence, not a solver regression or
timing datum.

Completed gates:

- `cargo test -p axeyum-fp smt_binary79`: five passed;
- `cargo test -p axeyum-fp --all-features`: 69 unit, 11 full-faithfulness, 14
  simple-faithfulness, and two width-guard tests passed; doc-tests passed;
- `cargo clippy -p axeyum-fp --all-targets --all-features -- -D warnings`:
  passed;
- `cargo fmt --all --check`, documentation links, and `git diff --check`:
  passed before publication.

Full `just check`, proof-producing UNSAT, a refreshed full-library run, and any
parity claim remain outside this increment.

## Next bounded step

Reclassify the 20 non-decisions in the frozen family sample by front-door
failure reason and measured cost. FMA has no selected `(15,64)` demand, so it
must stay fail-closed unless a fresh deterministic corpus selection justifies a
separate ternary-oracle preregistration.
