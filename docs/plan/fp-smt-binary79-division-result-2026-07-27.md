# SMT `(15,64)` symbolic division validation — 2026-07-27

## Bounded verdict

Axeyum now admits symbolic division for SMT-LIB `(_ FloatingPoint 15 64)` through
the existing pure-Rust wide-BV circuit. The operator matched an independent
79-bit IEEE `rustc_apfloat` semantics across every rounding mode, and both exact
public rows which selected the change move from format-validation refusal to
declared/Z3-matching UNSAT results in about 50 ms.

This is an operator-specific extension of ADR-0368. The common arithmetic
allowlist remains unchanged, and symbolic `(15,64)` sqrt and FMA remain directly
tested unsupported.

## Implementation and oracle

Implementation commit:
`0f406ad489880487efabf30a893a562b66fd3bcd`.

ADR-0369 adds a division-only format predicate and permits the `(15,64)`
circuit's 133-bit intermediate through the established wide-BV path. Exact
ground division, every previous format, the IR, solver trait, replay path, and
native dependency boundary are unchanged.

The private `rustc_apfloat` oracle uses `BITS = 79`, `EXP_BITS = 15`, matching
SMT's implicit-integer-bit layout rather than x87's 80-bit explicit encoding.
Division agrees in all five rounding modes over 12×12 structured Cartesian pairs
and 512 deterministic random pairs per mode: 3,280 input/mode cases, zero
non-NaN bit mismatch, and zero NaN-class mismatch. Structured inputs include
both zeros, infinities, NaN, minimum subnormal, maximum finite, ordinary finite,
and sign/exponent boundaries.

## Exact gains and retained set

The two formerly unsupported rows are:

| row | expected/current | cold total |
|---|---:|---:|
| `units_meter_ft/query.116.smt2` | UNSAT | 50.344 ms |
| `nan_longdouble/query.07.smt2` | UNSAT | 47.973 ms |

The combined artifact also retains all four ADR-0368 add/sub/mul gains:
two SAT / four UNSAT, zero unknown / unsupported / error, 6/6 agreement with Z3
4.13.3, zero model-replay failures, and PAR-2 mean 0.371 s.

Local artifact:
`/tmp/axeyum-qfbvfp-binary79-div-retained-20260727.json`, SHA-256
`c911d4d5625963421136750b1121b0c5c586af12acc17540d14c5fe7ee175839`
(not committed, so not durable evidence by itself). The exact release benchmark
and SMT-COMP CLI binaries have SHA-256
`eb8e63a98774d5299efee0c978e9a133ff227a737969277f82893e28f956cebd`
and `2f9e545fa0f498d4bfc601d2a8620e1ba0f50519017a32b5faf7d4b43059de05`.

The frozen 108-family process diagnostic reports 87 correct, zero wrong, 19
unknown, and two process timeouts. Relative to the immediate 83-correct
add/sub/mul run, only the two exact division rows are credited; the other two
aggregate recoveries are load-sensitive timeout variation.

## No-loss and verification

The standalone process-isolated ESBMC gate remains 34/34 correct with zero
unknown, wrong, process-timeout, or other outcome. A concurrent run of that gate
and the 108-family census produced two ESBMC outer timeouts; the isolated rerun
recovered both, so the concurrent result is a disclosed host-contention negative,
not accepted no-loss or timing evidence.

Completed gates:

- `cargo test -p axeyum-fp smt_binary79_apfloat_tests`: 4 passed;
- `cargo test -p axeyum-fp --all-features`: 68 unit, 11 full-faithfulness, 14
  simple-faithfulness, and two width-guard tests passed; doc-tests passed;
- `cargo clippy -p axeyum-fp --all-targets --all-features -- -D warnings`:
  passed;
- `cargo fmt --all --check`, documentation links, and `git diff --check`:
  passed before the implementation commit.

Full `just check`, remote CI, push, origin/main integration, proof-producing
UNSAT, and credited full-library completion are not claimed.

## Next bounded step

Selected `sqr_longdouble` rows now stop at symbolic `(15,64)` sqrt. Sqrt needs
the exact rounding-interval oracle used for F128 because `rustc_apfloat` exposes
no square-root operator. It therefore requires a separate preregistration and
must retain the six-row binary79 set plus the 34-file ESBMC gate. FMA remains a
later ternary-oracle increment.
