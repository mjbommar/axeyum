# SMT `(15,64)` add/sub/mul validation — 2026-07-27

## Bounded verdict

Axeyum now admits symbolic addition, subtraction, and multiplication for the
SMT-LIB `(_ FloatingPoint 15 64)` format. This is the 79-bit implicit-integer-bit
IEEE layout defined by SMT-LIB, not x87's 80-bit explicit-integer-bit encoding.
The existing pure-Rust circuits run through the wide-BV evaluator and lowering
path; no native solver or FFI dependency was added.

Four deterministic QF_BVFP family representatives move from a format-validation
refusal to definite declared/Z3-matching results: two SAT and two UNSAT, with
zero disagreement, error, or model-replay failure. Symbolic `(15,64)` division,
sqrt, and FMA remain fail-closed and are directly regression-tested as such.

Follow-up: ADR-0369 subsequently validated symbolic `(15,64)` division and
moved two more rows. Sqrt and FMA remain fail-closed; see the
[division result](fp-smt-binary79-division-result-2026-07-27.md).

## Selection

After closing the 34-file ESBMC hard tail, a new diagnostic selected one file
from each QF_BVFP leaf family which contained a declared SAT or UNSAT status.
Within each family, the lowest SHA-256 of its corpus-relative path won. Of 114
leaf families, 108 had an eligible declared-status file: 50 SAT and 58 UNSAT.

The process-isolated predecessor run at a two-second solver budget and
five-second process ceiling produced 77 correct results, zero wrong results, 29
`unknown` outputs, and two process timeouts. Detailed one-file artifacts showed
that a major explicit bucket was `unsupported construction: fp.add: unvalidated
format` or `fp.mul: unvalidated format` on `(15,64)`.

This selection is a current-code breadth diagnostic, not the official resumable
SMT-COMP selected slice and not a credited full-library run.

## Oracle and implementation boundary

Implementation commit:
`73f91fee66d3f228c28314ccd5603b4093cf550c`.

ADR-0368 keeps the general arithmetic allowlist unchanged and adds a private
operator-specific gate used only by add and mul; sub inherits it through the
exact `a + (-b)` identity. Their 133-bit intermediates use the wide-BV path
already exercised by F128. Div, sqrt, and FMA still consult the old allowlist.

The independent oracle is a private `rustc_apfloat::ieee::Semantics` with
`BITS = 79` and `EXP_BITS = 15`. Add and mul agree bit-for-bit (NaN payloads are
compared by class) in all five rounding modes over:

- 12 structured patterns, including signed zeros, normals, infinities, NaN,
  minimum subnormal, maximum finite, and a generic finite value;
- every structured Cartesian pair; and
- 512 deterministic random pairs per rounding mode.

That is 6,560 operator/mode input pairs with zero non-NaN mismatch and zero
NaN-class mismatch. A separate negative test requires symbolic `(15,64)` div,
sqrt, and FMA to return `IrError::Unsupported`.

## Exact gains

The final clean serial four-row artifact at a five-second budget reports:

| row | expected/current | cold total |
|---|---:|---:|
| `halve_longdouble-flow/query.3.smt2` | UNSAT | 549.973 ms |
| `halve_longdouble-noflow/query.1.smt2` | SAT | 145.225 ms |
| `inf_longdouble/query.13.smt2` | UNSAT | 144.512 ms |
| `ld-add_default/query.2.smt2` | SAT | 1,283.667 ms |

Summary: 2 SAT / 2 UNSAT / 0 unknown / 0 unsupported / 0 errors, 4/4 Z3
agreement, zero model-replay failures, PAR-2 mean 0.531 s.

Local artifact:
`/tmp/axeyum-qfbvfp-binary79-gains-20260727.json`, SHA-256
`e8fa2f925333a748b133624a1ec40dc770d75705db6ad2f0aeb7a42fd4ba75c8`
(not committed, so not durable evidence by itself). The exact release benchmark
and SMT-COMP CLI binaries have SHA-256
`435bd0ebad200a13f8dfa964c9965d3af0363debb58eb9831a197c1b4ec6aa01`
and `1d9bacaa0442d73554f6e48e50beabfd5039a987c9506ea8f13dca3515e39842`.

The post-change 108-family process run reports 83 correct, zero wrong, 23
unknown, and two process timeouts. Only the four rows above are credited:
three other apparent aggregate recoveries are load-sensitive timeout variation,
while `ld-add_default` remains marginal at the shorter two-second concurrent
gate. The exact five-second one-worker evidence establishes the four causal
format-boundary gains without overstating the aggregate delta.

## No-loss and verification

The 34-file ESBMC population remains 34/34 correct with zero unknown, wrong,
process-timeout, or other outcomes under a per-file 15-second process ceiling
and five-second solver budget. A monolithic one-worker harness attempt exceeded
its 120-second outer ceiling under host contention and produced no artifact; it
is not called green or used for timing.

Completed gates:

- `cargo test -p axeyum-fp smt_binary79_apfloat_tests`: 3 passed;
- `cargo test -p axeyum-fp --all-features`: 67 unit, 11 full-faithfulness, 14
  simple-faithfulness, and two width-guard tests passed; doc-tests passed;
- `cargo clippy -p axeyum-fp --all-targets --all-features -- -D warnings`:
  passed;
- `cargo fmt --all --check`, documentation links, and `git diff --check`:
  passed before the implementation commit.

Full `just check`, remote CI, push, origin/main integration, proof-producing
UNSAT, and credited full-library completion are not claimed.

## Next bounded step

The now-visible `(15,64)` residual splits cleanly: selected `nan_longdouble` and
`units_meter_ft` rows stop at symbolic division, while `sqr_longdouble` stops at
sqrt. Division has the strongest ready independent oracle (`rustc_apfloat`) and
should be considered before sqrt; it requires a separate operator-specific ADR
and all-mode sweep, with this four-row gain set and the 34-file ESBMC population
retained as no-loss gates.
