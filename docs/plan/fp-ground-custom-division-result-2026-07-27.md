# Ground custom-format `fp.div` result — 2026-07-27

## Outcome

The last unsupported row in the committed eight-file
`QF_BVFP/bitwuzla-regress-clean` slice is now decided. The public
`solver__fp__issue130.smt2` query uses only ground operands in the IEEE-style
`(_ FloatingPoint 4 12)` format. Axeyum returns the declared `sat`; the negation
of its exact equality returns `unsat`.

This is one bounded P2.8 coverage increment, not general floating-point parity.
The committed baseline before this change was 7/8 decided. Combined with the
finite-domain preprocessing repair, tested commit
`a3c4b04f9729defe1ebf496ee3d92d6decab24bb` is 8/8 decided with zero known-
status disagreements and zero model-replay failures.

## Design and soundness boundary

`axeyum-fp::div` now has an exact ground route for IEEE-style formats that are
outside the symbolic arithmetic allowlist. It decodes the two finite operands as
exact dyadic integers, forms an arbitrary-precision rational quotient with the
existing `num-bigint` dependency, and rounds once to the target format under all
five SMT-LIB rounding modes. NaN, infinity, signed-zero, overflow, normal, and
subnormal cases are handled explicitly.

The boundary is deliberately narrow:

- both operands must be constants;
- the format must use IEEE infinity/NaN conventions, fit in the IR's 128-bit
  scalar value, have `2 <= exp_bits < 63`, and have at least two significand
  bits;
- symbolic custom-format division still returns `Unsupported`;
- validated standard formats continue through the established symbolic circuit,
  preserving its independent oracle coverage and formula topology;
- the result remains an ordinary bit-vector/Float value and the existing SAT
  model-replay route is unchanged.

This completes an existing public operator at its ground boundary under
ADR-0023, ADR-0026, and ADR-0028. It does not add an operator, backend, evidence
format, or symbolic encoding, so no new ADR is required.

## Independent validation

The exact integer helper is checked independently rather than trusted because
FP UNSAT replay shares the lowering implementation.

- `rustc_apfloat` checks 5,720 F32 quotients (1,144 operand pairs times five
  rounding modes) and 1,105 F128 quotients (221 pairs times five modes). NaNs
  are compared by class; all other results are bit-exact. Total: 6,825 oracle
  comparisons.
- Direct Z3 4.13.3 parsing checks 20 deterministic `(4,12)` finite/nonzero
  pairs under all five rounding modes. Each script asks whether any Axeyum
  quotient differs; all five 20-term mismatch disjunctions are `unsat` (100
  custom-format quotient comparisons).
- A separate extreme-exponent regression exercises deep underflow, directed
  minimum-subnormal rounding, positive overflow, and inward saturation without
  constructing impractically large big integers.
- The public query is an end-to-end `sat` regression and its negation is an
  end-to-end `unsat` regression at `solve_smtlib`.

The local Bitwuzla 0.9.1 reference binary is not counted as an oracle: it was
built without `--fpexp` and explicitly rejects `(4,12)` as an experimental FP
format. cvc5 is not installed locally. The raw public query independently
returns `sat` under the Z3 4.13.3 CLI.

## Focused performance and coverage evidence

The final integrated product-backend artifact used a 10-second safety timeout
and four jobs. It records clean source revision
`a3c4b04f9729defe1ebf496ee3d92d6decab24bb` and reports:

| measure | result |
|---|---:|
| files / decided | 8 / 8 (100%) |
| expected / outcome | `sat` / `sat` |
| unsupported / disagree | 0 / 0 |
| model replay failures | 0 |
| post-parse DAG nodes | 1 |
| cold total | 1.381 ms |
| model replay | 0.049 ms |

The timing is a single local debug-build observation, not a competitive
performance claim. The important structural result is that the fully ground
assertion folds to one Boolean DAG node.

The integrated eight-file refresh completes at 5 SAT / 3 UNSAT, 100% decided,
DISAGREE=0, and zero replay failures. Z3 compares 7/8 with zero disagreement;
the custom row's independent evidence remains the direct raw-SMT Z3 battery.

## Reproduction

```sh
CARGO_BUILD_JOBS=2 cargo test -p axeyum-fp --lib
CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --features z3 \
  --test fp_ground_division
CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-fp --all-targets -- -D warnings
CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --features z3 \
  --test fp_ground_division -- -D warnings
z3 -T:10 corpus/public-curated/non-incremental/QF_BVFP/\
bitwuzla-regress-clean/solver__fp__issue130.smt2
```

For the one-row benchmark, place a symlink to `solver__fp__issue130.smt2` in an
otherwise empty temporary directory, then run:

```sh
cargo run -q -p axeyum-bench --features z3 -- "$CASE_DIR" \
  --backend solver --timeout-ms 10000 --logic QF_BVFP --compare-z3 \
  --jobs 1 --out "$RESULT_JSON"
```

The benchmark's Z3 comparison is not the independent oracle: the parser has
already folded the ground assertion before both backends see it. Use the raw-SMT
Z3 differential test above for semantic independence.
