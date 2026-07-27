# Finite-domain preprocessing repair — 2026-07-27

## Result

The current-main `QF_BVFP` row `Float-no-simp3-main.smt2` fell from the
committed baseline's millisecond decision to a construction run that exceeded
five minutes in the eight-file harness and 48 seconds in the direct CLI. Parsing
took milliseconds and each assertion decided alone, ruling out FP search.

Canonical constant folding evaluated `FpFromBits(constant)` to `Value::Bv` and
reified it as a plain `BitVec(32)`. Rebuilding the enclosing equality failed with
`SortsDiffer(Float { exp: 8, sig: 24 }, BitVec(32))`; default preprocessing then
degraded to the unreduced query and paid the large eager-circuit cost.

The repair is denotation-preserving:

- constant folding restores `Sort::Float` and `Sort::RoundingMode` wrappers
  around their bit-pattern values;
- value propagation recognizes a variable equal to a ground-evaluable scalar
  term and reifies the value with its original sort. Undefined FP conversion
  branches still decline when evaluation reaches an unbound interpretation.

Definitions retain the existing model-reconstruction trail, and SAT still
replays against the original query. This fixes an existing rewrite contract and
needs no new ADR or rewrite rule.

## Evidence

- `cargo test -p axeyum-rewrite`: 113 unit + 2 integration tests pass.
- The focused SMT-LIB regression decides declared `unsat` under a two-second
  internal timeout in 0.03 seconds of test time.
- Warning-denied Clippy passes for `axeyum-rewrite` and the focused solver test.
- The complete eight-file QF_BVFP slice finishes in 5 seconds of outer wall time:
  4 SAT, 3 UNSAT, 1 expected unsupported custom-format row, 7 agreements, zero
  disagreements, and zero model-replay failures.
- `Float-no-simp3-main.smt2` records 18.025 ms cold total in that debug artifact,
  versus bounded current-main runs exceeding 48 seconds/five minutes.

Combined with the separate ground custom-format division increment, clean source
revision `a3c4b04f9729defe1ebf496ee3d92d6decab24bb` measures 8/8 decided (5 SAT,
3 UNSAT), DISAGREE=0, and zero model-replay failures. In that integrated run this
row records 19.100 ms cold total.
