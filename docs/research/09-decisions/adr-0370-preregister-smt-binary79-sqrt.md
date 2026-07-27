# ADR-0370: Preregister SMT `(15,64)` symbolic square root

Status: accepted

Date: 2026-07-27

## Context

After ADR-0368/0369 validate `(15,64)` add/sub/mul/div, the deterministic family
sample's `sqr_longdouble-flow/query.1.smt2` and
`sqr_longdouble-noflow/query.1.smt2` stop at `fp.sqrt: unvalidated format`.
Both are declared/Z3 SAT.

The generic sqrt circuit already supports a 234-bit F128 intermediate through
the pure-Rust wide-BV path. `(15,64)` requires only 138 bits. Representation is
not the blocker; independent correct-rounding validation is. `rustc_apfloat`
does not expose square root, so ADR-0028 validates F128 RNE with an exact dyadic
rounding-interval checker which is itself tested against native F64 sqrt.

## Decision

**Generalize the exact sqrt oracle to all five SMT rounding modes, validate the
existing `(15,64)` circuit with it, and then admit only that format through a
sqrt-specific gate. Keep FMA unsupported.**

For a positive finite input `x` and candidate `r`, the oracle compares exact
dyadic squares with arbitrary-width integers:

- nearest-even: `x` lies between the squared midpoints to predecessor/successor,
  with exact ties choosing the even significand;
- nearest-away: the same interval, with a lower tie choosing `r` and an upper
  tie choosing the successor (away from zero);
- toward-positive: `r² >= x` and `pred(r)² < x`;
- toward-negative/toward-zero: `r² <= x` and `succ(r)² > x`; and
- NaN, negative, infinity, and signed-zero cases follow SMT/IEEE special rules
  independent of rounding mode.

The implementation must keep the already native-validated F64 RNE oracle test,
rerun the F128 RNE sweep through the generalized function, cover all five modes
on `(15,64)` structured plus deterministic random inputs, and directly require
symbolic `(15,64)` FMA to remain unsupported.

## Acceptance evidence

- The exact oracle accepts all 2,620 registered `(15,64)` input/mode cases and
  rejects both adjacent encodings for every applicable positive finite result.
  The existing native-F64 and F128 RNE sweeps also pass through the generalized
  checker.
- Both selected sqrt rows are replay-checked SAT with declared-status and Z3
  agreement. The combined eight-row binary79 artifact is 4 SAT / 4 UNSAT, 8/8
  against Z3, with zero unknown, unsupported, error, or replay failure.
- The six ADR-0368/0369 rows retain their decisions. The fresh serial ESBMC
  process gate is 34/34 UNSAT: 33 rows passed in one sweep and the sole outer
  timeout, `Float4_1-main.smt2`, passed in 4.01 s immediately in isolation.
  The corpus contains no `(15,64)` declaration.
- Full `axeyum-fp` tests pass (69 unit, 11 full-faithfulness, 14
  simple-faithfulness, two width-guard, and doc-tests), as do warning-denied
  Clippy, fmt, documentation links, and diff checks.
- Symbolic `(15,64)` FMA remains directly tested unsupported. The frozen
  108-family diagnostic has zero wrong verdicts (88 correct, 18 unknown, two
  contention-sensitive outer timeouts); only the two exact sqrt gains are
  credited.

## Alternatives

### Use host `long double` sqrt

Rejected. Host ABI/precision and x87's explicit-integer-bit encoding are not the
SMT 79-bit layout, and rounding-mode control would add platform/FFI dependence.

### Validate only round-nearest-ties-to-even

Rejected. The public operator accepts all five modes; format admission must not
leave four symbolic branches unvalidated.

### Admit FMA in the same change

Rejected. FMA is ternary and needs its own independent fused-rounding sweep and
front-door demand. Sqrt evidence grants no FMA assurance.

## Consequences

If accepted, `(15,64)` sqrt joins the four binary arithmetic operators through
the existing C-free wide-BV path. The exact all-mode sqrt checker becomes a
reusable test oracle. FMA remains the only rounded arithmetic member of this
format outside the validated set.
