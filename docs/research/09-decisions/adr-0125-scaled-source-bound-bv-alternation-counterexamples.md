# ADR-0125: Scaled source-bound BV alternation counterexamples

Status: accepted
Date: 2026-07-11

## Context

ADR-0124 checks one concrete outer assignment for a closed Bool/BV
`forall+ exists+` implication by source-instantiating the matrix and rechecking
a residual QF_BV DRAT/LRAT proof. Its first conservative admission limits were
128 binders and 4,096 matrix DAG nodes.

The final cvc5 quantified-BV unknown, `bug802`, has the same exact certificate
shape but 318 universal and 212 existential binders. Its 3,317-node matrix uses
only Bool and bit-vector widths 2, 3, 5, and 8. The first model of its outer-only
antecedent is already a valid counterexample: after source substitution, the
residual existential matrix is QF_BV-UNSAT. The old binder cap therefore rejects
a cheap checked proof solely because the hardware state tuple is wide.

## Decision

**Scale ADR-0124 admission to at most 1,024 total binders while retaining the
4,096-node matrix cap and without changing its semantics, search ordering, or
checker.**

The checker still requires a unique closed Bool/BV `forall+ exists+` prefix, an
implication matrix, and an outer-only antecedent. It still validates every
binding in prefix order, substitutes typed constants into the exact source,
freshens every existential deterministically, regenerates the exact QF_BV CNF,
and checks the carried DRAT/LRAT. Search still tries the antecedent model first,
then deterministic one-binder nondefault perturbations under one shared
deadline. The larger limits authorize more bounded work, not a broader logic or
weaker proof.

## Evidence

`bug802` moves from unknown to source-bound certified UNSAT in five optimized
samples of 20.419, 19.804, 18.417, 24.872, and 19.693 ms (median 19.804 ms).
The public cvc5 quantified-BV slice is now 32 SAT / 11 UNSAT / 0 unknown / 11
unsupported, with 43 expected-status agreements, no disagreement, error, or
replay failure, and five-run PAR-2 samples 5.148479, 5.148264, 5.149056,
5.148897, and 5.148639 seconds (median 5.148639 seconds).

The dominance audit independently certifies and checks all 43 decisions. At
initial acceptance the target was `bv-alternation-counterexample-unsat`, had an
empty trust ledger, and correctly declined Lean reconstruction; total Lean
coverage was 8/11 UNSAT and
dominance is 40/43. The direct-Z3 quantified-BV suite covers 1,336 cases and
controls with zero disagreement. Six focused certificate tests include the
318-outer-binder public target and an explicit 1,025-total-binder rejection;
the 16 new direct-Z3 scaling controls use 160 outer binders, certify all eight
UNSAT formulas, and safely handle all eight SAT formulas.

The accepted 2026-07-14 Lean follow-up reconstructs all 318 universal and 212
existential binders from the untouched source, checks the arbitrary-inner-value
refutation under genuine `Exists.rec` scopes, and emits no `sorryAx`. Its exact
direct/router module-equality gate passes in 45.28 seconds at 2,186,192 KiB peak
under the 4 GiB release envelope. The later 54-row quantified-BV audit therefore
counts this route in its 16/18 Lean UNSAT coverage.

## Alternatives

- **Recognize the USB hardware transition system by symbol names.** Rejected:
  the existing source-bound certificate already proves the result generically.
- **Add a dedicated transition invariant certificate.** Deferred until a case
  requires it; here it would duplicate a smaller residual-QF proof.
- **Raise the matrix-node cap too.** Rejected: `bug802` already fits the original
  4,096-node matrix bound, so no measured evidence justifies broadening it.
- **Remove limits.** Rejected: deterministic resource bounds are public API and
  protect satisfiable/near-miss formulas from unbounded perturbation search.
- **General QSAT/QE.** Deferred: the measured case needs one checked outer
  counterexample, not a complete alternation engine.

## Consequences

Large finite-state tuples can use the same checked counterexample contract as
small ones. Worst-case candidate search grows linearly with the admitted outer
prefix and remains deadline-bounded. General alternation, open formulas,
functions, arrays, and arithmetic remain open; the admitted Bool/BV shape now
has bounded Lean reconstruction.
