# ADR-0101: Checked finite equality-partition quantifiers

Status: accepted
Date: 2026-07-11

## Context

After ADR-0100 the 12-row quantified-LIA slice decides and certifies 8/12. The
smallest unsupported row, `cbqi-sdlx-fixpoint-3-dd`, is a closed Boolean formula
with nested positive and negated universals. Every bound integer is observed
only by a predicate of the form `x = 0`; no arithmetic operation consumes the
binder directly. Therefore all integers fall into exactly two behaviorally
indistinguishable cells: `{0}` and `Int \ {0}`.

The existing finite-domain expander correctly handles Bool/BV domains, but Int
is infinite and the original evaluator intentionally refuses to enumerate it.
cvc5's CEGQI machinery searches boundary terms and Z3's quantifier evaluator
evaluates clauses under candidate bindings. For this restricted fragment no
heuristic search is required: the syntactic equality predicates induce a finite
quotient that can be checked directly.

The other three unsupported rows are not in this class. They quantify 40--50
mixed Bool/Int variables used throughout affine ITE networks; two are SAT and
need general model construction. This ADR must not be presented as solving that
engine problem.

## Decision

Add an UNSAT-only decision and evidence route for a closed quantified Boolean
assertion satisfying all of the following:

1. quantifiers bind only `Bool` or `Int` values;
2. every occurrence of an `Int` binder is a direct operand of `Eq`, and the
   other operand is an explicit `IntConst`;
3. there are no free symbols, UF applications, arrays, datatypes, sequences, or
   floating-point terms;
4. the product of representative counts across every active quantifier path is
   bounded by a deterministic case cap.

For an Int binder mentioned against constants `C = {c1, ..., cn}`, enumerate
one representative for every singleton `{ci}` and one deterministic value not
in `C`. Bool binders enumerate `false,true`. This is complete because replacing
one value by another in the same cell preserves every atom in which the binder
can occur, hence preserves the whole Boolean formula under arbitrary nesting,
polarity, and ITE structure.

The untrusted solver route and trusted checker are separate implementations.
The checker re-scans the untouched original assertion, reconstructs every
partition, recursively evaluates quantifiers over their representatives, and
accepts only a false top-level assertion. The certificate carries the original
assertion and deterministic number of leaf cases; tampering either must fail.
No QF solver verdict, expanded term, or search trace is trusted.

## Evidence

- `cbqi-sdlx-fixpoint-3-dd` has four nested/side-by-side universals but only
  zero tests on their integer binders; the exact quotient has two cells per
  active binder.
- Focused tests must cover nested `forall` under `or`/`and`/`not`, multiple
  constants, unused binders, Bool binders, certificate tampering, free-symbol
  rejection, direct arithmetic use rejection, and satisfiable controls.
- A static-Z3 differential must compare generated formulas with varied
  constants, quantifier polarity, and connective structure.
- Acceptance requires a fresh corpus result of at least 9/12 with
  `DISAGREE=0`, certified/rechecked evidence for every new decision, no audit
  error/timeout/trust hole, and unchanged model replay safety.
- Six focused all-feature tests pass, including the target, signed/multiple
  constants, Bool binders, negated existentials, case-count tampering,
  free/direct-arithmetic/binder-equality declines, valid controls, and a
  static-Z3 sweep of 64 UNSAT plus 64 valid alternating formulas.
- Fresh release measurement is 9/12 (sat 2, unsat 7, unsupported 3),
  `DISAGREE=0`, with no error or model-replay failure. The nine-decision audit
  checks and certifies 9/9; `cbqi-sdlx-fixpoint-3-dd` carries
  `equality-partition-unsat`, an empty trust ledger, and no audit error or
  timeout. Lean UNSAT remains 0/7.

## Alternatives

- **Treat `{0,1}` as test points without checking occurrences.** Rejected: an
  arithmetic occurrence such as `x + 1` distinguishes infinitely many values.
- **Extend the general finite-domain expander to Int.** Rejected: Int itself is
  not finite. This is a formula-specific quotient and needs an explicit proof
  obligation and evidence artifact.
- **Encode only the target syntax.** Rejected: finite equality partitions are a
  genuine semantic class and support arbitrary checked Boolean nesting.
- **Attack the three large rows first.** Rejected for this increment: they need
  scalable CEGQI and SAT-side quantified models, while this exact quotient is a
  bounded measured gain. They remain the immediate broader target.

## Consequences

- One nested-QSAT-shaped infinite-domain row can become a small, reduction-free
  checked refutation.
- The trusted surface grows by a finite syntactic admissibility scan and
  representative evaluator, not by a general arithmetic solver.
- Inequalities, arithmetic uses, binder-to-binder equality, free parameters,
  UF applications, and unbounded case products decline unchanged.
