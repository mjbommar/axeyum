# ADR-0141: Checked source-term bit-vector Skolem witnesses

Status: accepted
Date: 2026-07-14

## Context

The bounded public quantified-BV UNSAT slice now reconstructs 18/18 rows in
Lean, while the next depth lane is broader nested/alternating QSAT and
quantified-UF models. GQ1/GQ10 must still wait for the real Glaurung capture,
so synthetic timing cannot select a cold-path optimization.

[ADR-0121](adr-0121-checked-reflexive-bitvector-skolem-witnesses.md) proves the
exact theorem `forall x. exists y. y R x` for equality or non-strict BV order
with the identity witness `y := x`. It deliberately declines equally direct
definitions such as `y := bvadd x c`, `y := bvnot x`, or `y := f(x)`, even
though substituting the exact source term makes the untouched body reflexive.
Interpreting the public rational affine recipe modulo `2^w` would be ambiguous,
and a general function interpretation is unnecessary for these theorems.

## Decision

**Extend the ADR-0121 certificate only with an exact, source-reachable BV term
over the leading universal binders, and continue to grant SAT only after
independent substitution reduces the untouched source to reflexivity.**

For a bit-vector existential, `AffineSkolemWitness` now has this exact-source
encoding:

- `terms` contains exactly one term with coefficient one;
- `constant` is exactly zero;
- the term is reachable from the exact original assertion, belongs to the
  caller's arena, is quantifier-free, and has the existential's exact BV sort;
- every ordinary symbol in the term is one of the leading universal binders;
  constants and total uninterpreted-function applications over those binders
  are permitted; and
- the checker substitutes that same interned term for the existential in a
  private arena clone and accepts only when its small Boolean checker proves
  the resulting equality, `bvule`, or `bvsle` by syntactic reflexivity.

The rational fields receive no modular interpretation. The BV recipe denotes
the one carried source term, not `sum(coeff_i * atom_i) + constant`; arithmetic
`Int`/`Real` recipes retain their existing affine meaning.

Search is untrusted and deterministic. It scans the quantifier-free body for
an equality or non-strict signed/unsigned BV-order atom in which the existential
is one direct operand and proposes the opposite source operand. Identity
proposals remain first. A candidate containing the existential, a free symbol,
a nested quantifier, a detached arena term, the wrong sort, or a term that does
not make the complete body provably true is rejected by the independent
checker. Strict comparisons, multiple existentials, nested quantifier bodies,
non-reflexive Boolean obligations, and synthesized terms absent from the source
still decline.

An application witness such as `y := f(x)` does not construct or trust a
function table. The source theorem is true for every total interpretation of
`f`; the checker proves only the instantiated reflexive proposition. General
function-valued models and piecewise Skolems remain separate work.

## Evidence

- The focused witness suite passes 17/17, including 32-bit modular addition,
  a 129-bit bitwise witness, and a BV-valued UF application.
- The certificate suite passes 14/14, including exact source-term identity,
  caller-arena preservation, detached-term rejection, free-symbol rejection,
  coefficient/constant tampering, and canonical model/evidence replay.
- A 64-case direct-Z3 BV matrix across widths 1, 2, 3, 4, 8, 16, 32, and 64
  certifies all 48 identity/composite-source SAT cases; the strict controls
  produce eight agreed UNSAT, two safe Axeyum unknowns, and six Z3 timeouts,
  with no disagreement.
- A separate 12-case direct-Z3 quantified-UF matrix covers equality and
  non-strict-order witnesses at widths 1, 2, 8, 32, 129, and 257. Every Axeyum
  model replays and every Z3 result is SAT.

## Alternatives

- **Interpret arbitrary rational affine recipes modulo the BV width.** Rejected:
  it changes the certificate's meaning and needs explicit wide modular
  coefficient semantics that this source-reflexive class does not require.
- **Accept any synthesized term over the universals.** Rejected: source
  reachability keeps the artifact arena-stable and auditable, while direct
  substitution already covers the measured theorem class.
- **Trust the search-side QF result.** Rejected: search only proposes a term;
  the small checker re-matches and proves the untouched quantified assertion.
- **Return a UF function model.** Rejected: `forall x. exists y. y = f(x)` is
  proved for every total `f`; a table would add an irrelevant and unchecked
  commitment.
- **Implement general BV QSAT/QE first.** Deferred: arbitrary alternation,
  multiple dependent existentials, and piecewise witnesses need distinct
  model/evidence contracts.

## Consequences

- Exact modular, bitwise, and UF-derived source terms become replayable
  nonvacuous BV Skolem witnesses without native-solver trust or enumeration.
- The public certificate type remains structurally compatible; its BV branch
  gains one explicit exact-source meaning while arithmetic behavior is
  unchanged.
- This advances both nested `forall/exists` QSAT and quantified-UF coverage,
  but does not close general alternation, function-valued models, free-symbol
  parameter witnesses, SAT-side Lean theorem/model export, or GQ1/GQ10.
