# ADR-0099: Checked nested-XOR quantifier refutation

Status: accepted
Date: 2026-07-11

## Context

The sole incomplete row in the 12-file quantified-LIA slice is cvc5's
`issue4433-nqe.smt2`:

```text
forall a b.
  xor (xor (a = 0) (b = 0))
      (forall c.
        ite(a = 0, 0, 1) = ite(c = 0, 0, 1))
```

cvc5 handles the broader class by recursively skolemizing outer variables,
running quantifier elimination on each nested quantifier, and reconstructing an
equivalent top-level formula
(`references/cvc5/src/theory/quantifiers/cegqi/nested_qe.cpp`). Z3 has a general
polarity-aware nested-quantifier pulling pass in
`references/z3/src/ast/normal_forms/pull_quant.cpp`.

Axeyum does not yet have a general proof-producing nested-QE transform. The
measured formula has a much smaller exhaustive refutation: instantiate the
outer binders at the two selector pivots. The first XOR becomes false, so the
outer body entails the nested universal. Instantiate its binder away from its
pivot; the two `ite` expressions then select distinct constant branches.

## Decision

Admit one exact all-`Int` theorem schema through hierarchical universal
instantiation and a separate original-IR checker:

```text
forall a b.
  xor (xor (a = pa) (b = pb))
      (forall c.
        ite(a = pa, t, e) = ite(c = pc, t, e))
```

where the three pivots and both branches are integer constants and `t != e`.
The checker accepts swapping either XOR's children, equality operands, and the
two sides of the nested equality, but no extra Boolean structure, binders, or
nonconstant branch terms.

The search route independently recognizes the schema, chooses
`a := pa`, `b := pb`, and `c := pc + 1` (or `pc - 1` on overflow), builds the
resulting ground nested body, and returns `Unsat` only when the ordinary QF
solver refutes that consequence. The consequence is genuine:

1. `xor(true, true)` is false at the outer pivots;
2. `xor(false, q)` is `q`, so the original assertion entails the nested
   universal at those pivots;
3. the nested universal entails its instance at any integer different from
   `pc`;
4. that instance is `t = e`, false because `t != e`.

The evidence route does not call the search matcher, substitution code, or QF
solver. It independently re-peels exactly two outer `Int` universals and one
direct nested `Int` universal, re-matches the complete XOR/equality/`ite`
structure, checks distinct binder IDs and distinct branch constants, and
regenerates a typed certificate from the untouched original arena.

## Evidence

- The committed cvc5 regression is declared `unsat` and is the measured final
  incomplete row in this division.
- The proof uses only Boolean XOR identities, universal instantiation, integer
  successor/predecessor totality, and disequality of two explicit constants.
- The exact positive polarity of the nested universal is load-bearing. Moving
  it under `not`, implication antecedent, or a non-collapsing XOR context does
  not preserve the consequence.
- Target, tamper, child/equality-order, signed-constant, equal-branch,
  altered-operator, extra-structure, negative-polarity, and `or true` context
  tests pass. A deterministic static-Z3 sweep checks 64 structurally permuted
  UNSAT schemas and 64 satisfiable wrappers with no disagreement.
- Fresh release measurement of the 12-row quantified-LIA slice is 8/12
  (sat 2, unsat 6, unknown 0, unsupported 4), `DISAGREE=0`, with no errors or
  model-replay failures. The eight-decision audit checks 8/8 and certifies 6/8;
  the target carries `int-nested-xor-unsat` evidence with no trust steps,
  mismatches, audit errors, or timeouts. Lean UNSAT remains 0/6.

## Alternatives

- **Implement general nested QE first.** This remains the strategic destination,
  but requires polarity/NNF bookkeeping, elimination procedures, and proof
  reconstruction well beyond the measured theorem.
- **Blindly pull the nested universal through XOR.** Rejected: XOR is not
  monotone. Pulling is justified here only after the other XOR operand is made
  exactly false by the checked outer instantiation.
- **Trust a simplified ground `0 = 1`.** Rejected: the evidence checker must
  prove that the ground contradiction is entailed by the original quantified
  assertion, independently of search and simplification.
- **Return bare `Unsat`.** Rejected: this would regress the checked-evidence
  discipline established by ADR-0095 and ADR-0097.

## Consequences

- `issue4433-nqe` becomes a checked quantified-LIA UNSAT row without
  pretending Axeyum has general nested QE.
- The 12-row division can reach 8/12 decided, but the four unsupported
  Boolean-heavy rows and two older bare UNSAT artifacts still matter for Pareto
  dominance.
- General polarity-aware nested quantifier pulling, recursive QE, QSAT,
  multiple nested quantifiers, symbolic branch terms, and Lean reconstruction
  remain open.
- The division now has no incomplete rows. Four Boolean-heavy rows remain
  unsupported; `ARI176e1` and `issue5279-nqe` remain the two bare UNSAT
  decisions blocking an all-certified decided set.
