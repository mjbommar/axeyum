# ADR-0551: Stop the naive even--odd parity induction

Status: accepted
Date: 2026-08-20
Index-summary: Certify the Frobenius-square parity decomposition and prove that it supplies squarefreeness, not an irreducibility induction

## Context

Every binary polynomial has a unique even--odd decomposition

```text
f(x)=E(x)^2+xH(x)^2.
```

For a half-degree-shaped polynomial of odd degree `2m+1`, the odd component
`H` is monic of degree `m` and is itself half-degree shaped.  At even degree
`2m`, the even component `E` has those properties.  This looked like a route
from a shaped irreducible in degree `m` to one in degree `2m` or `2m+1`.
Before searching for a complementary component, the exact implication carried
by the decomposition must be separated from the hoped-for induction.

## Decision

Add `half_degree_parity_split_report` to the bounded native `GF(2)` kernel.
It reconstructs the input from its two components and checks

```text
f'(x)=H(x)^2,
gcd(f,f')=gcd(E,H)^2.
```

Consequently `f` is squarefree exactly when `gcd(E,H)=1`.  Irreducibility of
`f` does not force the leading parity component to be irreducible.  The report
uses the existing exact Rabin route for both irreducibility verdicts and
independently checks every positive certificate, rather than treating the
decomposition as a new oracle.

The simplest proposed odd lift is stopped uniformly.  If `H` is irreducible
of degree greater than one and the complementary component is `E=1`, then
`H(1)=1`, so

```text
f(1)=H(1)^2+1=0.
```

Thus `x+1` divides every such lift.

## Evidence

The focused native tests retain three independent controls:

- `x^5+x^2+1` is Rabin-certified irreducible, but its leading odd component
  is the reducible polynomial `x^2`;
- `H=x^3+x+1`, `E=1` reconstructs
  `xH(x)^2+1=x^7+x^3+x+1`, and the report detects the forced factor `x+1`;
- the irreducible even polynomial `x^6+x^3+1` has reducible leading even
  component `x^3+1`, so the failure is not confined to odd degrees.

Non-shaped inputs and configured degree excess fail closed.  The focused
tests, all-target/all-feature `axeyum-cas` Clippy, and workspace formatting
pass.

## Alternatives

- **Promote the decomposition to an induction hypothesis:** rejected because
  the exact derivative identity yields only coprimality of the components.
- **Fix the complementary component to one:** rejected by the uniform
  `x+1` factor at every nontrivial odd irreducible source.
- **Search all complementary components and infer a theorem:** rejected.
  That is a smaller affine prescribed-coefficient irreducibility problem;
  finite success does not supply a uniform extension lemma.

## Consequences

- Axeyum retains the useful parity identity and squarefreeness criterion as a
  checked algebraic primitive.
- A future constructive route must state and prove an additional theorem that
  produces a complementary component; the parity decomposition itself grants
  no Lemire theorem credit.
- The universal proof frontier remains the connected signed endpoint trace,
  or an independently proved degree-changing construction.
