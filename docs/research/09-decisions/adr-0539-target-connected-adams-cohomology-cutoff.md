# ADR-0539: Target a degree-4ell cohomology cutoff for the connected Adams convolution

Status: accepted
Date: 2026-08-20
Index-summary: Identify the product-one Adams trace, expose all three Wick projectors, and reduce a geometric proof to a degree-4ell cohomology cutoff with an ell^4 Betti budget

## Context

The Hayes fourth cumulant is not the ordinary pointwise fourth moment governed
by single-family `SL` monodromy.  It is the product-constrained contraction

```text
Q_4=sum_(chi_1 chi_2 chi_3 chi_4=1) product_i S_n(chi_i).
```

For the Frobenius space `V_chi` of the Hayes `L`-polynomial, the power sum is
the trace of the Adams operation:

```text
S_n(chi)=Tr(Frob_chi^n|V_chi)=Tr(Frob_chi|psi^n V_chi).
```

Thus `Q_4` is an identity-fibre convolution trace.  A useful geometric target
must state how much cohomology remains after the three Wick contractions,
rather than citing monodromy generically.

## Decision

Extend `HayesCharacterFourthMomentComparison` to retain

```text
P_2=sum_chi S_chi S_(chi^-1)=2^ell M_2,
Q_4-3P_2^2=2^(2ell)K_4.
```

The CAS stores `P_2`, one Wick pairing, the sum of all three pairings, and the
connected difference, and checks the last identity against the independent
spatial cumulant.

Add `hayes_adams_identity_fibre_requirement`.  The product-one four-character
fibre has dimension `3ell`, so unrestricted compactly-supported cohomology can
reach degree `6ell`; each pairing diagonal has dimension `2ell`.  The
connected virtual object still has nonzero generic rank, so literal support on
the pairing diagonals is not asserted.  Admit the following as the exact
sufficient cohomological target, without claiming it:

```text
normalized connected virtual complex is mixed of weights <=0,
H_c^i of the connected complex vanishes for i>4ell,
total normalized Betti number <= ell^4.
```

After restoring the Adams weight `2^(2n)`, this gives

```text
abs(2^(2ell)K_4) <= ell^4 2^(2ell+2n).
```

Together with the proved second-moment envelope, this is exactly strong enough
for the accepted `64 ell^4 2^(3ell)` endpoint ledger.

## Evidence

At `ell=200`, the report requires the top cohomology degree to drop from 1200
to 800.  Its normalized Betti budget is
`200^4=1600000000`, and both endpoint weight restorations are checked with
exact bignums.  Off-endpoint and zero-level inputs decline.

The arithmetic Fourier source confirms that convolution becomes tensor
product, but its equidistribution and moment theorems fix the group and sheaf
and average characters over extension fields.  Katz's theorem similarly
fixes conductor while the field grows; its effective error contains an
uncontrolled sum of compactly-supported Betti numbers.  Neither source proves
four-pullback independence on the product-one fibre, the degree-`4ell`
cohomology cutoff after Wick subtraction, or the stated growing-conductor
Betti bound.

## Consequences

- A proposed geometric proof can now be checked against exact dimension,
  weight, and Betti budgets before it receives endpoint credit.
- ADR-0540 subsequently refutes `ell^4` as a universal all-`ell` Betti budget
  at `(ell,n,r)=(2,5,5)`.  A surviving use must prove an explicitly scoped
  large-`ell` budget or replace this coefficient and replay the endpoint.
- ADR-0541 then derives the entire level-two trace polynomial and proves that
  its normalized `q`-degree is 5, one above the proposed degree 4.  Thus the
  cutoff itself is also false universally, although a separately proved
  large-`ell` statement remains logically possible.
- Ordinary large-monodromy fourth moments remain the wrong contraction.
- Killing only the top cohomology group or gaining one Weil half-weight is
  insufficient; all compactly-supported cohomology above degree `4ell` must
  cancel in the connected virtual object.
- The remaining proof problem is a uniform four-pullback independence and
  complexity theorem over fixed `GF(2)`, or an algebraic argument implying the
  same trace bound.
