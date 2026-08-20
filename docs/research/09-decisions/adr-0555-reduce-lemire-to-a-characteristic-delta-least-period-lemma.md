# ADR-0555: Reduce Lemire to a characteristic-delta least-period lemma

Status: accepted
Date: 2026-08-20
Index-summary: Encode the complete Lemire coefficient class as one binary characteristic-delta convolution and isolate its unproved no-proper-period lemma

## Context

The analytic route has proved its inverse-energy input and canceled every
coarse frequency, but it still leaves a connected Frobenius trace for which no
positive uniform saving is known.  The characteristic-delta formalism of
Tuxanidy and Wang gives a different sufficient criterion: the inverse discrete
Fourier transform of a finite-field support indicator forces an element of
exact degree `n` when its least period does not divide the exponent of the
union of the proper subfields.

For Lemire, put

```text
ell=ceil(n/2)-1,  N=2^n-1,
delta_j(a)=1 iff the n-bit representative of a has Hamming weight j.
```

The characteristic elementary symmetric function satisfies

```text
sigma_j(zeta^a)=DFT(delta_j)(a).
```

Because the values of `sigma_j` lie in `GF(2)`, the product

```text
F(alpha)=product_(j=1)^ell (1+sigma_j(alpha))
```

is exactly the indicator that the first `ell` nonleading coefficients of the
degree-`n` characteristic polynomial of `alpha` vanish.  Its inverse DFT is

```text
Gamma_(n,ell)=*_(j=1)^ell (delta_0+delta_j)
```

in `GF(2)[Z/N]`.

## Decision

Add `tuxanidy_lemire_period_report` as a bounded native CAS operation.  It
constructs the exact parity convolution, computes its actual least translation
period, and compares that period with

```text
M_n=lcm_(d|n,d<n)(2^d-1)=N/Phi_n(2).
```

Tuxanidy--Wang's theorem certifies the implication

```text
least_period(Gamma_(n,ell)) does not divide M_n
  => a degree-n element satisfies every Lemire coefficient condition
  => the element's minimal polynomial is a Lemire irreducible.
```

The stronger observed statement

```text
least_period(Gamma_(n,ell))=N
```

is retained as a conjectured fact.  It is not promoted from bounded rows.

The report is resource-admitted by degree, cyclic order, and exact convolution
cell count.  It exposes separately the checked algebraic implication and the
false universal-certification flag.

## Evidence

- Exact group-algebra multiplication gives maximum least period for every
  Lemire row from degree 3 through degree 12.
- A separate extension-field oracle through degree 8 never constructs
  `Gamma`: it enumerates powers of a listed primitive element, multiplies the
  Frobenius-root characteristic polynomial directly, and derives the inverse
  DFT period from the gcd of the supported exponents.  It agrees with the
  convolution report.
- Factor supports are checked independently against `1+binomial(n,j)`.
- Invalid degrees, cyclic-domain excess, and convolution-work excess fail
  closed.
- The single-coefficient maximum-period theorem does not justify the product.
  A direct stopping control at degree 8 shows that the product over
  `j=1,2,3,4`, including the middle coefficient, has least period `15` rather
  than `255`.  The Lemire product stops at `j=3` and has period `255`, but this
  comparison rules out an unrestricted convolution-preserves-period lemma.

## Alternatives

- **Promote the finite period table:** rejected; no bounded table proves the
  quantified statement.
- **Multiply the Hansen--Mullen single-coefficient theorem:** rejected;
  convolution of distinct maximum-period idempotents need not retain maximum
  period, as the degree-8 middle-coefficient control shows.
- **Treat the period criterion as an equivalence:** rejected.  The cited
  direction is sufficient and can be stronger than existence of an exact
  degree element.
- **Abandon the connected-trace route now:** rejected.  The period lemma is a
  new proof target, not yet a theorem, so the proved analytic infrastructure
  remains a valid fallback.

## Consequences

- The shortest current candidate paper reduces to one explicit combinatorial
  theorem about a binary cyclic convolution.
- The immediate mathematical task is to rule out periods dividing `M_n`, not
  necessarily to prove the stronger maximum-period pattern.
- A successful proof bypasses the unresolved connected trace and gives the
  required irreducible directly.  Until then, it receives no Lemire theorem
  credit.

ADR-0558 sharpens this boundary.  The single period `M_n` gives an exact
criterion only for prime-power `n`; at mixed-divisor degrees its root subgroup
strictly overcovers the union of proper subfields.  The exact all-degree target
is instead the nonvanishing of the product of maximal-subfield translation
differences recorded there.  The present least-period condition remains a
valid sufficient condition, but is no longer the selected minimal target.

## References

- Tuxanidy and Wang, [*A new proof of the Hansen--Mullen irreducibility
  conjecture*](https://arxiv.org/abs/1604.04023), especially the DFT-period
  criterion and the characteristic delta functions.
