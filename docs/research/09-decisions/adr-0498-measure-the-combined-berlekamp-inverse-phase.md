# ADR-0498: Measure the combined Berlekamp-inverse phase on shift fibres

Status: accepted
Date: 2026-08-19
Index-summary: Add a bounded exact stationary-fibre ledger for the characteristic-two Berlekamp-discriminant plus inverse-additive phase

## Context

The explicit wrapped inverse-energy theorem and exhaustive Vaughan table leave
the signed low/medium Möbius aggregate as the Lemire endpoint blocker.  Taking
absolute values order by order loses the cancellation visible in the exact
annihilator-depth regroup.  More exponent bookkeeping cannot supply that
cancellation.

Carmon's characteristic-two source states the exact squarefree identity

```text
mu(f) = (-1)^deg(f) chi_2(Berl(f)).
```

For `GF(2)`, `chi_2(z)=(-1)^z`.  Thus the conventional inverse-additive sum

```text
B_k(a) = sum_(deg f=k, monic, f(0)=1)
           mu(f) (-1)^<a,f^(-1)-1>
```

is a combined Berlekamp-discriminant and inverse phase on the squarefree
locus.  Squareful inputs have Möbius weight zero; the rational Berlekamp
discriminant is undefined there, so silently extending its sign would change
the sum.

The remaining question is whether coefficient translations expose a
uniformly small stationary set for this combined phase.  This must be measured
on the actual phase and shift fibres before proposing a rank theorem.

## Decision

Add a resource-bounded exact operation
`binary_berlekamp_inverse_phase_report`.  It enumerates monic constant-one
binary polynomials, obtains the Möbius weight from native Berlekamp
factorization, applies the exact inverse-additive character modulo
`x^(ell+1)`, and partitions the coefficient cube by the subspace toggling its
first `s` free coefficients.

For phase weights `w_a(f)` and shift subspace `H`, retain the exact identity

```text
E_H(a;k)
  = sum_coset (sum_(f in coset) w_a(f))^2
  = sum_(h in H) sum_f w_a(f)w_a(f+h).
```

The report counts same-sign and opposite-sign ordered squarefree pairs,
checks that their difference equals `E_H`, and exposes the Cauchy bound

```text
B_k(a)^2 <= 2^(k-1-s) E_H(a;k).
```

The operation is diagnostic only.  It does not assign theorem credit to a
finite rank pattern or silently promote Carmon's large-field theorem to fixed
`q=2`.

## Evidence

At `(ell,k,a,s)=(4,9,12,4)`, the operation finds 171 squarefree inputs,
`B_9(12)=-19`, stationary energy 245, and Cauchy square bound 3920, versus the
trivial square bound 29241.  At the full eight-dimensional shift the Cauchy
bound becomes the exact square `361`.  A test sweeps all sixteen frequencies
at `(ell,k,s)=(4,9,4)` and requires a strict improvement over the trivial
bound.

The direct phase sums also check the reciprocal/ramified identity

```text
B_k(a)-B_(k-1)(a)=H_k(a)
```

against the independently reconstructed additive Möbius spectrum.  Invalid
frequencies, oversized shift spaces, and starved resource limits decline.

## Alternatives

- Use only the Möbius sign: rejected because it hides the inverse character
  whose interaction with the Berlekamp phase is the point of the proposed
  cancellation.
- Evaluate the rational Berlekamp discriminant on squareful inputs: rejected
  because it is undefined and the correct Möbius weight is zero.
- Publish unrestricted spectrum tables: rejected because the useful object is
  the quantified stationary-fibre energy on the residual coefficient block.
- Invoke Carmon's theorem directly: rejected because its limit is fixed
  degree with field size tending to infinity, not fixed `GF(2)` with moving
  degree and prime-power modulus.

## Consequences

- Axeyum can now state and test a precise van-der-Corput input for the combined
  characteristic-two phase.
- The next mathematical obligation is a uniform upper bound for `E_H(a;k)`
  on the annihilator frequencies and degree block left by the explicit
  Vaughan tail, followed immediately by substitution into the aggregate
  exponent budget.
- The finite improvement is encouraging but does not move the proof frontier
  until that stationary-fibre bound is proved with usable dependence on all
  parameters.
