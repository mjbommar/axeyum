# ADR-0499: Average Berlekamp shift energy over annihilators

Status: accepted
Date: 2026-08-19
Index-summary: Replace per-frequency Berlekamp diagnostics by an exact signed simultaneous-coset energy and feed candidate bounds into the endpoint ledger

## Context

ADR-0498 exposed the combined squarefree phase

```text
w_a(f)=mu(f)(-1)^<a,f^(-1)-1>
```

and its coefficient-shift energy `E_H(a;k)` frequency by frequency.  The
Lemire endpoint, however, sums all frequencies in an annihilator.  Bounding
each frequency separately discards cancellation and leaves no direct
classification target.

Let `H=W_s` toggle the first `s` free coefficients of a monic constant-one
degree-`k` polynomial.  Let `A=W_d^perp` be the additive-frequency
annihilator.  An input coset `C` fixes coefficients above `s`; an inverse coset
`D` fixes coefficients of `f^(-1)` above `d`.  Put

```text
b_(C,D)=sum_(f in C, f^(-1) in D) mu(f).
```

These signed simultaneous-coset sums retain the Berlekamp phase rather than
replacing it by support size.

## Decision

Use additive orthogonality before taking absolute values.  The exact identity
is

```text
sum_(a in A) E_H(a;k) = |A| sum_(C,D) b_(C,D)^2.       (AE)
```

Expose the right side as `signed_coset_energy` in the bounded native operation
`binary_berlekamp_annihilator_energy_report`.  Also expose the unsigned
collision count obtained by replacing each `b_(C,D)^2` with the square of its
squarefree population.  The difference measures genuine Möbius/Berlekamp
cancellation.

Combining `(AE)` with Cauchy gives the normalized inverse-interval bound

```text
(sum_(f: f^(-1) in V_d) mu(f))^2
  <= 2^(k-1-s) sum_(C,D) b_(C,D)^2.                    (CB)
```

Add `binary_berlekamp_aggregate_exponent_ledger` so every candidate upper
bound for the signed energy is immediately propagated through
`H_k=B_k-B_(k-1)`, the convolution weight `d`, and the exact `2^ell` target.

The report also decomposes the energy by the actual coefficient shift:

```text
sum_(C,D)b_(C,D)^2
  = sum_(h in W_s) sum_f mu(f)mu(f+h)
      1_(f^(-1)+(f+h)^(-1) in W_d).                   (SC)
```

The zero-shift term is exact.  The number `Q_k` of monic, constant-one,
squarefree binary polynomials of degree `k` satisfies

```text
Q_k=2^(k-1)-Q_(k-1)=(2^k-(-1)^k)/3.                  (QD)
```

Indeed, all monic squarefree degree-`k` polynomials number `2^(k-1)`, and
the ones divisible by `x` are exactly `xg` for constant-one squarefree `g`
of degree `k-1`.

## Evidence

At `(ell,k,d,s)=(4,9,3,3)`, the simultaneous-coset report has 62 occupied
buckets, signed energy 179, unsigned collisions 599, and exact inverse-fibre
sum zero.  Summing the independently computed per-frequency energies over the
two annihilator frequencies gives `358=2*179`, checking `(AE)`; the direct
phase sums check the normalized inverse-fibre identity.

The tempting constant-one random-scale target

```text
sum_(C,D)b_(C,D)^2 <= 2^(k-1)
```

is false: at `(ell,k,d,s)=(6,9,5,5)` the exact energy is `309>256`.  The
diagonal in `(SC)` is exactly `Q_9=171`, so the nonzero shifts contribute
`138`; the failure is genuinely off diagonal.  The relaxed candidate
`E<=2^k` survives both endpoint windows for every `2<=ell<=9` and
`1<=d<ell`.  This is finite evidence only.

A second, local target also survives the same controls:

```text
b_(C,D)^2 <= 2d #(C,D).                               (LSR)
```

Unlike the bare global candidate, `(LSR)` asks for square-root cancellation
in each simultaneous input/inverse fibre.  Summing it and using `(QD)` gives
`E<=2d Q_k<d 2^k`.  It is still only a conjectural character-sum target.

If `E(k)<=2^k` and `E(k-1)<=2^(k-1)` held uniformly with `s=d`, the exact
ledger at `ell=300` would first give a strict weighted-term saving at `d=207`
for degree 601 and `d=208` for degree 602.  It therefore moves a prospective
pointwise tail substantially below the Vaughan transition near 283, but does
not control the complementary low block.

The weaker consequence `E<d 2^k` of `(LSR)` first gives strict odd and even
weighted-term savings at `d=210`.  Thus its polynomial loss costs only three
orders at this scale and it is strong enough for essentially the same tail;
it likewise leaves the complementary block open.

## Alternatives

- Maximize `E_H(a;k)` over frequencies: rejected because the endpoint sums an
  annihilator and orthogonality retains more cancellation.
- Drop the Möbius signs and count only simultaneous unit/inverse collisions:
  retained as an explicit comparison, but rejected as the primary bound
  because it erases the Berlekamp input.
- Record `E<=2^(k-1)` as a conjecture: rejected by the exact level-six
  counterexample.
- Treat `E<=2^k` as proved from the controls: rejected; no uniform
  stationary-fibre argument is yet available.

## Consequences

- The Berlekamp route now has one precise quantified target rather than a
  collection of phase spectra.
- Any proposed energy exponent can be rejected or accepted by the endpoint
  ledger before a long proof attempt.
- Even the useful `E<=2^k` candidate would leave a linear low block.  A final
  proof must either preserve cross-order cancellation there or prove a
  stronger block estimate; this increment does not claim endpoint closure.
