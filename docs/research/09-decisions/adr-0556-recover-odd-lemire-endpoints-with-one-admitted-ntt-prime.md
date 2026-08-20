# ADR-0556: Recover odd Lemire endpoints with one admitted NTT prime

Status: accepted
Date: 2026-08-20
Index-summary: Use the exact odd prime-power identity and candidate count to replace two-prime CRT by one uniqueness-bounded NTT

## Context

The general Hayes population operation reconstructs `N_n(1)` with two NTT
primes and CRT under the deliberately coarse bound `N_n(1)<=2^n`.  That is
appropriate for arbitrary levels and degrees, but it performs twice the
necessary transform work at an odd Lemire endpoint.

For `n=2ell+1`, the already proved prime-power reduction is

```text
N_n(1)=1+n I_n(1).
```

The term one is the ramified polynomial `x^n`.  Every irreducible in the
identity class has constant coefficient one, leaving only the `ell`
coefficients of degrees `1,...,ell` free.  Hence

```text
0 <= I_n(1) <= 2^ell,
0 <= N_n(1) <= 1+n 2^ell.                         (UB)
```

Thus one modular transform determines the integer population exactly whenever
its prime modulus is strictly larger than `(UB)`.

## Decision

Add `odd_endpoint_irreducible_count_single_ntt`.  It uses the NTT prime

```text
p=75161927681=70*2^30+1,
```

for which `3` is a primitive root.  The operation first applies the ordinary
Hayes resource admission and then rejects unless `1+n*2^ell<p`.  Its residue
is consequently the unique possible nonnegative population, with no CRT or
rounding.  It fails closed unless subtraction of the zero contribution is
nonnegative and divisible by `n`, and unless the resulting irreducible count
obeys `I_n(1)<=2^ell`.

Add the explicit high-memory runner
`axeyum-gf2-hayes-odd-endpoint`, capped at `ell=27`.  The cap is an operational
memory boundary, not a theorem boundary.  The reusable operation remains
caller-admitted and its single-prime uniqueness check is authoritative.

## Evidence

- `75161927681` is prime, `p-1` has the required power-of-two transform
  factor, and the existing transform uses primitive root `3`.
- Through `ell=12`, the single-prime report agrees exactly with the independent
  two-prime population and full classwise prime-power inversion, including all
  report fields.
- The runner reproduces the pinned `(ell,n)=(8,17)` row
  `N_17(1)=562`, `Delta_(8,17)=50`, and `I_17(1)=33`.
- Exact-commit fleet runners fill the four consecutive new stopping rows:

  ```text
  ell  n   N_n(1)   Delta       I_n(1)   mod 8
   22 45   8381026   -7582       186245      5
   23 47  16834790   57574       358187      3
   24 49  33556083    1651       684818      2
   25 51  67066531  -42333      1315030      6
  ```

  The level-25 row on `s6` took `961.748` wall-clock seconds and peaked at
  `13,371,736` KiB resident memory.  The staged binary has SHA-256
  `84e2582567c2a929ee6cf3b5c29502dcbedb3d3681f678fdf5924d5ec6090e9e`;
  the complete `/usr/bin/time -v` log has SHA-256
  `55f34e988c98841e47b3dfeab363e1a843043fcf6a4b409cdc6d14dc9620bea7`.
  The nonzero residue preserves but does not prove the proposed 2-adic
  nonvanishing pattern.
- Zero level, ordinary resource excess, loss of the single-prime uniqueness
  bound, nonintegral `1+nI`, and candidate-count excess are typed failures.
- A unit test independently checks primality of the admitted modulus, its
  factorization `p-1=70*2^30`, and the full primitive-root criterion at the
  distinct prime factors `2,5,7`.

## Alternatives

- **Use one of the existing smaller primes:** rejected.  The odd population's
  rigorous upper bound eventually exceeds either modulus, so its residue need
  not be the integer answer.
- **Infer the closest residue from the expected main term:** rejected.  That
  would assume precisely the discrepancy estimate still awaiting proof.
- **Promote a nonzero finite count to the universal theorem:** rejected.  The
  operation accelerates exact stopping tests; it proves no asymptotic or
  quantified existence statement.

## Consequences

- Targeted odd-endpoint computations use half as many exact character
  transforms as the previous scalar route.
- The runner prints `I_n(1) mod 8` explicitly so the current 2-adic candidate
  can be killed promptly without confusing a surviving finite row with a
  congruence theorem.
- The universal Lemire conjecture remains open until either the connected
  signed trace, the characteristic-delta period obstruction, or another
  uniform argument supplies positivity in every degree.
