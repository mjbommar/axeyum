# ADR-0502: Cross-check binary Möbius signs by Swan and second-trace Arf invariants

Status: accepted
Date: 2026-08-19
Index-summary: Expose exact dyadic-discriminant and second-trace Arf coordinates for the squarefree binary Mobius sign without treating full per-polynomial rank as cancellation

## Context

ADR-0501 rules out a proof that replaces each simultaneous-coset Möbius sum
by the best single-translation defect.  ADR-0500 nevertheless leaves every
collision on an explicit affine Artin--Schreier fibre, so a collective
quadratic representation of the sign is a plausible next coordinate system.

Two classical characteristic-two identities apply on the squarefree locus.
For the monic integral `0/1` lift `F` of a degree-`k` binary polynomial,
Stickelberger--Swan gives

```text
mu(f)=(-1)^k (-1)^((Disc(F)-1)/4),  Disc(F)=1 or 5 mod 8.
```

For the étale algebra `E=GF(2)[x]/(f)`, the Arf invariant of the adjusted
second trace form satisfies

```text
(Disc(F)-1)/4 = Arf(T_2)+epsilon_k mod 2,
epsilon_k=1 exactly for k mod 8 in {3,4,5,6}.
```

## Decision

Expose `binary_second_trace_arf_report` as a bounded CAS operation.  It:

- computes the polynomial Möbius value by binary factorization;
- computes the integral-lift Sylvester determinant modulo eight using unit
  elimination on the squarefree locus;
- constructs multiplication in `GF(2)[x]/(f)` and the second trace quadratic
  form;
- restricts to trace zero in odd degree;
- computes the polar rank and Arf invariant by exact binary linear algebra;
  and
- rejects any disagreement among the three sign routes.

Keep squareful inputs explicit: they have Möbius weight zero and receive no
Swan or Arf phase.  Do not infer endpoint cancellation from the full rank of
the per-polynomial trace form.  That nondegeneracy is the identity that makes
the normalized Gauss sum equal the sign; a useful bound still needs rank or
orthogonality after `f` and the auxiliary quadratic variable are placed in one
joint Artin--Schreier fibre system.

## Evidence

Pinned irreducible and reducible quadratic/cubic examples distinguish the
degree correction, discriminant bit, and Arf bit.  A squareful quadratic pins
the zero-weight boundary.  Exhaustive tests compare all three routes for every
monic constant-one binary polynomial through degree ten and check full polar
rank exactly on every squarefree input.

## Consequences

- The CAS no longer needs factorization alone to represent the
  characteristic-two Möbius sign.
- A future joint Gauss-sum argument can use an exact quotient-algebra and Arf
  implementation with the parity conventions already checked.
- Per-polynomial Arf rank is diagnostic structure, not theorem credit and not
  an endpoint exponent input.
