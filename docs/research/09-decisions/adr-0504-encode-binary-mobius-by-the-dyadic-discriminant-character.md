# ADR-0504: Encode binary Möbius by the dyadic discriminant character

Status: accepted
Date: 2026-08-19
Index-summary: Extend the Swan sign through squareful zero weights and expose the exact four-phase discriminant Fourier expansion modulo eight

## Context

ADR-0502 uses Stickelberger--Swan and the second trace Arf invariant only on
the squarefree locus, leaving squarefreeness as an explicit gate in any joint
fibre sum.  That gate is avoidable at the discriminant level.  The integral
discriminant is odd exactly when the binary reduction is squarefree.  On that
odd locus Swan says it is `1` or `5 mod 8` and determines factor parity.

Let `chi_8(D)=(2/D)` be the real primitive Kronecker character modulo eight,
extended by zero on even integers.  Then every monic binary polynomial and
its integral `0/1` lift satisfy

```text
mu(f)=(-1)^deg(f) chi_8(Disc(F)).
```

## Decision

Make the dyadic character a checked part of the binary discriminant report.
Determine discriminant parity independently by the packed formal-derivative
gcd, compare that squarefreeness decision with Berlekamp factorization, and
reject unless the Kronecker value recovers the full Möbius value including
zero.

Also expose `binary_dyadic_character_fourier_report`, which checks in
`Z[zeta_8]` the exact identity

```text
sum_(a=1,3,5,7) chi_8(a) zeta_8^(aD)
  = 2 chi_8(D) (zeta_8-zeta_8^3).
```

This supplies four additive modulo-eight phases for a future
Artin--Schreier--Witt estimate.  It does not itself bound their sum.

## Evidence

The cyclotomic identity is checked for all eight residue classes in the
integral basis `1,zeta_8,zeta_8^2,zeta_8^3`.  Pinned irreducible, reducible,
and squareful quadratic/cubic examples distinguish the degree sign, the two
odd Swan residues, and the even zero.  Exhaustive checks through degree ten
compare derivative-gcd parity, factorization, the dyadic character, the Swan
phase, and the Arf phase wherever each is defined.

## Consequences

- The prospective joint discriminant sum no longer needs a separate
  squarefree indicator; even discriminants contribute zero by character
  orthogonality.
- The remaining local theorem can be posed as cancellation of four explicit
  `Z/8` discriminant phases on the affine inverse-coset system.
- Second-trace Arf invariants remain useful on the étale locus, but their
  squarefree-only applicability is no longer a representational blocker.
