# Model

Each check is a bounded integer or residue artifact.

```text
x == r_i mod m_i
root^2 == residue mod p
n = a^2 + b^2
sum_i coefficient_i * solution_i = target
gcd(coefficients) ∤ target
```

The validator checks:

```text
CRT witness:          every congruence plus pairwise compatibility
quadratic residue:    root^2 modulo p
nonresidue:           exhaustive roots modulo p
nonresidue QF_BV:     fixed-width modular square refuted by DRAT
bad square witness:   candidate^2 modulo p disagrees with target
bad witness QF_BV:    fixed-width modular square value conflict refuted by DRAT
two squares witness:  a^2 + b^2
mod-4 obstruction:    squares are only 0 or 1 modulo 4
Diophantine witness:  exact linear integer equation replay
Diophantine QF_LIA:   gcd-divisibility obstruction refuted by UnsatDiophantine
```

## Axeyum Route

The intended Axeyum route is split by shape: BV/enumeration for finite residue
searches and QF_LIA for linear Diophantine equations. The modulo-7 nonresidue
row now also carries a QF_BV artifact: a 3-bit residue `x` is guarded by
`x < 7`, zero-extended to 6 bits, squared, reduced by `bvurem 7`, and
constrained to equal `3`. The generated CNF is refuted by checked DRAT
evidence. The bad square-root row uses the same route for a concrete witness:
it computes `2*2 mod 7 = 4` at 6-bit product width and refutes the false target
`2`.

The Diophantine obstruction row carries the QF_LIA route: it encodes
`14*x + 21*y = 5`, emits checked `UnsatDiophantine` evidence, and rechecks the
gcd contradiction against the original integer equation.
