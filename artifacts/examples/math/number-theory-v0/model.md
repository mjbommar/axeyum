# Model

Each check is a bounded integer or residue artifact.

```text
x == r_i mod m_i
root^2 == residue mod p
n = a^2 + b^2
sum_i coefficient_i * solution_i = target
```

The validator checks:

```text
CRT witness:          every congruence plus pairwise compatibility
quadratic residue:    root^2 modulo p
nonresidue:           exhaustive roots modulo p
nonresidue QF_BV:     fixed-width modular square refuted by DRAT
two squares witness:  a^2 + b^2
mod-4 obstruction:    squares are only 0 or 1 modulo 4
Diophantine witness:  exact linear integer equation replay
```

## Axeyum Route

The intended Axeyum route is split by shape: BV/enumeration for finite residue
searches and QF_LIA for linear Diophantine equations. The modulo-7 nonresidue
row now also carries a QF_BV artifact: a 3-bit residue `x` is guarded by
`x < 7`, zero-extended to 6 bits, squared, reduced by `bvurem 7`, and
constrained to equal `3`. The generated CNF is refuted by checked DRAT
evidence.
