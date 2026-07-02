# Checks

| Check | Expected | Evidence |
|---|---|---|
| `householder-formula-witness` | `sat` | replay-only |
| `householder-orthogonality-witness` | `sat` | replay-only |
| `householder-zeroing-witness` | `sat` | replay-only |
| `householder-involution-witness` | `sat` | replay-only |
| `householder-determinant-witness` | `sat` | replay-only |
| `bad-householder-entry-rejected` | `unsat` | replay-only |
| `qf-lra-bad-householder-entry` | `unsat` | checked |
| `general-householder-qr-theory-lean-horizon` | `not-run` | Lean horizon |

The replay rows recompute the reflector denominator, the Householder matrix
entries, the transpose, orthogonality, the zeroing product, involution,
determinant, and squared norms exactly.

The checked row uses:

```text
artifacts/examples/math/finite-householder-reflection-v0/smt2/bad-householder-entry-farkas-conflict.smt2
```

That artifact asserts both `householder_entry_00 = -3/5` and
`householder_entry_00 = -4/5`. The solver regression must emit
`Evidence::UnsatFarkas` and independently check the certificate.
