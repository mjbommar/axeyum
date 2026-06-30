# Finite Chain-Complex Torsion

This pack checks one explicit finite free abelian chain complex:

```text
C1 = Z<e>  --d1-->  C0 = Z<v>
d1(e) = 2v
d0 = 0
```

The trusted replay facts are small:

- `d0 * d1 = 0`, so the data is a chain complex.
- The Smith diagonal of `[2]` is `[2]`, so `H0 = Z/2` and `H1 = 0`.
- `2v` is a boundary, but `v` is not, because `2*k = 1` has no integer solution.

The promoted solver row is the last point encoded as a QF_LIA/Diophantine
contradiction. Axeyum may search for the contradiction, but the accepted
artifact must re-check as `Evidence::UnsatDiophantine` against the original
integer equation.

Run the focused checks with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chain-complex-torsion-v0
cargo test -p axeyum-solver --test math_resource_lia_routes finite_chain_complex_torsion_bad_generator_emits_checked_diophantine_evidence
```

General universal coefficient theorems, Ext/Tor laws, exact sequences, chain
homotopy invariance, and topological invariance are intentionally not claimed
by this pack. They remain Lean-horizon resources.
