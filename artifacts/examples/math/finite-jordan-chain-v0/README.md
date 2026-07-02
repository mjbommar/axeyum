# Finite Jordan-Chain Checks

This pack checks one exact rational Jordan-chain shadow for the `2x2` Jordan
block

```text
A = [[2, 1],
     [0, 2]].
```

It is deliberately finite. The trusted work is exact matrix-vector and
matrix-matrix replay plus a checked `QF_LRA/Farkas` contradiction for one false
generalized-eigenvector component.

It does not claim the Jordan normal form theorem, diagonalization criteria,
algebraic/geometric multiplicity theory, or numerical eigensolver behavior.

## Resource Shape

- fixed Jordan block `A = [[2,1],[0,2]]`;
- eigenvalue `lambda = 2`;
- nilpotent part `N = A - lambda*I = [[0,1],[0,0]]`;
- eigenvector `v1 = [1,0]`;
- generalized eigenvector `v2 = [0,1]`;
- exact checks `A*v1 = 2*v1`, `N*v2 = v1`, and `A*v2 = 2*v2 + v1`;
- nilpotent replay `N^2 = 0` while `N` is nonzero;
- Jordan reconstruction `P*J*P^-1 = A`;
- replay-only rejection of a malformed claim about the first component of
  `N*v2`;
- checked `QF_LRA/Farkas` artifact for the scalar contradiction
  `nilpotent_image_0 = 1` and `nilpotent_image_0 = 0`;
- Lean-horizon row for general Jordan theory and diagonalization theorems.

## Trust Boundary

```text
untrusted fast search -> candidate eigenvectors or Jordan-chain data
trusted small checking -> exact rational replay and Farkas certificate
remaining horizon -> general Jordan normal form and diagonalization theory
```

## Validate

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-jordan-chain-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_jordan_chain_bad_component_artifact_emits_checked_farkas
```
