# Exact Finite Tensor Product Checks

This pack adds a small tensor-product bridge after the finite vector-space and
module packs. It uses finite vector spaces over `F2`, so every claim reduces to
finite table replay.

It checks:

- dimension and basis replay for `F2^2 tensor F2`;
- bilinearity of a finite table `beta(v,a) = a*v`;
- a finite universal-property shadow, where a bilinear scalar map factors
  through the tensor map by a linear projection;
- a fixed Kronecker-product matrix over `F2`;
- checked rejection of a malformed bilinear map;
- Lean-horizon metadata for general tensor and multilinear algebra.

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-tensor-products-v0
```
