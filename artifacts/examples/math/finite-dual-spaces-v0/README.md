# Exact Finite Dual Space Checks

This pack adds a finite dual-space bridge after vector spaces, modules, and
tensor products. It uses `F2^2`, so every covector is represented by an explicit
finite table into `F2`.

It checks:

- each listed covector is linear;
- dual-space addition and scalar multiplication are pointwise;
- a primal basis and dual basis pair as the identity matrix;
- an annihilator is recomputed from the evaluation table;
- a transpose map satisfies `(T*phi)(v) = phi(Tv)`;
- a malformed covector is rejected by an additivity counterexample;
- general duality and functional analysis are marked Lean-horizon.

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dual-spaces-v0
```
