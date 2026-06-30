# Finite Universal Coefficient Shadow

This pack checks one finite degree-one shadow of the universal coefficient
theorem for the same two-term complex used by the torsion resource:

```text
C1 = Z<e>  --d1=[2]-->  C0 = Z<v>
```

The dual cochain map is also `[2]`, so the replayed cohomology is:

```text
H^0 = 0
H^1 = Z/2
```

The degree-one universal-coefficient shape for this fixed complex is:

```text
0 -> Ext(H0, Z) -> H^1 -> Hom(H1, Z) -> 0
0 -> Z/2        -> Z/2 -> 0          -> 0
```

The promoted solver row rejects the false claim `H^1 = 0` after replay has
computed `H^1 = Z/2`. The SMT-LIB artifact is intentionally a pure EUF equality
conflict: `H1 = Z2`, `H1 = Zero`, and `Z2 != Zero`. Axeyum may search for the
conflict, but accepted evidence must re-check as `Evidence::UnsatAletheProof`.

Run the focused checks with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-universal-coefficient-shadow-v0
cargo test -p axeyum-solver --test math_resource_uf_routes finite_universal_coefficient_bad_h1_zero_emits_checked_alethe
```

The general universal coefficient theorem, naturality, exact-sequence proof,
Ext/Tor functor laws, splitting choices, and arbitrary chain-complex statements
remain Lean-horizon resources.
