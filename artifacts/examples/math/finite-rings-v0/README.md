# Finite Rings V0

This pack covers the first core-structure slice for `rings`: two finite
operation tables, additive group structure, multiplication, distributivity, and
zero divisors.

The examples are finite table artifacts:

- replay `Z/4Z` as a ring under addition and multiplication;
- replay the zero-divisor witness `2 * 2 = 0 mod 4`;
- reject a fixed two-operation table that violates distributivity;
- reject a fixed two-operation table that falsely claims a multiplicative
  identity.

These checks are small finite artifacts. They do not claim ideal theory,
Noetherian/PID/UFD structure, or quantified ring theory.

## Concepts

- `curriculum_rings`
- `curriculum_groups`
- `field_abstract_algebra`

## Trust Story

The validator checks addition as an abelian group, multiplication closure and
associativity, optional multiplicative identity, and both distributive laws. The
zero-divisor row is accepted only after replaying a nonzero product to the
additive identity. The negative row is accepted only because distributivity
fails on the listed finite table.

The bad distributivity row has a QF_BV proof-route artifact:
[`smt2/non-distributive-table-bitblast-conflict.smt2`](smt2/non-distributive-table-bitblast-conflict.smt2).
For the failing triple `(a=1,b=0,c=0)`, the source table computes
`a*(b+c)=1` and `(a*b)+(a*c)=0`; the artifact records the resulting one-bit BV
contradiction.

The bad multiplicative-identity row has the same route:
[`smt2/bad-multiplicative-identity-bitblast-conflict.smt2`](smt2/bad-multiplicative-identity-bitblast-conflict.smt2).
For the claimed identity `one=1` and element `1`, the source table computes
`1*1=0` even though the identity law requires `1`. The solver regression
exports DIMACS/DRAT certificates for both QF_BV artifacts, and
`UnsatProof::recheck` validates them. The finite table-to-term lowering and
bit-blast/Tseitin steps remain explicit trust steps until Lean reconstruction
covers the original formulas.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-rings-v0
cargo test -p axeyum-solver --test math_resource_bv_routes finite_rings_bad_multiplicative_identity_emits_checked_drat
cargo test -p axeyum-solver --test math_resource_bv_routes finite_rings_bad_distributivity_emits_checked_drat
```
