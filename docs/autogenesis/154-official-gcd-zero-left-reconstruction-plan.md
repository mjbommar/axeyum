# Official-representation `Nat.gcd_zero_left` reconstruction plan

Date: 2026-08-21

The representation audit rules out importing the native `WellFounded` package
into the generic official kernel. This increment instead extends the already
accepted pointwise official-gcd model with one zero-left proof.

The new proof chooses fuel one for the pair `(0,n)`, uses the existing
`gcdGo_congr` theorem to expose exactly that fixed-fuel computation, reduces
the zero branch, and unfolds only the official `Nat.gcd` wrapper. Apart from
the two new theorem declarations and their two axiom-print commands, the
accepted predecessor source is byte-for-byte unchanged.

One pinned Lean compilation and export are authorized. Two fresh importer
audits must agree on an empty footprint and must not reach the official
`Nat.gcd_zero_left`, `WellFounded.Nat.fix_eq`, extensionality, or proposition
axioms. Success grants only the new official-representation zero-left leaf;
the closed balanced-Bézout theorem remains a separate gate.

```sh
python3 scripts/check-autogenesis-official-gcd-zero-left-reconstruction-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_zero_left_reconstruction_plan
```
