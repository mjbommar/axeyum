# Cancellation dependency audit isolates six carriers

One non-rendering read classified all seventeen direct dependencies of the V2
cancellation theorem. Eleven are empty-footprint. Six reach exactly `propext`:

- `Nat.dvd_add`
- `Nat.dvd_add_iff_right`
- `Nat.dvd_mul_right_of_dvd`
- `Nat.mul_left_comm`
- `Nat.right_distrib`
- `eq_self`

The next proof should replace direct divisibility closure with existential
witness construction, reuse or reconstruct clean multiplication/distributivity
leaves, and isolate a target-owned additive divisibility-cancellation lemma.

The sealed manifest is
`/nas3/data/axeyum/autogenesis/reference-packs/efe97708a-coprime-factor-cancellation-dependency-audit-v1/manifest.json`
with SHA-256
`c2a7e50b8af4f19139cf43b7a2398eeae961057320b4344fe63bdabef1a293ae`.
