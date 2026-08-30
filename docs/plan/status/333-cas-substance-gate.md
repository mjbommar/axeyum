# Lane 333 — CAS substance gate

<!-- plan-section: lane-status -->

**Status: LANDED.** `scripts/check-cas-substance.py` is green on the committed
ledger and registered in both `scripts/check.sh` and the `justfile`
(`check-aggregate-scope.sh` green, 66 recorded differences, no new one-sided
step). Decision recorded in
[ADR-0622](../../research/09-decisions/adr-0622-a-reconstruction-must-say-what-it-establishes.md).

## The deficiency

`scripts/validate-facts.py`'s `classify_cas_certificate_checker` returns
`kernel-reconstructed` when some executed `cargo test` / `cargo run` segment
merely NAMES the `axeyum-lean-kernel` package. It never inspects what the kernel
was asked to check. So the headline

    cas-certificate: 42 total -- kernel-reconstructed 14, cas-internal 28

moved identically for `poly_expr(X) = Rat.ofInt 1 * poly_expr(X)` — true of
every polynomial — and for a six-variable identity with real cancellation.

## The measurement, all 14

Derived by `scripts/cas_substance.py` from the certificate the CAS emitted,
where one exists; declared by the fact where none does. `in`/`out` are monomials
entering the combination and remaining in the conclusion, per conclusion.

| fact | shape | provenance | active gens | in → out |
| --- | --- | --- | --- | --- |
| `F:geometry-centroid-divides-medians-kernel-checked` | `combination` | derived | 3 | 88 → 4 (×2) |
| `F:geometry-medians-cofactor-identity-kernel-checked` | `combination` | derived | 2 | 20 → 10 |
| `F:geometry-orthocentre-cofactor-identity-kernel-checked` | `combination` | derived | 2 | 16 → 8 |
| `F:geometry-parallelogram-diagonals-bisect-kernel-checked` | `combination` | derived | 3 | 60 → 4 (×2) |
| `F:geometry-rhombus-cofactor-identity-kernel-checked` | `combination` | derived | 4 | 264 → 8 |
| **`F:geometry-thales-cofactor-identity-kernel-checked`** | **`refl`** | derived | 1 | **8 → 8, zero cancellation** |
| `F:cas-difference-of-squares-free-x-kernel-checked` | `identity` | declared | — | free `x` |
| `F:cas-partial-fractions-mixed-general-case-kernel-checked` | `identity` | declared | — | `forall x` |
| `F:cas-evt-endpoint-exclusion-cubic-kernel-checked` | `evaluation` | declared | — | concrete |
| `F:cas-extremum-deriv-sign-bracket-kernel-checked` | `evaluation` | declared | — | concrete |
| `F:cas-ivt-degree4-sign-bracket-kernel-checked-cost-curve` | `evaluation` | declared | — | concrete |
| `F:cas-ivt-sign-bracket-cbrt2-kernel-checked` | `evaluation` | declared | — | concrete |
| `F:cas-mvt-secant-endpoints-kernel-checked` | `evaluation` | declared | — | concrete |
| `F:cas-taylor-remainder-lhs-kernel-checked` | `evaluation` | declared | — | concrete |

Detail moved to [`../notes/333-cas-substance-gate.md`](../notes/333-cas-substance-gate.md).

