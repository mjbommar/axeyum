# Lane: cas-row-three — move row 3's cas-certificate kernel-reconstructed count

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (3 new kernel-reconstructed sibling facts landed;
verified the 28-fact cas-internal backlog is unchanged and re-confirmed its
cluster breakdown; two clusters identified as genuinely needing new kernel
machinery, not cheaply reachable)`, cas-row-three, 2026-08-29).**

## Starting measurement (verified myself, step 0)

`python3 scripts/validate-facts.py` at the start of this lane:

    cas-certificate: 32 total -- kernel-reconstructed 4, cas-internal 28

Matches `docs/research/11-design-review/2026-08-28-ivt-evt-pareto-position-measured.md`'s
"Row 3, followed up" section exactly.

## Cluster breakdown of the 28 cas-internal facts — re-verified, unchanged

Wrote a small script classifying every `cas-certificate` fact via
`scripts/validate-facts.py`'s own `classify_cas_certificate_fact`, then
grouped the 28 cas-internal ones by name prefix:

Detail moved to [`../notes/274-cas-row-three.md`](../notes/274-cas-row-three.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | `a94927553` | `F:cas-extremum-deriv-sign-bracket-kernel-checked` — new bridge file `rat_prelude/cas_extremum_deriv_bridge_tests.rs`; kernel-reconstructed 4→5 |
| 2026-08-29 | `d57773ad2` | `F:cas-mvt-secant-endpoints-kernel-checked` — new bridge file `rat_prelude/cas_mvt_secant_bridge_tests.rs`; kernel-reconstructed 5→6 |
| 2026-08-29 | `af6d9f1e6` | `F:cas-taylor-remainder-lhs-kernel-checked` — new bridge file `rat_prelude/cas_taylor_remainder_bridge_tests.rs`; kernel-reconstructed 6→7 |
