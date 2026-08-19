# Lane: gf2-lemire — half-degree irreducibles

<!-- plan-section: lane-status -->

**WIP** (`gf2-lemire`, 2026-08-19).  The non-strict statement is independently
checked through degree 400.  Bounded native CAS operations now cover Hayes
populations, moments/conductor filtration, and exact prime-power inversion.
At odd endpoints they certify `N_(2ell+1)(1)=1+(2ell+1)I_(2ell+1)(1)`; hence
only the strict analytic bound `N_(2ell+1)(1)>1` remains there.  Even endpoints
still require the checked general proper-power subtraction.

**Next:** prove a uniform endpoint discrepancy bound, encode it as replayable
evidence, then write the paper.  The selected sufficient fourth-moment bound is
experimentally true for `6<=ell<=23` but remains an open fact; curve positivity
alone is non-strict.  Sparse and elementary degree-raising shortcuts have been
closed negatively.  Full definitions, proofs, controls, and literature record:
`docs/research/10-cas/lemire-half-degree-irreducibles.md`.

<!-- plan-section: landed-changes -->

| 2026-08-19 | `77209a5ee` | Added exact fourth moments/cumulants, checked the conditional implication and low control, retained level-23 evidence, and recorded open facts. |
| 2026-08-19 | `068e0fbff` | Added the exact resource-bounded fourth-moment conductor filtration, quotient-projection controls, public diagnostic, and literature boundary refresh. |
| 2026-08-19 | `fd9b3633d` | Corrected the fourth-moment ledger contract from an impossible irreducible mean to the exact Mangoldt-weighted population used by the CAS and conditional proof. |
| 2026-08-19 | `448be3674` | Added bounded exact Hayes prime-power inversion, exposing and invariant-checking the native identity-class irreducible count without an external CAS. |
| 2026-08-19 | `7cba6d63f` | Reduced every odd endpoint exactly to `N_(2ell+1)(1)>1`, with a bounded divisor certificate and full-inversion controls; closed `f -> x f+1` as an even-degree bridge. |
