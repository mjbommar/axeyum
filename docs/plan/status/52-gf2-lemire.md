# Lane: gf2-lemire — half-degree irreducibles

<!-- plan-section: lane-status -->

**WIP** (`gf2-lemire`, 2026-08-19).  Axeyum has dual-checked the non-strict
statement through degree 400 and has bounded CAS APIs for the Hayes recurrence,
exact class distributions, central moments, signed fourth cumulants, and the
exact conductor filtration of squared-discrepancy Fourier energy.  ADRs
0484--0486 keep this CAS-local; the missing estimate is analytic.

The selected sufficient obligation is
`M_4(ell,n) <= 64 ell^2 2^(3ell)` for `ell>=200` and
`n in {2ell+1,2ell+2}`.  Its implication to the universal theorem is checked
independently, but the premise is open.  It fails at the retained low control
`(5,12)` and holds experimentally at both endpoints for every `6<=ell<=23`.
Both the lemma and universal conjecture have empty-evidence ledger facts.

**Next:** prove a polynomial-times-`2^(3ell)` connected-cumulant bound, then
reconstruct reciprocity and the central lemma.  The new filtration identity
shows no isolated bad conductor through `ell=16`; pursue a nested
martingale/large-sieve estimate rather than a one-level bound.  Full record:
`docs/research/10-cas/lemire-half-degree-irreducibles.md`.

<!-- plan-section: landed-changes -->

| 2026-08-19 | `77209a5ee` | Added exact fourth moments/cumulants, checked the conditional implication and low control, retained level-23 evidence, and recorded open facts. |
| 2026-08-19 | `pending` | Added the exact resource-bounded fourth-moment conductor filtration, quotient-projection controls, public diagnostic, and literature boundary refresh. |
