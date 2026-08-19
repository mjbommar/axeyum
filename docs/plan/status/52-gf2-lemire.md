# Lane: gf2-lemire — half-degree irreducibles

<!-- plan-section: lane-status -->

**WIP** (`gf2-lemire`, 2026-08-19).  Axeyum has dual-checked the non-strict
statement through degree 400 and has bounded CAS APIs for the Hayes recurrence,
exact class distributions, central moments, signed fourth cumulants, and the
exact conductor filtration of squared-discrepancy Fourier energy.  ADRs
0484--0486 keep this CAS-local; the missing estimate is analytic.

The open fourth-moment fact now pins the quantity actually computed:
`N_n(e)` is the degree-`n` Mangoldt population, not the unweighted
irreducible count.  The existing checked Hayes/Mobius step is what removes
proper prime powers before concluding irreducible positivity.

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

The sparse-construction audit is closed negatively.  All 400 committed
witnesses are weight 1, 3, or 5, with the exact 1/227/172 distribution already
enforced by the finite-range gate.  An all-degree shaped trinomial-or-
pentanomial construction would imply the *Handbook of Finite Fields*
Conjecture 2.2.5, while the published `2b+c` pentanomial family neither proves
irreducibility for all parameters nor meets the half-tail inequality.  Do not
replace the Hayes obligation with extrapolation from the sparse artifacts.

The cyclotomic curve identity also implies unconditionally that the identity
class Mangoldt population is positive in every degree:
`#C_ell(GF(2^n))=2^ell N_n(1)+1`, while the `2^ell` places over infinity are
already rational.  This narrows but does not close the theorem, because the
positive population may consist only of proper prime powers.  The live bound
must still prove new degree-`n` mass after the checked proper-power subtraction.

<!-- plan-section: landed-changes -->

| 2026-08-19 | `77209a5ee` | Added exact fourth moments/cumulants, checked the conditional implication and low control, retained level-23 evidence, and recorded open facts. |
| 2026-08-19 | `068e0fbff` | Added the exact resource-bounded fourth-moment conductor filtration, quotient-projection controls, public diagnostic, and literature boundary refresh. |
| 2026-08-19 | `pending` | Corrected the fourth-moment ledger contract from an impossible irreducible mean to the exact Mangoldt-weighted population used by the CAS and conditional proof. |
