# Lane: gf2-lemire — half-degree irreducibles

<!-- plan-section: lane-status -->

**WIP** (`gf2-lemire`, 2026-08-19).  The non-strict statement is independently
checked through degree 400.  Bounded native CAS operations now cover Hayes
populations, moments/conductor filtration, and exact prime-power inversion.
At odd endpoints they certify `N_(2ell+1)(1)=1+(2ell+1)I_(2ell+1)(1)`; hence
only the strict analytic bound `N_(2ell+1)(1)>1` remains there.  Even endpoints
still require the checked general proper-power subtraction.  The CAS now also
has proved closed forms for every pair of principal-unit interval degrees:
exact mixed product energies and nonprincipal Fourier `L^2 x L^2` moments.

**Next:** prove a uniform endpoint discrepancy bound, encode it as replayable
evidence, then write the paper.  The selected sufficient fourth-moment bound is
experimentally true for `6<=ell<=23` but remains an open fact; curve positivity
alone is non-strict.  The exact half-level Möbius sieve now has a native
positive-composite counterexample, so the elementary divisor-density route
requires genuine Type-II/bilinear cancellation.  Sparse and elementary
degree-raising shortcuts have also been closed negatively.  The new mixed
energies are genuine Type-II inputs, but they do not control the connected
cross-degree terms in the required Mangoldt fourth moment.  The exact
diagnostic through `ell=26` led to a uniform proved wild-Kloosterman amplitude
bound for the extremal pair `V_(ell-1)^2`, now exposed as a bounded native CAS
report and as an explicitly uncredited Autogenesis fact obligation.  The
stronger exact plateau support formula remains finite evidence only, but is no
longer a dependency.  The Kloosterman estimate is unweighted, while a Vaughan
decomposition is Möbius-weighted; substituting one for the other has now been
closed as invalid.  Exact signed classwise Möbius distributions are exposed as
a bounded native diagnostic with independent factorization controls.  Proving
a weighted binary bilinear estimate, a recurrence-wide Möbius bound, or the
aggregate endpoint estimate remains open.  Group-ring logarithmic
differentiation now reduces that choice to one exact short signed
Möbius-convolution sum; the CAS reconstructs it from a single recurrence table
and the ledger exposes its still-unproved uniform endpoint bound without
granting finite experiments theorem credit.  A direct small-degree
factorization oracle now checks each convolution term and detects inverse- and
weight-dropping mutations independently of the transform reconstruction.  The
exact additive-Fourier bridge is now native: a checked Walsh spectrum recovers
every inverse-interval fibre, while a direct factorization oracle validates
the reciprocal-polynomial and ramified-`x` identity frequency by frequency.
The source-level characteristic audit isolates the reusable Hölder/energy
core from the odd-characteristic complete-sum input.  Exact inverse-additive
energy is now a separate native diagnostic with a direct collision oracle;
fleet rows through level 21 suggest, but do not prove, a no-wrap regime.  The
source dependency table and exact exponent ledger are now complete.  They
show that direct substitution of the proved binary wild-Kloosterman maximum
loses all uniform saving in Bagshaw's Type-I Case 5, while even the published
zero-epsilon exponent pair would pointwise cover only the tail
`d>(14/15)ell+O(1)`.  The next step is therefore a replacement estimate on
the uncovered Type-I/low-`d` range, not a verbatim Bagshaw port or more
normalization guesswork.
Full definitions,
proofs, controls, and literature record:
`docs/research/10-cas/lemire-half-degree-irreducibles.md`.

<!-- plan-section: landed-changes -->

| 2026-08-19 | `eef2032e5` | Completed the source-level Bagshaw dependency audit and added exact non-credit-bearing exponent ledgers that isolate the binary Type-I Case-5 obstruction and the uncovered endpoint interval range. |
| 2026-08-19 | `e0398d06a` | Added exact inverse-additive interval energy and Walsh fourth moments with independent collision controls, a characteristic-two source audit, and an explicit boundary against finite no-wrap inference. |
| 2026-08-19 | `329e842c6` | Recorded the exact inverse-additive Fourier and reciprocal-polynomial bridge in the canonical research note and lane status. |
| 2026-08-19 | `3c3be779a` | Added the exact inverse-additive Möbius Walsh spectrum, annihilator reconstruction, and frequencywise direct controls for the reciprocal-polynomial and ramified-`x` bridge. |
| 2026-08-19 | `c021db86a` | Added a direct Berlekamp-factorization oracle for every endpoint convolution term through level 5, with mutation controls for inverse-class and interval-weight errors. |
| 2026-08-19 | `53eeeda49` | Reduced the endpoint discrepancy to one exact signed Möbius-convolution sum, added a one-table native reconstruction with endpoint controls, and exposed the remaining uniform bound as an uncredited ledger obligation. |
| 2026-08-19 | `0e9bacef9` | Added exact signed classwise polynomial-Mobius distributions with dual-modulus reconstruction, independent Berlekamp-factorization controls, and an explicit boundary against unproved weighted cancellation. |
| 2026-08-19 | `88288f006` | Exposed the stationary-phase bound as an uncredited formal fact obligation so Autogenesis can see it without mistaking bounded tests for a universal certificate. |
| 2026-08-19 | `6e02ac7d6` | Proved the uniform binary wild-Kloosterman amplitude bound by stationary phase, exposed its bounded native CAS report, and pinned exhaustive direct controls through level 9. |
| 2026-08-19 | `afec92512` | Isolated the top inverse-coefficient plateau-spectrum candidate, its exact connection to `V_(ell-1)^2`, and dual local/fleet evidence through `ell=26` without granting theorem credit. |
| 2026-08-19 | `0513b1a22` | Generalized the equal-degree product energy to every ordered interval-degree pair, proved the two closed-form regimes, and checked all mixed collision tables through `ell=8`. |
| 2026-08-19 | `31b862946` | Added the exact closed-form principal-unit product energy and Fourier fourth moment, with direct native collision-table controls and an explicit boundary against the still-open Mangoldt moment. |
| 2026-08-19 | `5fac62cbb` | Added the bounded exact half-interval Möbius identity, pinned its first positive-composite parity counterexample with native Berlekamp factorization, and ruled out Porritt's explicit bound at `q=2`. |
| 2026-08-19 | `77209a5ee` | Added exact fourth moments/cumulants, checked the conditional implication and low control, retained level-23 evidence, and recorded open facts. |
| 2026-08-19 | `068e0fbff` | Added the exact resource-bounded fourth-moment conductor filtration, quotient-projection controls, public diagnostic, and literature boundary refresh. |
| 2026-08-19 | `fd9b3633d` | Corrected the fourth-moment ledger contract from an impossible irreducible mean to the exact Mangoldt-weighted population used by the CAS and conditional proof. |
| 2026-08-19 | `448be3674` | Added bounded exact Hayes prime-power inversion, exposing and invariant-checking the native identity-class irreducible count without an external CAS. |
| 2026-08-19 | `7cba6d63f` | Reduced every odd endpoint exactly to `N_(2ell+1)(1)>1`, with a bounded divisor certificate and full-inversion controls; closed `f -> x f+1` as an even-degree bridge. |
