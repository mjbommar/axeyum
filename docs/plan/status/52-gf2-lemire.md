# Lane: gf2-lemire — half-degree irreducibles and finite-field evidence

<!-- plan-section: lane-status -->

**The Lemire half-degree conjecture is an active CAS/evidence lane** (`WIP`,
gf2-lemire, 2026-08-19).  The exact target is the paper's non-strict
`deg(f-x^n) <= floor(n/2)`; the strict social-post wording fails at degree 2.
The reciprocal reduction asks for a degree-`n` prime in the identity class
modulo `x^ceil(n/2)`.

The bounded machinery is complete for present research needs.  ADRs 0480--0482
cover bit-packed `GF(2)[x]`, portable Frobenius/Bezout certificates, the finite
fact-ledger contract, and the public resource-bounded Hayes CAS API.  The API
now includes exact full-class distributions, bounded central power sums,
signed fourth-cumulant numerators, and a checked implication from an explicit
fourth-moment assumption to the theorem.  The lane gate dual-checks all degrees
`1..=400`, direct class counts through degree 20, and exact NTT/CRT endpoint
diagnostics.  Rust and independent C++ agree at `ell=24`:
`Delta_(24,49)=1651`, `Delta_(24,50)=4787`.  These are finite facts, not a
universal proof.  No SMT surface is missing: the outstanding statement is an
analytic cancellation theorem, with no solver/model/replay consumer that would
justify new SMT semantics.

The exact reductions leave a sharply bounded obligation.  Characterwise Weil
controls all but the highest `ceil(log_2 ell)+2` conductor levels within half
the candidate budget; translation kills level `2^v_2(n)`.  Equivalently, the
family norm is the numerator of one binary Carlitz cyclotomic curve, but its
generic Hasse--Weil bound still loses a factor asymptotic to `ell`.  The
centered group-ring logarithm starts at order three, yet its orders must remain
signed: at `(ell,n)=(5,12)` their absolute sum is `145632` while the answer is
`32`.

The CAS also pins the excluded routes.  A constant-one layer estimate is false
at `(j,n)=(5,45)`.  Exact-conductor Cauchy fails at `(8,17)`.  `5ddfe3984`
adds the full-family Parseval diagnostic: at the two `ell=8` endpoints its
total squared deviations are `693360` and `1861136`, exceeding uniform-mean
squares `512^2` and `1024^2`; an independent integer group-ring checker agrees.
Thus raw unweighted variance cannot force positivity at these controls.
`8649aa085` adds the missing bounded inverse-Fourier distribution API: the
actual maximum class errors are only `155` and `290`, and every class is
positive.  `77209a5ee` adds exact fourth moments and the connected numerator
`K_4=2^ell M_4-3M_2^2`.  The experimental envelope
`M_4<=64 ell^2 2^(3ell)` fails at the retained low control `(ell,n)=(5,12)`
but holds at both endpoints for every exact level `6..=23`; from `ell=200` it
would finish the universal theorem together with the certified finite range.
The universal conjecture and this selected sufficient lemma now have explicit
empty-evidence ledger facts, and no Autogenesis operation falsely claims to
establish either one.  The live problem is the connected off-diagonal
four-character bound, not missing CAS or SMT representation.
Global supersingularity is not that estimate: Gorodetsky proves this exact
cyclotomic curve nonsupersingular for every `ell>=4`.  Hsu's known bound retains
a logarithmic loss, and sparse-polynomial conjectures plus standard
Artin--Schreier doubling do not close the endpoint.

**Next.** Prove a polynomial-times-`2^(3ell)` fourth-moment bound, equivalently
control the connected fourth cumulant after the three Gaussian pairings, at
`n=2 ell+1,2 ell+2`; a direct class-sensitive `L^infinity` estimate or universal
construction remains an alternative.  Then reconstruct reciprocity and the
central lemma through the kernel before promoting the universal ledger fact or
claiming a proof.  Full derivations, literature audits, provenance, and
rejected routes remain in
`docs/research/10-cas/lemire-half-degree-irreducibles.md`.

Earlier certificate, range-search, recurrence, Fourier, conductor, and centered-
log increments are retained with their exact commits and evidence in the linked
research note; this operational table keeps only the current proof-direction
changes.

<!-- plan-section: landed-changes -->

| 2026-08-19 | `77209a5ee` | Added exact bounded central moments and signed fourth cumulants, independently checked the conditional fourth-moment implication and its low-level failure control, recorded exact evidence through level 23, and created empty-evidence ledger facts for the open lemma and universal conjecture without inventing SMT or Autogenesis credit. |
| 2026-08-19 | `7f73d02cd` | Added a bounded native distribution-only runner for exact per-class minima, maxima, maximum deviations, and positivity, keeping finite evidence distinct from the missing uniform theorem. |
| 2026-08-19 | `8649aa085` | Added exact bounded inverse-Fourier class distributions, matched Parseval and an independent group-ring implementation, and isolated the surviving class-sensitive `L^infinity` problem. |
| 2026-08-19 | `5ddfe3984` | Added an exact full-family Parseval diagnostic, dual-checked both `ell=8` endpoints, and showed that raw total variance cannot supply the missing positivity estimate. |
| 2026-08-19 | `f02916fa9` | Proved translation pairing for level `2^v_2(n)`, bounded all but the top `ceil(log_2 ell)+2` levels by ordinary Weil, retained the bounded one-level runner, and extended the exact native endpoint diagnostic to `ell=24`. |

| 2026-08-19 | `fda041d49` | Independently replayed the level-24 endpoint transform in C++ on s1, matched both native Axeyum discrepancies with hashed provenance, and identified the family norm as one cyclotomic curve's zeta numerator without misusing the generic Hasse--Weil bound. |
