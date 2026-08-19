# Lane: gf2-lemire — half-degree irreducibles and finite-field evidence

<!-- plan-section: lane-status -->

**The Lemire half-degree conjecture is an active CAS/evidence lane** (`WIP`,
gf2-lemire, 2026-08-19).  The exact target is the paper's non-strict
`deg(f-x^n) <= floor(n/2)`; the strict social-post wording fails at degree 2.
The reciprocal reduction asks for a degree-`n` prime in the identity class
modulo `x^ceil(n/2)`.

The bounded machinery is complete for present research needs.  ADRs 0480--0482
cover bit-packed `GF(2)[x]`, portable Frobenius/Bezout certificates, the finite
fact-ledger contract, and the public resource-bounded Hayes CAS API.  The lane
gate dual-checks all degrees `1..=400`, direct class counts through degree 20,
and exact NTT/CRT endpoint diagnostics.  Rust and independent C++ agree at
`ell=24`: `Delta_(24,49)=1651`, `Delta_(24,50)=4787`.  These are finite facts,
not a universal proof.  No SMT surface is missing: the outstanding statement
is an analytic cancellation theorem, with no solver/model/replay consumer that
would justify new SMT semantics.

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
positive.  A distribution-only native runner now exposes the exact bounded
`L^infinity` diagnostic independently of the heavier moment runner.  The live
analytic distinction is therefore `L^infinity` versus raw `L^2`, suggesting a
class-sensitive higher-moment or hypercontractive estimate.
Global supersingularity is not that estimate: Gorodetsky proves this exact
cyclotomic curve nonsupersingular for every `ell>=4`.  Hsu's known bound retains
a logarithmic loss, and sparse-polynomial conjectures plus standard
Artin--Schreier doubling do not close the endpoint.

**Next.** Prove a class-sensitive `L^infinity` or signed/weighted estimate for
the highest
`ceil(log_2 ell)+2` conductor levels at `n=2 ell+1,2 ell+2`, or find a universal
construction.  Then reconstruct reciprocity and the central lemma through the
kernel before promoting the finite ledger fact or claiming a proof.  Full
derivations, literature audits, provenance, and rejected routes remain in
`docs/research/10-cas/lemire-half-degree-irreducibles.md`.

<!-- plan-section: landed-changes -->

| 2026-08-19 | `7f73d02cd` | Added a bounded native distribution-only runner for exact per-class minima, maxima, maximum deviations, and positivity, keeping finite evidence distinct from the missing uniform theorem. |
| 2026-08-19 | `8649aa085` | Added exact bounded inverse-Fourier class distributions, matched Parseval and an independent group-ring implementation, and isolated the surviving class-sensitive `L^infinity` problem. |
| 2026-08-19 | `5ddfe3984` | Added an exact full-family Parseval diagnostic, dual-checked both `ell=8` endpoints, and showed that raw total variance cannot supply the missing positivity estimate. |
| 2026-08-19 | `f02916fa9` | Proved translation pairing for level `2^v_2(n)`, bounded all but the top `ceil(log_2 ell)+2` levels by ordinary Weil, retained the bounded one-level runner, and extended the exact native endpoint diagnostic to `ell=24`. |

| 2026-08-19 | `fda041d49` | Independently replayed the level-24 endpoint transform in C++ on s1, matched both native Axeyum discrepancies with hashed provenance, and identified the family norm as one cyclotomic curve's zeta numerator without misusing the generic Hasse--Weil bound. |

| 2026-08-18 | `01cc5dfdf` | Pinned the exact centered-order cancellation vector and refuted a second triangle route: its absolute sum is `145632` where the full endpoint discrepancy is `32`. |
| 2026-08-18 | `f247587c6` | Derived the exact centered endpoint logarithm, proved its linear and quadratic orders vanish structurally, and independently checked the resulting connected-correlation expansion. |
| 2026-08-18 | `a48c57824` | Added exact conductor-family second moments, refuted generic Cauchy at `(8,17)`, and pinned the direct `(5,45)` counterexample to the otherwise sufficient constant-one layer target. |

| 2026-08-18 | `1ff1ca6b7` | Extracted bounded reusable Hayes/principal-unit/conductor CAS APIs, dual-checked the conditional sufficient-bound arithmetic, retained the missing cancellation lemma as an explicit obligation, and independently reproduced `ell=23`. |
| 2026-08-18 | `4b129601c` | Extended the exact NTT/CRT endpoint oracle through `ell=22`, added an a-priori CRT uniqueness guard, reduced peak memory, and isolated the family-norm cancellation factor that the universal proof must recover. |
| 2026-08-18 | `6aff45e82` | Added accepted ADR-0481 and a canonical, mutation-checked certificate-spec fact for the dual-replayed degree-1-through-400 result without inventing finite-field SMT or kernel support. |
| 2026-08-18 | `30a004188` | Audited the tempting Hsu half-coefficient survey claim against the explicit bound and the 2023 Gao follow-up; neither supplies positivity at the exact fixed-`GF(2)` endpoint. |
| 2026-08-18 | `fd1e8793b` | Added an exact finite principal-unit Fourier oracle using two NTT primes and CRT, verified the sufficient endpoint-discrepancy candidate through `ell=18`, and kept the candidate explicitly outside the theorem and fact ledger. |
| 2026-08-18 | `d32ebbdb1` | Corrected the half-boundary parameterization, derived the exact integral Hayes recurrence, and gated its identity-class counts against an independent direct Rabin enumeration through degree 20. |
| 2026-08-18 | `6e1372073` `d308c7bc1` | Added deterministic content-bound search shards; five hosts produced and the repository admitted 400/400 dual-checked degrees, with finite-range credit explicitly separated from the universal conjecture. |
| 2026-08-18 | `98f2d953f` `b678ec7e6` `3718aab11` | Added canonical bounded artifacts, an algebraically separate dense checker, standalone producer/checker CLIs, and the dual-gated degree-400 witness; completion does not claim the universal theorem. |
| 2026-08-18 | `81321fc65` | Added bounded bit-packed `GF(2)[x]`, untrusted Rabin certificate production, independent identity checking, exhaustive degree-10 oracle agreement, certificate mutations, the exact Lemire theorem contract, and accepted ADR-0480. |
