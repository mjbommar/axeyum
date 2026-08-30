# Notes: 223-cas-reconstruct

Detail moved out of [`../status/223-cas-reconstruct.md`](../status/223-cas-reconstruct.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Honest accounting, stated so the increment is not over-read.** The
reconstructions are not new work by this lane; the ledger simply did not hold
them. Why they were missed is itself the useful finding: the `cas-certificate`
rows were written **per mathematical result**, and slice 1's mathematics
(`(x+1)(x-1) = x^2-1`) is trivial — but under ADR-0601 the unit of account for
row 3 is the **route**, not the theorem. By that measure the difference-of-
squares row is the *strongest* kernel-reconstructed row in the ledger: it is
universally quantified over a genuinely free fvar, so no numeral reduction is
available to paper over a defeq gap, and it decides both directions.

**Neither of the two facts the brief named was converted, and neither could
be by this lane.** `F:cas-ivt-cbrt2-in-1-2` and `F:cas-extremum-irrational-argmax`
both claim a **Sturm count**, and folding the existing sign-bracket evidence
into either would make `classify_cas_certificate_fact` label the *whole*
certificate — root containment and Sturm count included — as reconstructed.
`cas_ivt_bridge_tests`'s own module doc says exactly this, which is why the
sibling-fact pattern exists.

## The access blocker, which is structural and is not mathematical

**A lane that cannot write `crates/axeyum-lean-kernel/` cannot produce a new
kernel-reconstructed row at all.** `Kernel::add_declaration` is reachable only
through `IntDev::new`, which is `pub(crate)`; `complex/cas_bridge_tests.rs`'s
module doc already states that an external crate cannot reach the development
handle or the ring-law decision procedure. `axeyum-cas` deliberately does not
depend back on `axeyum-lean-kernel` (both `Cargo.toml`s say so), so the bridge
can only be written from inside the kernel crate. This lane's brief scoped that
crate read-only, so registration of existing bridges was the whole reachable
surface. **A future row-3 lane must be given write access to
`crates/axeyum-lean-kernel/src/{rat_prelude,complex}/` or it cannot succeed.**

## Backlog or boundary? Measured: 28 is a BACKLOG

The brief asks whether the remaining 28 are structurally unreconstructable.
**None of them is.** Richardson's theorem bites on zero-testing for expressions
built from `exp`/`sin`/`abs` and a transcendental constant. **No
`cas-certificate` fact in this ledger poses that obligation.** The one place a
transcendental function appears at all is the WZ rows' Gamma-quotient
*specification* of a hypergeometric term — and the certificate's actual
verification obligation is a **rational-function identity**, reached by the
Gamma functional equation, which is exactly why Gosper/Zeilberger terminate.
Everything else is polynomial or rational over ℚ, or a bounded finite-field
enumeration. Every one of the 28 is therefore inside the decidable fragment.
The clusters, read from each fact's `formal.fragment` and `axiom_footprint`:

| cluster | n | what the checker actually verifies | kernel machinery missing | residual assumption reconstruction CANNOT remove |
| --- | --- | --- | --- | --- |
| hypergeometric / WZ | 9 | a creative-telescoping certificate; clearing denominators makes it a polynomial identity in `(n,k)` | multivariate polynomial identity; a telescoping-sum lemma; a kernel definition of the summand | **YES** — `cas.gamma-functional-equation`, `cas.hyperterm-specification-denotes-the-summand` |
| NRA geometry | 10 | a cofactor identity `Σ hᵢgᵢ = f` in `ℚ[x₁..xₙ]` (+ Rabinowitsch) | a **multivariate** ring layer — the kernel has none (`MultiPoly` appears nowhere in `axeyum-lean-kernel/src/` except the bridge's own univariate-only restriction doc) | **YES** — `geometry.cartesian-coordinatisation-of-the-euclidean-plane` |
| real-algebraic (IVT/EVT/MVT/Taylor) | 4 | a Sturm chain plus a sign-variation count | `Rat` polynomial division with remainder → Sturm chain → Sturm's theorem itself | no |
| partial fractions | 1 | clearing denominators: a **univariate** polynomial identity | very little beyond what the existing bridge does — factorization and the linear solve are *search*, not check | no |
| gf2 | 4 | finite-field identities / bounded enumeration | a GF(2) carrier; 2 of the 4 also need Rabin irreducibility and lifting-the-exponent as real theorems | no |

Two findings that follow, and the second is the actionable one:

1. **For 19 of the 28 (WZ + geometry), reconstruction relocates rather than
   discharges the assumption.** Proving `Σ hᵢgᵢ = f` in the kernel does not
   prove that those polynomials mean the geometric predicates they are named
   after; the ledger already keeps a separate coordinatisation control for
   exactly this (`geometry_encoding_agreement`). The same holds for the WZ
   rows' "the Gamma-quotient specification denotes the summand". So the honest
   ceiling for those 19 is *smaller* than "kernel-reconstructed" sounds — the
   modelling axiom becomes a kernel **definition choice**, which is better, but
   it is not removed.
2. **`Rat.polyEval_mul` is the single highest-leverage missing piece, and it is
   closer than the fact notes suggest.** `rat_prelude/polynomial.rs`'s own
   module doc (which says it "has now been wrong twice in opposite directions",
   so it enumerates what is CHECKED) reports the ℚ reindexing machinery
   *done* — `Rat.sumRange_split`, `sumRange_diagonal`,
   `sumRange_rect_eq_diag_add_corner`, the two-bound rectangle steps, and the
   antidiagonal cell collapse `declare_pow_sub_add`. What remains is a
   four-factor ring rearrangement under `sumRange_congr_lt`, plus a decision
   about the statement, because the corner term does **not** simplify to a
   `polyEval` (the naive two-term identity is refuted at `n = 2`, 66 of 91).

**A stale blocker, corrected.** `F:cas-ivt-sign-bracket-cbrt2-kernel-checked`'s
notes size item 2 (root containment) as needing "a `Rat` polynomial long-
division/remainder construction … it does not yet [exist]". That is true over
`Rat` and **false over `Complex`**: `complex/poly.rs` already declares
`polyMul`, `polyEval_polyMul`, `factorQuotient`, `factorQuotient_degreeLt` and
`factorQuotient_succ_eq`, and its own module doc says "this section used to say
`polyMul` and the factor theorem were not there". `factorQuotient` divides by a
**linear** `(X − a)` only, so it does not cover division by an arbitrary
minimal polynomial — but for a certificate whose root is *simple*, item 2 is
now a short bridge over `Complex`, not a missing construction. This is the
retrieval hazard `CLAUDE.md` keeps recording: verify a blocker still exists
before sizing work against it.

## Next lane

Give it write access to `crates/axeyum-lean-kernel/`. In value order:

1. **`F:cas-extremum-irrational-argmax`, endpoint exclusion** — the decisive
   half of that certificate is pure rational arithmetic and needs *no new
   kernel machinery at all*. For `p = x³ − 6x` on `[−3, 2]`: shift to
   `q = p − p(−3)` (integer coefficients `[9,−6,0,1]`) and `r = p − p(2)`
   (`[4,−6,0,1]`), then admit `0 < polyEval q 4 (ofInt −1)` and
   `0 < polyEval r 4 (ofInt −1)` with the *existing* `zero_lt_via_nat_le`. That
   kernel-proves `p(−1) > p(−3)` and `p(−1) > p(2)` — i.e. **the maximum is
   interior, not at an endpoint** — as a sibling fact. The Sturm completeness
   claim stays `cas-internal`, correctly.
2. Add the missing swapped-statement negative control to
   `ivt_sign_bracket_degree_four_kernel_checked` (its degree-3 sibling has one).
3. `Rat.polyEval_mul`, as the three-term identity its own module doc argues for.
   It is the shared prerequisite for the largest part of the backlog.
