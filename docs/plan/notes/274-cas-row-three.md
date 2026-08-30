# Notes: 274-cas-row-three

Detail moved out of [`../status/274-cas-row-three.md`](../status/274-cas-row-three.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

| cluster | count | facts |
| --- | --- | --- |
| WZ (Zeilberger/Gosper binomial identities) | 9 | `alternating-binomial-row-sum-zero`, `apery-numbers-recurrence`, `binomial-row-sum-two-power`, `chu-vandermonde-convolution`, `chu-vandermonde-convolution-recurrence`, `cross-binomial-row-sum`, `franel-numbers-recurrence`, `squared-binomial-row-sum-central`, `weighted-binomial-row-sum` |
| NRA geometry (Nullstellensatz cofactor certificates) | 10 | `geometry-centroid-divides-medians`, `geometry-euler-line`, `geometry-medians-concurrent`, `geometry-orthocentre-altitudes-concurrent`, `geometry-pappus-hexagon`, `geometry-parallelogram-diagonals-bisect`, `geometry-rhombus-diagonals-perpendicular`, `geometry-simson-line`, `geometry-thales-right-angle-in-semicircle`, `geometry-varignon-midpoint-parallelogram` |
| real-algebraic (IVT/EVT/MVT/Taylor Sturm-backed certificates) | 4 | `cas-extremum-irrational-argmax`, `cas-ivt-cbrt2-in-1-2`, `cas-mvt-cubic-witness-sqrt3`, `cas-taylor-quartic-lagrange-witness` |
| partial fractions | 1 | `cas-partial-fractions-mixed-general-case` |
| gf2 (GF(2) polynomial composition) | 4 | `gf2-composition-shape-classification`, `gf2-degree-eight-octuple-two-step-chain`, `gf2-general-monomial-composition-criterion`, `gf2-witt-shifted-degree-seven-closed-form` |

9+10+4+1+4 = 28, exact match to the design review's count. **The breakdown
was accurate and nothing had shifted in the day since it was measured.**

## What landed: 3 new sibling facts, kernel-reconstructed 4 → 7

All three follow the SAME pattern the existing 4 kernel-reconstructed facts
established: a NEW sibling fact naming a strictly WEAKER sub-claim than the
full Sturm-backed certificate, admitted through `Kernel::add_declaration`
over `Rat.polyEval`, reusing `rat_prelude::cas_ivt_bridge_tests`'s shared
engine (`poly_eval_to_of_int`, `n_term_polynomial`, `int_lit`, `of_int`,
`rational_to_int`) verbatim rather than re-deriving it. **No existing fact
was relabeled and no checker was weakened.**

1. **`F:cas-extremum-deriv-sign-bracket-kernel-checked`** (commit `a94927553`)
   — for `p(x)=x^3-6x` on `[-3,2]` (`F:cas-extremum-irrational-argmax`'s own
   instance), the derivative `p'=3x^2-6` (`cert.deriv` itself, not
   hand-differentiated) satisfies `p'(-2)=6>0` and `p'(-1)=-3<0`. This is a
   DIFFERENT, EARLIER step than the already-existing
   `F:cas-evt-endpoint-exclusion-cubic-kernel-checked` sibling (which shows
   the interior point beats both endpoints). Does NOT establish: the IVT
   implication itself (sign change ⇒ a root exists — not admitted through
   this kernel, only the two inequalities), differentiation as a general
   kernel operation, Sturm completeness of `critical_points`, or that the
   resulting root is `-sqrt(2)`/irrational.

2. **`F:cas-mvt-secant-endpoints-kernel-checked`** (commit `d57773ad2`) — for
   `p(x)=x^3` on `[0,3]` (`F:cas-mvt-cubic-witness-sqrt3`'s own instance),
   `p(3)=27` and `p(0)=0` (`cert.poly`/`a`/`b` themselves), reconstructed as
   `Eq` conclusions (no `Lt`-specific closing lemma needed — `Eq` falls
   straight out of `poly_eval_to_of_int`). Does NOT establish: the slope
   division `(27-0)/(3-0)=9` itself, Rolle's theorem, the Rolle reduction
   `g(x)=p(x)-p(0)-9x`, or the witness `c=sqrt(3)`/its Sturm-isolated
   bracket. First reconstruction touching the MVT cluster.

3. **`F:cas-taylor-remainder-lhs-kernel-checked`** (commit `af6d9f1e6`) — for
   `p(x)=x^4` at `a=0,n=1,b=2` (`F:cas-taylor-quartic-lagrange-witness`'s own
   instance), `p(2)=16` and `T_1(2)=0` (`T_1` is the CAS's own
   `cert.taylor_poly`, which trims to the empty/zero polynomial for this
   instance since `p'(0)=0`). The `T_1(2)=0` sub-claim is trivial by
   construction and the fact's own `axiom_footprint` says so plainly — it is
   included only for uniformity with the `p(2)=16` row, not because it was
   in doubt. Does NOT establish: the remainder subtraction `16-0=16` itself,
   the generalized-Rolle argument, `p''=12x^2`, the Lagrange identity, or the
   witness `xi=sqrt(2/3)`/its Sturm-isolated bracket. Also unrelated to
   `rat_prelude::taylor`'s `Rat.taylor_deg1` (already flagged elsewhere as
   materially weaker — degree ≤ 1 only, no remainder, no witness).

Together these three touch **three of the four real-algebraic-cluster
facts** (extremum, MVT, Taylor). The fourth, `F:cas-ivt-cbrt2-in-1-2`,
already had a sign-bracket sibling (`F:cas-ivt-sign-bracket-cbrt2-kernel-
checked`) predating this lane; its remaining unclaimed parts (root
containment and the Sturm count) need genuinely new kernel machinery — see
below.

**Final measurement:** `cas-certificate: 35 total -- kernel-reconstructed 7,
cas-internal 28` (`python3 scripts/validate-facts.py`, 0 errors, run after
each of the three commits).

## No unregistered already-passing bridges existed (checked first, per the brief)

Before writing any new code, I enumerated every `#[test]` in the three
existing bridge files (`rat_prelude/cas_ivt_bridge_tests.rs`,
`rat_prelude/cas_evt_bridge_tests.rs`, `complex/cas_bridge_tests.rs`): 2, 1,
and 1 tests respectively, and **all four were already registered** as the
existing 4 kernel-reconstructed facts. There was no cheap "just register"
win available this time — unlike the design review's own finding for the
PRIOR lane, where 2 of the first 3 kernel-reconstructed facts were exactly
this. All three of this lane's facts are genuinely new bridge code.

## Two clusters checked and found genuinely hard, not cheaply reachable

- **Partial fractions (1 fact).** Hand-solved the `mixed_general_case`
  certificate's linear system (`p=x+1`, `q=(x-1)^2(x^2+1)`): the
  undetermined coefficients are `A=-1/2, B=1, C=1/2, D=-1/2` — **three of
  four are non-integer rationals**. The existing bridge translator
  (`rational_to_int`) declines on any non-integer value by design; there is
  no `Rat.ofRat`-style general-rational-literal cast in the kernel bridge
  layer today (the fact's own `axiom_footprint` already flags this as
  needed, and I confirmed it by hand rather than trusting the note). This
  needs new infrastructure — a general fractional-literal builder — before
  any part of this certificate can be kernel-reconstructed at all.

- **Geometry (10) and WZ (9), 19 facts total.** Both need MULTIVARIATE
  polynomial identity checking in the kernel (coordinates of points for
  geometry; `n`/`k` indices for WZ's rational-function certificates). Every
  existing bridge (`cas_ivt_bridge_tests`, `cas_evt_bridge_tests`,
  `cas_mvt_secant_bridge_tests`, `cas_taylor_remainder_bridge_tests`,
  `complex/cas_bridge_tests`) is explicitly univariate-only by design (see
  `complex/cas_bridge_tests.rs`'s own module doc). Building general
  multivariate polynomial evaluation over the kernel is a materially larger
  task than any of the three facts this lane landed, and — per the design
  review's own qualification, which I re-confirm rather than merely
  cite — reconstructing the polynomial identity `Σhᵢgᵢ=f` would NOT by
  itself establish that those polynomials mean the geometric predicates
  they are named after (the coordinatisation is a separate modelling
  assumption that reconstruction only RELOCATES into a kernel definition
  choice, never discharges). So even a future 31-of-31 on this route would
  not mean full geometric/combinatorial validity — sizing this honestly
  matters more than reaching it quickly.

  **gf2 (4 facts)** is a third, separate hard case: it needs GF(2)
  polynomial-ring arithmetic in the kernel, which does not exist in any
  form today (no modular/characteristic-2 construction anywhere in
  `rat_prelude`/`int_prelude`). Not attempted.

## Gates run (all foreground, all confirmed nonzero where applicable)

- `env -u RUST_MIN_STACK scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib rat_prelude::cas` — 6 passed, 0 failed (all bridge tests together, run after each commit)
- Each new test's exact `checker_command` re-run standalone and piped through the same `grep -cE` the fact JSON uses, confirmed to print `1`
- `cargo fmt --all --check` on the changed files (via `rustfmt --edition 2024 <file>`, per the multi-agent rule against workspace-wide `cargo fmt`)
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — clean after fixing two `doc_markdown` "backticks are unbalanced" errors from inline code spans split across `//!` line breaks
- `python3 scripts/validate-facts.py` — 0 errors, run after each of the three commits (32→33→34→35 total, 4→5→6→7 kernel-reconstructed)

## Did NOT touch

`crates/axeyum-lean-kernel/src/nat_prelude/` and `creal/` (per the brief —
other lanes were there); no existing fact was relabeled; no checker was
weakened; `axeyum-cas` itself was read-only (no changes needed — every
translator only reads existing public certificate fields).
