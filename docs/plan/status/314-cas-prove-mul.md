# Lane: cas-prove-mul — polynomial × polynomial cofactors for the CAS→kernel geometry bridge

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (prove_mul landed with one reconstructed
certificate; kernel-reconstructed 8 → 9; the "8 more geometry certificates"
sizing is CORRECTED to 3 — five of the eight also need the fractional literal
cast, including the one lane 277 named as cheapest)`, cas-prove-mul,
2026-08-29).**

## Step 0: re-measured before building on it

`python3 scripts/validate-facts.py` at lane start:

    2154 facts checked, 0 errors
    cas-certificate: 36 total -- kernel-reconstructed 8, cas-internal 28

Unchanged from `docs/plan/status/277-cas-multivariate.md`. That lane's arity
survey re-verified against `artifacts/geometry-certificates/` and reproduces
exactly (arities 6–19; `varignon` and `thales` vacuous).

`scripts/brief-step0.py` was not run against a kernel-declaration target: this
lane declares no library lemma. Its subject is one `Check.*` theorem built
inside a `#[cfg(test)]` module, which no environment projection carries, and the
Rust helpers it needed (`prove_merge`, `poly_expr`, `int_poly`) were located by
reading the sibling module directly rather than by name search. The
retrieval-hazard rule still applied and paid: **nine helpers were reused from
`cas_geometry_bridge_tests.rs` by widening them to `pub(super)`, not
re-derived** — including `prove_merge`, which `prove_mul` calls at every
insertion point and which would have been the single largest piece of
duplicated work.

## The correction: `prove_mul` unblocks THREE certificates, not eight

Lane 277 sized "geometry, non-constant cofactors" at **8**, and separately
listed `medians-concurrent` as the one blocked on a fractional-literal cast.
Measured per certificate — counting terms whose serialised `coefficient`
denominator is not `1` — the two blockers **overlap on three of the eight**:

| certificate | terms | non-integer coeffs | max cofactor terms | non-constant cofactors | blocked on |
| --- | --- | --- | --- | --- | --- |
| orthocentre-altitudes-concurrent | 26 | 0 | 1 | 0 | (landed by lane 277) |
| thales-right-angle-in-semicircle | 17 | 0 | 1 | 0 | vacuous identity (`refl`) |
| varignon-midpoint-parallelogram | 0 | 0 | 0 | 0 | vacuous identity (`0 = 0`) |
| medians-concurrent | 32 | **24** | 1 | 0 | fractional cast only |
| **rhombus-diagonals-perpendicular** | **79** | **0** | **12** | **4** | **`prove_mul` only — THIS LANE** |
| pappus-hexagon | 145 | 0 | 10 | 9 | `prove_mul` only |
| simson-line | 2010 | 0 | 324 | 10 | `prove_mul` only |
| parallelogram-diagonals-bisect | 53 | **24** | 4 | 6 | `prove_mul` **and** fractional cast |
| centroid-divides-medians | 61 | **16** | 4 | 6 | `prove_mul` **and** fractional cast |
| euler-line | 337 | **272** | 74 | 5 | `prove_mul` **and** fractional cast |

So `prove_mul` alone reaches **three**. And **`parallelogram-diagonals-bisect`
— the certificate lane 277 named as the cheapest next target on term count — is
not one of them**: every one of its cofactors and both of its conclusions carry
`±1/2`. Sizing the next lane at "parallelogram, ~47 terms, cheapest" would have
sent it into the fractional-cast wall with a `prove_mul` brief.

The cheapest certificate `prove_mul` actually reaches is
**`rhombus-diagonals-perpendicular`**, and this lane reconstructed it.

## `prove_mul`'s design

`crates/axeyum-lean-kernel/src/rat_prelude/cas_geometry_mul_bridge_tests.rs`
(new, 5 tests). The parent module stays untouched apart from nine `pub(super)`
widenings.

**The problem.** Lane 277's tractability argument is that every monomial goes
through one builder, so two equal monomials are the same `ExprId` and the
cofactor identity is *linear* over an ordered basis of opaque atoms. A
polynomial cofactor breaks that: the product of two monomials must be rebuilt
in canonical variable order, which is exactly the `mul_comm`/`mul_assoc`
reasoning the constant case never needed.

**The move that keeps it cheap: represent a monomial as a sorted LIST OF
VARIABLE OCCURRENCES rather than as an exponent map.** Then monomial ×
monomial is the *same sorted merge* the addition already uses, and the
structure of `prove_merge` transfers wholesale. Three layers:

- **`prove_mono_mul`** — `prod(u) · prod(v) = prod(merge(u, v))` on two
  ascending factor lists. Six cases and **two of them are free**: when the left
  head wins and its tail is empty, the two sides are literally the same
  `ExprId` (`rrefl`); the mirrored case is a single `mul_comm`. The recursive
  cases are one `mul_assoc` and one derived `mul_left_comm` respectively. (The
  two singleton cases exist only because a monomial is `ax * (bx * cy)` rather
  than `ax * (bx * (cy * 1))` — the parent module's `mono_expr` does not
  terminate its product in `Rat.one`, which keeps the declared statement
  readable at the cost of those branches.)
- **`prove_head_product`** — `(c₁m₁)·(c₂m₂) = (c₁c₂)·(m₁m₂)`: `mul_assoc`,
  `mul_left_comm`, `mul_assoc`, `Rat.ofInt_mul` reversed, then `prove_mono_mul`
  under `ofInt(c₁c₂) * _`, then one defeq ascription re-normalising the
  `Int.mul` node to the canonical literal (same device as `prove_scale`).
- **`prove_term_mul` / `prove_poly_mul`** — `left_distrib` over the right
  factor, `right_distrib` over the left, with every product term re-inserted
  through the parent module's `prove_merge`.

**The re-insertion is load-bearing, not an optimisation.** Multiplying by a
fixed monomial is **not** order-preserving under the monomial order: with
`m = x`, `x < y` as monomials but `x·y < x·x`, so the image of a sorted term
list is not sorted. It is also what makes cancellation free — `(x−y)(x+y)`
needs the two `xy` terms to vanish, and `prove_merge`'s existing zero-drop path
does it with no special case.

`Rat.one_mul` and `Rat.zero_mul` **do not exist in this prelude**; both are
derived here from `mul_comm` plus `mul_one`/`mul_zero`.
<!-- absent: Rat.one_mul, Rat.zero_mul -->

**Three of my first drafts had a rewrite backwards**, and the fix was to
recover each direction from the parent module's own call sites rather than
assume it:

    add_assoc x y z     : (x+y)+z = x+(y+z)
    mul_assoc x y z     : (x*y)*z = x*(y*z)
    left_distrib x y z  : x*(y+z) = x*y + x*z
    right_distrib x y z : (x+y)*z = x*z + y*z

so `mul_assoc` runs `start → mid` in `prove_mono_mul` and needs **no** `rsymm`,
while the coefficient-pairing step in `prove_head_product` does. The tell for
each was reading which side of an existing `rsymm(a, b, h)` the lemma sat on.

## What was reconstructed, and what it does NOT establish

`Check.geometry_rhombus_cofactor_identity`, admitted through
`Kernel::add_declaration`: nine universally quantified `Rat` variables (eight
coordinates plus the saturation variable `Zinv0`), four generators, cofactors
of 12/8/6/8 terms. `Declaration::Theorem`, `axiom_footprint` empty. Registered
as `F:geometry-rhombus-cofactor-identity-kernel-checked`.

    cas-certificate: 37 total -- kernel-reconstructed 9, cas-internal 28

**The 28 does not shrink**, for the same reason it did not for lanes
cas-row-three and cas-multivariate: this is a new kernel-reconstructed
*sibling*, not a relabelling of the parent. Nothing was relabelled and no
checker weakened.

Five things it does not establish, each in the fact's `axiom_footprint`:

1. **It does not prove the geometry.** The kernel sees nine `Rat` variables and
   one algebraic identity. That `ax` is a point's abscissa, that the four
   generators are "AB ∥ DC", "BC ∥ AD", "|AB| = |BC|" and the non-degeneracy
   saturation, and that the conclusion is "AC ⟂ BD", are modelling choices made
   in `axeyum_cas::geometry_corpus` and reproduced by the translator.
   Reconstruction **relocates** that assumption into a kernel definition choice;
   it does not discharge it.
2. **It does not establish the geometric conditional.** The theorem is the
   identity `f = Σ hᵢgᵢ`. The implication `(∀i. gᵢ = 0) → f = 0` is one `Rat`
   rewrite away and is not taken.
3. **Non-degeneracy is now IN the statement as an uninterpreted variable — and
   this is WORSE than for the orthocentre sibling, which had no saturation at
   all.** `generators[3]` is `Zinv0 · (ABD collinearity determinant) − 1`, and
   `Zinv0` is one more universally quantified `Rat` with no interpretation
   whatever. The reading that `Zinv0` *witnesses* invertibility of that
   determinant — and hence that the identity is silent rather than false on
   degenerate configurations — lives entirely outside what is proved. The
   certificate's own `statement` field records that the geometric claim is
   **false** without the condition (four collinear points with `|AB| = |BC|`
   satisfy every hypothesis and have *parallel* diagonals); the kernel term
   knows nothing of that.
4. **It is over `Rat`, not `CReal`.** A rational-coefficient identity holds in
   every ℚ-algebra.
5. **`prove_mul` lifts the constant-cofactor restriction, not the integer one.**
   The translator still declines any non-integer coefficient.

## Mutation results — both halves, and they die through DIFFERENT guards

Run in this lane's own worktree, never the shared checkout. Each killed the two
kernel-checked tests and left the three non-kernel tests green:

- **Statement.** `prove_head_product`'s coefficient `a.1 * b.1` →
  `a.1 * b.1 + 1`. Dies at the `merged == conclusion` assertion, printing a
  **105-term** wrong normal form against the certificate's 8-term conclusion.
  So the statement the kernel is asked to admit is pinned to the
  **certificate's** conclusion, not to whatever the emitter produced.
- **Kernel gate.** The single `mul_comm` in `prove_mono_mul`'s right-head
  singleton branch, arguments swapped (same lemma, same arity, wrong
  direction). The statement assertion **passes** — the normal form is
  unchanged, only the proof is wrong — and `add_declaration` refuses with
  `TypeMismatch`, in bounded time.

That the two die through *different* guards is the discrimination that matters:
(a) alone would not show the proof is genuinely re-derived, and (b) alone would
not show the statement is pinned to the certificate.

## Cost, measured

Debug, on this host, through `scripts/cargo-serialized.sh`:

| run | wall clock |
| --- | --- |
| `rat_prelude::cas_geometry` (both modules, 8 tests) | 135–141 s |
| `geometry_rhombus_cofactor_identity_kernel_checked` alone | 152.79 s |
| `rhombus_certificate_identity_holds_at_integer_points` alone (no kernel work) | 120.04 s |
| `prove_mul_difference_of_squares_kernel_checked` alone (no certificate) | 7.66 s |

**About 120 s of the 153 is `axeyum_cas::geometry_certify::certify`, not the
kernel.** The translator test does no kernel work at all and still costs
120.04 s, which is what isolates it. The kernel side is ~33 s for 79 terms
across four polynomial products — so the *proving* is cheap and the
*certificate production* is what dominates at this size. Anyone sizing the next
certificate should measure `certify` first.

## What the remaining ones need

| what | count | needs |
| --- | --- | --- |
| `pappus-hexagon` | 1 | **nothing new.** All-integer, cofactors ≤10 terms, 9 generators, 19 variables. `prove_mul` reaches it as written. The open question is cost: ~450 term-products against rhombus's ~264, so expect 2–3× the kernel time, and `certify` on 19 variables is the part to measure first. This is the obvious next lane. |
| `simson-line` | 1 | `prove_mul` reaches it in principle and **should not be attempted until pappus is measured.** 2010 terms, a 324-term cofactor, 17 variables. The insertion-merge is O(n²) in the product's term count, so this is two orders of magnitude past rhombus on the wrong axis. If it matters, the fix is a linear multi-way merge over all product terms at once rather than repeated singleton insertion — a real change to `prove_term_mul`, not a tuning knob. |
| `parallelogram-diagonals-bisect`, `centroid-divides-medians`, `euler-line` | 3 | **the fractional-literal cast, on top of `prove_mul`.** A `Rat.ofRat`-style builder for a `num/den` literal, plus the arithmetic on `Fraction` coefficients in the translator. Doing that once also unblocks `medians-concurrent` (constant cofactors, `±1/2` only) and `F:cas-partial-fractions-mixed-general-case` — **four facts in three clusters for one build, which makes it the highest-leverage next piece, ahead of pappus.** `euler-line` additionally has 74-term cofactors, so treat it as a `simson`-class cost question rather than a cast question. |
| `medians-concurrent` | 1 | fractional cast only; `prove_scale`/`prove_merge` already suffice for its constant cofactors. |
| `thales`, `varignon` | 2 | nothing worth doing on this route. The certificate identity is `refl` and `0 = 0` respectively. If they are to be reconstructed at all, the honest target is the *normalisation* step, which the certificate does not carry. |
| WZ | 9 | `prove_mul` is a prerequisite and now exists, but it is **not** the whole obligation — see lane 277's write-up: the Gamma-to-factorial modelling step, the boundary-term argument over `k`, and the induction on `n` are all outside the polynomial identity. Sizing WZ at "one dependency away" would overstate it in the same direction the design review warns about for geometry. |
| gf2 | 4 | GF(2) polynomial arithmetic; nothing modular or characteristic-2 exists in `rat_prelude`/`int_prelude`. Untouched. |
| real-algebraic | 4 | unchanged: root containment and Sturm counts need `Rat` polynomial division and a Sturm chain in the kernel. |

## Gates run (all foreground)

- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib rat_prelude::cas_geometry` — **8 passed, 0 failed**, 141.21 s (nonzero count confirmed)
- Both `checker_command`s re-run standalone through GNU `/usr/bin/grep -cE` (explicitly, not the interactive ugrep) — each prints `1`, exit 0
- `cargo fmt --all --check` — clean
- `scripts/cargo-serialized.sh clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — clean (one `useless_vec` found and fixed)
- `python3 scripts/validate-facts.py` — 2155 facts, **0 errors**
- `python3 scripts/check-mirror-statement-fidelity.py` — `violations=0 verdict=PASS`

Not run: the aggregate gate, per the brief.

## Did NOT touch

`crates/axeyum-lean-kernel/src/nat_prelude/`, `int_prelude/`, `creal/`, and
`axeyum-cas` itself (read-only — the translator only reads existing public
certificate fields). The parent `cas_geometry_bridge_tests.rs` changed only by
widening nine items to `pub(super)`; no logic edited, no existing fact
relabelled, no checker weakened. Nothing pushed.

<!-- plan-section: landed-changes -->

| 2026-08-29 | `203712454` | step 0 re-measurement: the "8 more geometry certificates" sizing corrected to 3; `parallelogram-diagonals-bisect` needs the fractional cast too |
| 2026-08-29 | `e253e79cd` | `rat_prelude/cas_geometry_mul_bridge_tests.rs` — `prove_mul`: monomials as sorted factor lists, three layers, `one_mul`/`zero_mul` derived |
| 2026-08-29 | `f24f87fa9` | `Check.geometry_rhombus_cofactor_identity` admitted — 9 variables, 4 polynomial cofactors, axiom-free; rewrite directions recovered from the parent module's call sites |
| 2026-08-29 | `4b9d63e9e` | `F:geometry-rhombus-cofactor-identity-kernel-checked` registered; cas-certificate kernel-reconstructed 8 → 9; mutation-verified both halves |
