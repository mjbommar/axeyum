# Lane: cas-fractional-cast — the general `Rat.ofRat`-style fractional-literal cast, plus medians-concurrent

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (fractional cast landed; kernel-reconstructed 9 →
10; medians-concurrent reconstructed; centroid-divides-medians and
parallelogram-diagonals-bisect still need prove_mul ON TOP of this cast;
F:cas-partial-fractions-mixed-general-case untouched -- cast-only, next
lane's cheapest target)`, cas-fractional-cast, 2026-08-30).**

## Step 0: re-verified before building

`python3 scripts/validate-facts.py` at lane start:

    cas-certificate: 37 total -- kernel-reconstructed 9, cas-internal 28

Matches `docs/plan/status/314-cas-prove-mul.md` exactly. Re-verified that
lane's specific correction before starting: `parallelogram-diagonals-bisect`
(lane 277's originally-named "cheapest next target") is genuinely NOT
reachable by the fractional cast alone — every one of its cofactors and both
of its conclusions carry `±1/2`, which is a NON-CONSTANT-cofactor shape
needing `prove_mul` as well. `medians-concurrent` is the one certificate
whose cofactors are constant (`-1`, `-1`) and whose generators are the ones
needing the cast, so it is reachable by the cast alone — confirmed by reading
`artifacts/geometry-certificates/medians-concurrent.json` directly before
writing any Rust.

`scripts/brief-step0.py` was not run against a kernel-declaration target, for
the same reason lane cas-prove-mul's did not: this lane declares no library
lemma, only a `Check.*` theorem inside a `#[cfg(test)]` module.

## What landed

`crates/axeyum-lean-kernel/src/rat_prelude/cas_geometry_frac_bridge_tests.rs`
(new, 3 tests). Two existing helpers widened to `pub(super)` for reuse
(`nat_le_lit` in `cas_ivt_bridge_tests.rs`, `add_left_comm` in
`cas_geometry_bridge_tests.rs`); no existing logic changed.

### The cast

`Rat.normalize n d h` (`rat_prelude/ops.rs`) already existed — it takes an
`Int` numerator, a `Nat` denominator, and a proof `1 <= d`, and reduces to
lowest terms internally. That IS a `Rat.ofRat`-style cast; nothing needed
declaring in the kernel. `rat_lit(d, r: Rational) -> ExprId` is the one-line
builder this bridge lacked:

    Rat.normalize (int_lit r.numerator()) (nat_lit r.denominator())
                  (nat_le_lit 1 r.denominator())

using `axeyum_ir::Rational`'s own canonical (numerator, denominator) pair —
the same `Rational` type `axeyum_cas`'s `MvPoly` already stores coefficients
in, so the translator (`rat_poly`) is total: unlike `int_poly`, it never
declines.

### Why the proof machinery needed LESS new content than expected

`int_prelude_tests.rs` already carries `rat_normalize_reduces_two_quarters_
to_one_half`, `rat_mul_renormalises_two_thirds_times_three_halves_to_one`,
and `rat_add_renormalises_and_neg_is_an_involution` — each demonstrating, in
that suite's own words, that `Rat.add`/`Rat.mul`/`Rat.normalize` fully
renormalise CONCRETE literals through `def_eq` alone, "no lemma needed".
Every coefficient this module ever combines is such a literal (built by
`rat_lit` from a certificate's own `Rational`), so `prove_scale_rat`/
`prove_merge_rat` need exactly one FEWER step than their integer-coefficient
predecessors (`prove_scale`/`prove_merge` in `cas_geometry_bridge_tests.rs`):
the `Rat.ofInt_mul`/`Rat.ofInt_add`-then-`Eq.refl` collapse becomes a SINGLE
`Eq.refl` ascription straight to the canonical `rat_lit(k*c)` / `rat_lit(ca+cb)`,
with the kernel's own `Rat.mul`/`Rat.add` computation checking it directly —
this was verified empirically (both `prove_scale_rat`'s coefficient-collapse
step and `prove_merge_rat`'s zero-drop route, which the medians identity
exercises twice, type-checked on the first attempt).

The zero-drop case (`ax*by` and `ay*bx` cancel between `-g0` and `-g1`) is
the SAME `mul_comm`/`mul_zero`/`zero_add` route the int-case uses, unchanged
in shape — the only new burden on `def_eq` is that the cancelling sum now
renormalises through a genuine `Rat.add` of two fractions rather than an
`Int.add` of two literals, and the same precedent covers it.

### What was reconstructed, and what it does NOT establish

`Check.geometry_medians_cofactor_identity`: eight universally quantified
`Rat` variables, two constant cofactors (`-1`, `-1`), two 10-term generators
(8 of 10 terms in each carry a genuine `±1/2`), one 10-term conclusion.
`Declaration::Theorem`, `axiom_footprint` empty. Registered as
`F:geometry-medians-cofactor-identity-kernel-checked`.

    cas-certificate: 38 total -- kernel-reconstructed 10, cas-internal 28

Six things it does NOT establish, each in the fact's `axiom_footprint` (the
sixth is new relative to the orthocentre/rhombus siblings): the fractional
cast itself is untested at denominators larger than 2, and nothing here
measures whether the `def_eq` renormalisation stays cheap at the larger
denominators `euler-line`'s cofactors would need — a cross-multiplied
denominator product is exactly the kind of magnitude CLAUDE.md's
numeral-magnitude gotcha warns is superlinear-cost under this kernel's unary
`Nat` arithmetic.

## Mutation results — both halves, different guards

Run in this lane's own worktree. Each killed only the target test, leaving
the other two `cas_geometry_frac_bridge_tests` green:

- **Statement.** `prove_merge_rat`'s combined coefficient: `a_head.1 +
  b_head.1` → `a_head.1 + b_head.1 + Rational::integer(1)`. Dies at the
  `merged == concl_for_build` Rust-level assertion, printing an 11-term wrong
  normal form against the certificate's 10-term conclusion — the statement
  the kernel is asked to admit is pinned to the certificate's conclusion, not
  to whatever the emitter produced.
- **Kernel gate.** The zero-drop path's closing lemma: `p.zero_add` →
  `p.add_zero` (same arity and argument, wrong side of the sum). The
  statement assertion still PASSES (the normal form is unchanged, only the
  proof direction is wrong), and `add_declaration` refuses with
  `TypeMismatch`.

That the two die through different guards is the discrimination that
matters: (a) alone would not show the proof is genuinely re-derived, and (b)
alone would not show the statement is pinned to the certificate.

## Cost, measured

Debug, this host, uncontended, through `scripts/cargo-serialized.sh`:

| run | wall clock |
| --- | --- |
| `translator_reads_the_medians_certificate_the_cas_produced` | 0.11s |
| `rat_poly_arithmetic_drops_cancelling_monomials` | 0.10s |
| `geometry_medians_cofactor_identity_kernel_checked` alone | 8.14s |
| full `rat_prelude::cas_geometry` sweep (all 11 tests, 3 modules) | 145.26s |

Far cheaper than the rhombus sibling's 152.79s for its single kernel-checked
test: medians-concurrent's cofactors are constant (no `prove_mul` /
polynomial-times-polynomial needed at all) and its 10-term polynomials are a
fraction of rhombus's 79-term ones. The `certify` call itself was not
measured in isolation here — it was not the bottleneck at this size (the
whole reconstruction, including certify, is 8.14s), so isolating it was not
worth the extra test lane cas-prove-mul's handoff already asked for at
larger sizes.

## What the remaining fractional-cast-needing facts need

| what | needs |
| --- | --- |
| `F:cas-partial-fractions-mixed-general-case` | **the cast only** — untouched by this lane. Per the brief's explicit scope ("landing the cast plus one reconstruction is a full result... don't batch-convert"), this is the next lane's cheapest target: `rat_lit` is ready to use as-is. |
| `centroid-divides-medians` | cast (now landed) **and** `prove_mul` (already landed, lane cas-prove-mul) — 16 non-integer terms, max cofactor 4 terms, 6 non-constant cofactors. Both pieces exist; nobody has yet combined them for this certificate. |
| `parallelogram-diagonals-bisect` | same as centroid — cast **and** `prove_mul`, both landed, not yet combined. 24 non-integer terms, max cofactor 4 terms, 6 non-constant cofactors. |
| `euler-line` | cast **and** `prove_mul`, **and** a simson-class term-count cost question: 272 non-integer terms, 74-term max cofactor, 337 total terms. Should not be attempted until a `prove_mul`+cast combination is measured on the two smaller ones above first. |

The natural next step for a lane combining cast and `prove_mul` is a small
generalisation this lane did NOT need: `prove_scale_rat`/`prove_merge_rat`
handle constant×polynomial and polynomial+polynomial over `Rational`
coefficients, but a NON-CONSTANT rational-coefficient cofactor needs the
`prove_mono_mul`/`prove_head_product`/`prove_term_mul`/`prove_poly_mul`
family from `cas_geometry_mul_bridge_tests.rs` generalised the same way this
lane generalised `prove_scale`/`prove_merge` — i.e. a `RatTerm`-typed
`prove_head_product_rat` replacing its `Rat.ofInt_mul`-then-`Eq.refl` step
with a single `Eq.refl` ascription to `rat_lit(product)`, mirroring exactly
what this lane did for the additive side.

## Gates run (all foreground)

- `cargo check -p axeyum-lean-kernel --lib --tests` — clean
- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib
  cas_geometry_frac_bridge_tests` — **3 passed, 0 failed** (nonzero count
  confirmed), and again as part of the 11-test `rat_prelude::cas_geometry`
  sweep (all three sibling modules together) — **11 passed, 0 failed**
- Both `checker_command`s re-run standalone through `/usr/bin/grep -cE`
  explicitly (not the interactive `ugrep`) — each prints `1`, exit 0
- `rustfmt --edition 2024 --check` on all four touched files — clean
- `scripts/cargo-serialized.sh clippy -p axeyum-lean-kernel --all-targets --
  -D warnings` — clean
- `python3 scripts/validate-facts.py` — **2156 facts, 0 errors**;
  `cas-certificate: 38 total -- kernel-reconstructed 10, cas-internal 28`
- `python3 scripts/check-mirror-statement-fidelity.py` —
  `violations=0 verdict=PASS`

Not run: the aggregate gate (`just check`/`check.sh`), per the brief.

## Did NOT touch

`crates/axeyum-lean-kernel/src/nat_prelude/`, `int_prelude/`, `creal/`, and
`axeyum-cas` itself (read-only — the translator only reads existing public
certificate fields). The parent `cas_geometry_bridge_tests.rs` and
`cas_ivt_bridge_tests.rs` changed only by widening two items each to
`pub(super)`; no logic edited, no existing fact relabelled, no checker
weakened. Nothing pushed.

<!-- plan-section: landed-changes -->

| 2026-08-30 | `370a51a64` | draft: `rat_prelude/cas_geometry_frac_bridge_tests.rs` -- `rat_lit` cast, `prove_scale_rat`/`prove_merge_rat`/`prove_const_combination_rat`, medians-concurrent reconstruction (compiles, not yet test-run in that commit) |
| 2026-08-30 | (pending) | tests green (11/11 sweep), mutation-verified both halves through different guards; `F:geometry-medians-cofactor-identity-kernel-checked` registered, `cas-certificate` kernel-reconstructed 9 -> 10 |
