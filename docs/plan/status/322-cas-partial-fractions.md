# Lane: cas-partial-fractions — the univariate partial-fraction bridge, and correcting a stale sizing

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (kernel-reconstructed 10 -> 11; the "cast only"
sizing in docs/plan/status/317-cas-fractional-cast.md was WRONG for this
target -- see below; next cheapest cas-internal targets are
centroid-divides-medians / parallelogram-diagonals-bisect, cast+prove_mul,
both landed but not yet combined)`, cas-partial-fractions, 2026-08-30).**

## Step 0: verified the handoff rather than trusting it

`docs/plan/status/317-cas-fractional-cast.md` named
`F:cas-partial-fractions-mixed-general-case` "the cast only -- next lane's
cheapest target", in the same table as three `GeometryCertificate` facts
(`centroid-divides-medians`, `parallelogram-diagonals-bisect`, `euler-line`).

**That characterisation does not survive reading the fact.** Read directly:
`axeyum_cas::partial_fractions::PartialFractionCertificate` is a completely
different CAS module from `axeyum_cas::geometry_certify::GeometryCertificate`
-- no `cofactors`/`generators`/`conclusions` shape, no existing translator, and
(per the fact's own `notes` field, written 2026-08-27) "no kernel-side
partial-fraction route exists at all in this kernel." The "cast only" sizing
appears to have been carried over from the geometry facts in the same table
without checking that this one belongs to an unrelated module.

What was ACTUALLY needed, beyond the landed fractional cast:

1. A brand-new translator (`dense_to_rat_poly`) for this certificate's
   `Vec<Rational>`-dense, single-variable representation -- no
   `GeometryCertificate`-shaped translator applies to it.
2. A `Rational`-coefficient generalisation of
   `cas_geometry_mul_bridge_tests`'s `i128`-only polynomial x polynomial
   machinery (`prove_head_product`/`prove_term_mul`/`prove_poly_mul`/
   `prove_poly_combination`), because the quadratic factor's numerator
   (`Cx+D`) is genuinely non-constant -- the constant-cofactor-only
   `prove_scale_rat`/`prove_merge_rat`/`prove_const_combination_rat` the
   fractional-cast lane built cannot express that multiplication.

So this target needed the SAME two pieces `centroid-divides-medians` and
`parallelogram-diagonals-bisect` need (cast + `Rational` poly x poly), plus a
new translator neither of those needs, since they reuse the existing
`GeometryCertificate` translator. It was not the cheapest remaining target by
the measure 317 used (term count / existing infrastructure reuse); it happened
to still be small enough (a 4-degree denominator, a 2-term x 3-term product at
the largest) to land in one session anyway.

## What landed

`crates/axeyum-lean-kernel/src/rat_prelude/cas_partial_fractions_bridge_tests.rs`
(new, 4 tests). Widened five `i128`-coefficient-independent helpers in
`cas_geometry_mul_bridge_tests.rs` to `pub(super)` (`factors_expr`,
`rat_one_mul`, `rat_zero_mul`, `mul_left_comm`, `prove_mono_mul` -- none of
these touch a coefficient, only monomial factor lists, so they needed no
change to be reused verbatim) and three in `cas_geometry_frac_bridge_tests.rs`
(`add_poly_rat`, `term_expr_rat`, `poly_expr_rat`) for reuse. No existing logic
changed in either file (confirmed: the full 21-test `rat_prelude::cas_` sweep
stays green).

### The four new proof-emitting functions

`prove_head_product_rat` / `prove_term_mul_rat` / `prove_poly_mul_rat` /
`prove_poly_combination_rat` mirror `cas_geometry_mul_bridge_tests`'s `i128`
versions exactly in structure, with the same simplification the fractional-
cast lane already established for the additive side: where the `i128` case
needs an explicit `Rat.ofInt_mul` lemma plus an `Eq.refl` collapse,
`prove_head_product_rat` uses a SINGLE `Eq.refl` ascription straight to the
canonical `rat_lit(a.1 * b.1)`, relying on the kernel's own `Rat.mul`
computation on two literals (the same precedent `prove_scale_rat`/
`prove_merge_rat` already rely on).

### The concrete instance

`p(x) = x+1`, `q(x) = (x-1)^2(x^2+1)` -- exactly
`partial_fractions::tests::mixed_general_case`, produced by calling
`axeyum_cas::partial_fractions::partial_fractions` directly (not hand-copied).
Solving gives `A=-1/2, B=1, C=1/2, D=-1/2`. The kernel-checked statement:

```
forall x : Rat,
  x + 1 = (-1/2)*((x-1)*(x^2+1)) + 1*(x^2+1) + ((1/2)*x + (-1/2))*((x-1)*(x-1))
```

This is the checker's own `p = whole*q + leading*Sigma(numerator*cofactor)`
identity (`partial_fractions.rs:426`), specialised to this instance's `whole=0`
and `leading=1` (both asserted in the reconstruction, not assumed). None of
the checker's four structural guards (power-set, numerator-degree bound,
pairwise coprimality, q-reconstruction) are reconstructed -- only the
coefficient-matching identity. Full disclosure list in the fact's
`axiom_footprint` and the module doc.

Registered as `F:cas-partial-fractions-mixed-general-case-kernel-checked`, a
SIBLING fact (not an edit to the parent, per ADR-0601 SS2 and the geometry
cofactor-identity precedent -- folding this into the parent would make
`classify_cas_certificate_fact` label the whole certificate, including the
un-reconstructed structural guards, as kernel-reconstructed).

    cas-certificate: 39 total -- kernel-reconstructed 11, cas-internal 28

## Mutation results -- both halves, different guards

Applied by hand in this lane's own worktree, each reverted immediately after
confirming the failure mode, then re-confirmed green:

- **Statement guard.** `numerator_cofactor_pairs`'s `remaining_power = mult -
  term.power` -> `mult - term.power + 1` (an off-by-one in the cofactor
  exponent). Dies at BOTH the standalone
  `coefficient_matching_reconstruction_equals_p_exactly` test (a Rust-level
  `assert_eq!` against `cert.p`, printing a 6-term wrong reconstruction
  against the certificate's 2-term `p`) and the kernel test's own `merged ==
  p_for_build` assertion -- before `add_declaration` is ever called.
- **Kernel gate.** `prove_head_product_rat`'s `mul_assoc` argument order:
  `&[a_rat, a_mono, b_e]` -> `&[b_e, a_mono, a_rat]` (same arity, wrong
  instantiation). The Rust-side statement is UNCHANGED (the mutation touches
  only which `mul_assoc` instance is cited, not any Rust-computed value), so
  `merged == p_for_build` still passes -- and `add_declaration` rejects with
  `TypeMismatch { expected: ExprId(1959628), got: ExprId(1959639) }`.

The two die through different guards, confirming (a) the statement is pinned
to the certificate rather than to whatever the emitter produced, and (b) the
proof is genuinely re-derived by the trust anchor rather than restating a
Rust-side computation.

## Cost, measured

Debug, this host, through `scripts/cargo-serialized.sh`:

| run | wall clock |
| --- | --- |
| the 3 non-kernel tests (producer/translator/reconstruction checks) | well under 1s each |
| `cas_partial_fractions_mixed_general_case_kernel_checked` alone | 8.03s |
| this module's 4-test sweep | 7.87-10.1s |
| full `rat_prelude::cas_` sweep (21 tests, all bridge modules) | 134.71s |

Comparable to `medians-concurrent`'s 8.14s despite needing genuine poly x poly
multiplication (not just constant-scale), because both polynomials involved
stay small -- the largest product is a 2-term numerator times a 3-term
cofactor. No large numeral magnitude is formed anywhere in this construction
(the largest literal is a denominator of 2), so the unary-`Nat`-arithmetic
cost trap CLAUDE.md warns about does not apply here.

## Both checker_command directions verified

Verified standalone with `/usr/bin/grep -cE` explicitly (not the interactive
`ugrep`), both evidence rows:

- `kernel-reconstructed-partial-fractions-mixed-general-case-identity`:
  real test name -> count 1, exit 0; fabricated test name
  (`this_test_does_not_exist`) -> count 0, exit 1.
- `translator-and-reconstruction-checked-against-numbers`:
  real count string (`4 passed`) -> count 1, exit 0; fabricated count
  (`99 passed`) -> count 0, exit 1.

## What the remaining cas-internal facts need

Unchanged from 317's table, since this lane's target was a different module
entirely and did not touch the geometry certificates:

| what | needs |
| --- | --- |
| `centroid-divides-medians` | cast (landed) and `prove_mul` (landed), not yet combined -- 16 non-integer terms, max cofactor 4 terms, 6 non-constant cofactors |
| `parallelogram-diagonals-bisect` | same as centroid -- 24 non-integer terms, max cofactor 4 terms, 6 non-constant cofactors |
| `euler-line` | cast and `prove_mul`, plus a simson-class term-count cost question: 272 non-integer terms, 74-term max cofactor |

The natural next step for either of the first two: `prove_scale_rat`/
`prove_merge_rat`/`prove_const_combination_rat` handle constant cofactors over
`Rational`; a NON-CONSTANT rational-coefficient cofactor needs exactly the
`prove_mono_mul`(reused)/`prove_head_product_rat`/`prove_term_mul_rat`/
`prove_poly_mul_rat`/`prove_poly_combination_rat` family this lane just built
-- it is already `Rational`-coefficient-generic and does not need a further
generalisation, only a `GeometryCertificate`-shaped `(cofactor, generator)`
parts list instead of this lane's `(numerator, cofactor)` one.

## Gates run (all foreground)

- `cargo check -p axeyum-lean-kernel --lib --tests` -- clean
- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib
  cas_partial_fractions_bridge_tests` -- **4 passed, 0 failed** (nonzero count
  confirmed), and again as part of the 21-test `rat_prelude::cas_` sweep
  across every bridge module -- **21 passed, 0 failed**
- Both `checker_command`s re-run standalone through `/usr/bin/grep -cE`
  explicitly, BOTH directions (see above)
- `rustfmt --edition 2024 --check` on the new file, plus `cargo fmt --all
  --check` (workspace-wide, read-only) -- clean
- `scripts/cargo-serialized.sh clippy -p axeyum-lean-kernel --all-targets --
  -D warnings` -- clean (one `doc_markdown` unbalanced-backticks fix landed
  along the way)
- `python3 scripts/validate-facts.py` -- **2157 facts, 0 errors**;
  `cas-certificate: 39 total -- kernel-reconstructed 11, cas-internal 28`

Not run: the aggregate gate (`just check`/`check.sh`), per the brief.

## Did NOT touch

`crates/axeyum-lean-kernel/src/nat_prelude/`, `int_prelude/`, `creal/`, and
`axeyum-cas` itself (read-only -- the translator only reads existing public
certificate fields via `axeyum_cas::partial_fractions` and `axeyum_ir::poly`,
both already-public APIs). `F:cas-partial-fractions-mixed-general-case` itself
is unmodified, per the sibling-fact convention. Nothing pushed.

<!-- plan-section: landed-changes -->

| 2026-08-30 | `f781973b9` | draft: `rat_prelude/cas_partial_fractions_bridge_tests.rs` -- not yet compiled (committed within first 10 tool calls per lane protocol) |
| 2026-08-30 | `24c5e1eb7` | feat: kernel-reconstruct `F:cas-partial-fractions-mixed-general-case` (compiles, 4/4 tests green, both mutation guards verified) |
| 2026-08-30 | `d2a954587` | fix: clippy `doc_markdown` unbalanced backticks |
| 2026-08-30 | `f07c07346` | fact: register `F:cas-partial-fractions-mixed-general-case-kernel-checked`, `cas-certificate` kernel-reconstructed 10 -> 11 |
