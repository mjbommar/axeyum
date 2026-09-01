# ADR-1460: `mvt.rs` and `extremum.rs` audited clean for ADR-1435's open-interval defect, for a structural reason

Date: 2026-09-01
Status: Accepted
Lane: `mvt-extremum-interval-audit`

Index-summary: ADR-1435 fixed `real_algebraic::verify_ivt_certificate`'s
strictness at the upper bound of the classical open interval `(a, b)` and
flagged `mvt.rs`/`extremum.rs` (same `count_real_roots_in(...) == Some(1)`
idiom) as unaudited. Both are clean, and not by luck: neither compares an
`AlgebraicReal`'s own half-open `(lower, upper]` isolation bracket directly
against `a`/`b` (the pattern that bit `verify_ivt_certificate`).
`sturm::count_real_roots_in` is used in both only to re-confirm a candidate's
own bracket isolates exactly one root of its own minimal polynomial; the
actual boundary decision goes through `RealAlgebraic::compare_rational`
(exact bignum bisection, no floating point), which decides `==`/`<`/`>`
directly and has no half-open-vs-open shape mismatch to exploit.
`mvt.rs` targets the classical OPEN `(a, b)` (its own module doc) and has one
explicit, intentional strict-interiority check (step 5) doing the work,
confirmed load-bearing in a snapshot for BOTH bounds (removing it makes an
endpoint witness wrongly accepted; two adversarial fixtures, one per bound,
now pin this). `extremum.rs` targets a CLOSED `[a, b]` where an endpoint
answer is legitimate by definition, so the open-interval question does not
even apply to its final answer — only to whether a boundary point may
*additionally* appear in `critical_points`, which is a completeness
question, not a soundness one, and is guarded independently by two
mechanisms (`is_strictly_inside` at the per-point check, and the
completeness cardinality recount), confirmed independently sufficient and
jointly necessary in a snapshot with all four combinations tried.
Index-status: Accepted

## Context

[ADR-1435](adr-1435-sturm-ivt-bridge-re-derives-the-half-open-upper-bound.md)'s
"Scope not covered" section named `inverse.rs`, `mvt.rs`, `extremum.rs`, and
`taylor.rs` as sharing `real_algebraic::verify_ivt_certificate`'s consuming
idiom — `count_real_roots_in(root.minimal_polynomial(), lower, upper) ==
Some(1)` — and noted `inverse.rs` had already been confirmed clean (closed
interval, no open-boundary risk). This lane audits `mvt.rs` and
`extremum.rs`; `taylor.rs` is out of scope here.

## What the two files actually do

Both files use `count_real_roots_in` in exactly one place each, and in both
cases it operates on the candidate's **own** isolating interval
(`root.isolating_interval()`), re-confirming the bracket is a valid
single-root witness for the candidate's own minimal polynomial. Neither file
ever compares that bracket's `lower`/`upper` against the caller-supplied
`a`/`b` — grepped and confirmed (`grep -n "isolating_interval\|lower\|upper"`
over both files: three hits each, all three lines are the self-consistency
check, none touch `a`/`b`).

The boundary decision against `a`/`b` is a **separate** step in both files,
and it goes through `RealAlgebraic::compare_rational`
(`crates/axeyum-ir/src/real_algebraic.rs:289`), which refines the isolating
interval by exact bignum bisection until the rational `c` provably lies
outside the current bracket (or is detected as an exact root), and returns
`Ordering::Equal`/`Less`/`Greater` accordingly — a genuinely exact decision
with no half-open-bracket-vs-open-interval shape mismatch, because it never
consults the half-open convention at all.

`mvt.rs`'s `verify_mvt_certificate` step 5:

```rust
let lifted_c = crate::real_algebraic::from_algebraic_real(c)?;
let above_a = lifted_c.compare_rational(a)?;
let below_b = lifted_c.compare_rational(b)?;
if above_a != Ordering::Greater || below_b != Ordering::Less {
    return Some(false);
}
```

`extremum.rs`'s `is_strictly_inside` (used both by the producer's interior
filter and, again, independently, at checker step 3):

```rust
fn is_strictly_inside(root: &AlgebraicReal, a: Rational, b: Rational) -> Option<bool> {
    let lifted = crate::real_algebraic::from_algebraic_real(root)?;
    let above_a = lifted.compare_rational(&a)? == Ordering::Greater;
    let below_b = lifted.compare_rational(&b)? == Ordering::Less;
    Some(above_a && below_b)
}
```

## Why the two files need different things, and both already have it

**`mvt.rs`**: MVT's conclusion names a point in the classical **open**
`(a, b)`; an endpoint witness is a false MVT claim (the module doc's
"Degenerate cases" section is explicit about this, and the file already
carried one adversarial regression, `verify_rejects_an_endpoint_witness`,
pinning the **left** bound with a genuine coincidence case — `p = x^3-4x^2`
on `[0,4]`, where `p'(0) = 0` equals the secant slope exactly). Step 5 above
is the sole strictness guard (MVT needs only one witness, so there is no
completeness recount to fall back on). Added the mirrored **right**-bound
fixture (`verify_rejects_an_endpoint_witness_at_the_right_bound`, `q =
-x^3+8x^2-16x` on `[0,4]`, the left-endpoint example reflected through
`x -> 4-x`, where `q'(4) = 0` equals the slope exactly). Verified in a
snapshot (`scripts/lane-snapshot.sh`, never the shared tree): with step 5's
condition neutralized, **both** fixtures are wrongly accepted (`Some(true)`);
restored, both correctly reject. The guard is genuinely load-bearing for
both bounds, and it is an explicit, intentional check (not an incidental
side effect of a guard written for something else, unlike the pre-fix IVT
bridge).

**`extremum.rs`**: EVT targets a **closed** `[a, b]`; an endpoint answer is
always a legitimate extremum by definition, and both endpoints
(`value_a`/`value_b`) are unconditionally compared as candidates regardless
of `critical_points`. So a boundary point wrongly admitted into
`critical_points` cannot, by itself, produce a wrong reported maximum — at
worst it is a redundant duplicate of a value already covered by the endpoint
comparison. The open-interval question here is purely about completeness of
the *candidate set claim*, not about the correctness of the *reported
answer*. Two independent guards exist: `is_strictly_inside` at the per-point
check (checker step 3) and the completeness cardinality recount (checker
step 5, which re-isolates `deriv`'s roots from scratch and compares counts).
Added four tests: two correctness spot-checks confirming the producer's own
interior filter naturally excludes a critical point sitting exactly at `a`
or `b` (`p = x^2` on `[0,2]`/`[-2,0]`, root at the shared boundary), and two
adversarial fixtures forging that excluded point back into `critical_points`.

The adversarial fixtures needed a second iteration to be genuinely isolating.
The first version (`p = x^2`, forged point's value `0` well below the true
max `4`) was still rejected with both `is_strictly_inside` and the
completeness recount removed in a snapshot — but for an unrelated reason:
checker step 6's maximality check (`max_value` must be `>=` every candidate)
caught the inconsistency regardless, since the forged `max_value` did not
dominate the real endpoint values. That is a real guard, but not the one
being audited, and its presence made the fixture non-isolating per ADR-1400's
standard ("construct an instance where every OTHER guard passes and only
that distinction separates accept from reject"). Retargeted to `p = -x^2`,
where the forged boundary point (value `0`) **is** the genuine max
(`p(0)=0 > p(±2)=-4`), so step 6 passes trivially. Re-verified all four
combinations in a snapshot:

| `is_strictly_inside` (step 3) | completeness recount (step 5) | forged cert result |
|---|---|---|
| present | present | `Some(false)` (correct) |
| removed | present | `Some(false)` (step 5 alone catches it) |
| present | removed | `Some(false)` (step 3 alone catches it) |
| removed | removed | `Some(true)` (**wrongly accepted**) |

This is genuine, non-vacuous defense in depth: either guard alone is
sufficient, and removing both is a real (if narrow — completeness, not
soundness) hole, confirming the fixture is doing real work rather than being
caught by something else.

## No floating point

`grep -n "f64\|f32"` over both files returns nothing. Unlike
`real_algebraic::polynomial_ivt`, neither producer even uses `f64` as a
selection optimization — every step in both files, producer and checker, is
exact `Rational`/`RealAlgebraic`/`BigRational` arithmetic.

## Verification

`cargo test -p axeyum-cas --lib mvt::`: 19 passed, 0 failed (1 new test).
`cargo test -p axeyum-cas --lib extremum::`: 24 passed, 1 ignored
(pre-existing, unrelated), 0 failed (4 new tests). Full `axeyum-cas --lib`:
941 passed, 0 failed, 5 ignored — unchanged aside from the 5 new tests.
`cargo clippy -p axeyum-cas --lib --tests -- -D warnings`: clean.

Commits: `b53cfd5a2` (initial audit + fixtures), `a432ca02c` (tightened the
`extremum.rs` fixtures after the snapshot check above showed the first
version was not isolating).

## Scope not covered

`taylor.rs` was not audited in this lane.
