# ADR-1435: the Sturm IVT bridge re-derives the half-open-interval upper bound instead of trusting an unrelated check

Date: 2026-09-01
Status: Accepted
Lane: `sturm-convention-repair`

Index-summary: ADR-1400/ADR-1425 named `sturm.rs`'s half-open `(lower, upper]`
convention (lower excluded, upper included) as living only in prose, with
`real_algebraic::verify_ivt_certificate` — the bridge the dominance document's
IVT row cites — consuming it "on trust." Re-derivation confirms the checker
as committed is sound (the classical open-interval claim `root < b` was
already implied by the existing checks jointly), but the strictness at the
upper bound rested entirely on the `pb.is_zero()` guard, a check written for
an unrelated purpose (the strict sign-change IVT hypothesis) many lines
earlier, with no test isolating that dependency. Added an explicit,
self-contained re-derivation directly in `verify_ivt_certificate` — when the
bracket's `upper` equals the claimed bound `b`, confirm `b` is not itself a
root of `root`'s own minimal polynomial — plus an adversarial fixture
(`make_unchecked`-forged certificate, root exactly at the claimed open upper
bound) verified in a snapshot to be wrongly ACCEPTED when both the old and
new guards are absent, and correctly REJECTED when only the new guard is
restored, proving it independently load-bearing rather than a restatement.
The mirrored lower bound needs no equivalent guard: `lower` is excluded from
the half-open bracket, so `root > lower >= a` is free.
Index-status: Accepted

## Context

[ADR-1400](adr-1400-a-certificate-must-record-every-distinction-its-acceptance-depends-on.md)
and the 2026-09-01 re-assessment
in
[`docs/formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md`](../../formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md)
(§8) named `sturm.rs`'s half-open `(lower, upper]` convention as one of two
highest-priority distinction-completeness gaps in the CAS certificate audit,
specifically because `real_algebraic::verify_ivt_certificate` — the bridge
this document's §2.2 IVT row cites as "ours" — "consumes this on trust," and
because a mutation suite structurally cannot find a missing guard (it can
only test guards that exist).

This ADR records what was actually found on inspection, since the finding as
relayed was one step removed from the code.

## What the convention actually is

`crates/axeyum-cas/src/sturm.rs` and `crates/axeyum-cas/src/algebraic.rs`
both consistently document and implement a genuinely half-open interval:
`lower` **excluded**, `upper` **included** — `(lower, upper]`. This is not a
documentation-only claim; `sturm.rs`'s own test
`counts_roots_in_a_subinterval` (roots at 1, 2, 3; `count(p, 0, 2) = 2`
includes the root at 2, `count(p, 2, 4) = 1` excludes it) empirically confirms
the exclusion/inclusion asymmetry holds, not just that it is asserted.

The convention is carried purely as a bare `(Rational, Rational)` tuple —
nothing in the type distinguishes it from a closed or open reading — which is
the concrete form of "lives only in prose."

## What was actually consuming it, and whether it disagreed

`real_algebraic::verify_ivt_certificate` is the bridge. Its certificate
(`IvtCertificate`) claims a named root lies in the **classical open**
interval `(a, b)`, while `root.isolating_interval()` returns the half-open
`(lower, upper]`. The two are genuinely different shapes, so the boundary
treatment is not symmetric: `lower >= a` alone already implies `root > a`
(exclusivity at `lower` is free), but `upper <= b` alone does **not** imply
`root < b` — `upper == b` permits `root == b` exactly, which would place the
root on the boundary of the open claim rather than strictly inside it.

Working through the full check set as committed (`a < b`; `p(a) != 0`,
`p(b) != 0`; opposite signs; `lower >= a`, `upper <= b`; `lower < upper`;
`minimal_poly` divides `poly` exactly; re-derived Sturm count `== 1`),
`root == b` is provably impossible whenever the certificate is accepted:
`minimal_poly` divides `poly` exactly, so if `root == b` then
`poly(b) == minimal_poly(b) * quotient(b) == 0`, contradicting the earlier
`pb.is_zero()` rejection. **So the checker as committed is sound** — it was
not producing false accepts on the exact `p(x) = x - 2` example named in the
audit's illustration.

What it *did* have: the strictness at the upper bound was resting entirely
on `pb.is_zero()`, a guard written for a different purpose (the classical IVT
hypothesis requires a strict sign change, not a boundary root) many lines
above the bracket-containment check, with no test exercising this specific
coupling. This is exactly the `nra_monomial_bound_cert` shape CLAUDE.md
already treats as the canonical lesson: a check that happens to be sufficient
is not the same as a check that is *understood* to be necessary, and nothing
would have caught it silently becoming insufficient under a future edit.

## Decision

Add an explicit, self-contained re-derivation in `verify_ivt_certificate`,
per ADR-1400's preference order (re-derive over record-plus-control): when
`upper == b` exactly, evaluate `root`'s own minimal polynomial at `b` and
reject if it vanishes there. This re-derives "`b` is not `root`" directly
from `root`'s own data, independent of `poly`/`pb` and independent of check
ordering. No equivalent guard is needed at the lower bound — `lower` is
excluded from the half-open bracket by construction, so `root > lower >= a`
holds unconditionally.

## Verification

Three tests added to `crates/axeyum-cas/src/real_algebraic.rs`:

- `verify_rejects_a_root_forged_exactly_at_the_open_upper_bound` — an
  adversarial certificate built with `algebraic::test_support::make_unchecked`
  (minimal polynomial `x - 2`, legitimate half-open bracket `(1, 2]`, claimed
  open interval `(0, 2)`) where the root sits exactly at the claimed `b`.
- `verify_accepts_a_loose_but_genuinely_open_upper_bound` — the non-vacuity
  control: the same root, a `b` strictly past it, correctly accepted.
- `verify_accepts_a_root_bracket_touching_the_open_lower_bound_exactly` — a
  regression control recording that `lower == a` exactly is still accepted
  (a completeness fact, not a soundness one).

Verified both ways in an isolated snapshot (`scripts/lane-snapshot.sh`, never
the shared tree): with **both** the pre-existing `pb.is_zero()` guard and the
new re-derivation removed, `verify_rejects_a_root_forged_exactly_at_the_open_
upper_bound` **fails** (`Some(true)`, wrongly accepted) — demonstrating the
underlying vulnerability is real once the implicit coupling is gone. With
only the new re-derivation restored (`pb.is_zero()` still removed), the same
test **passes** (`Some(false)`, correctly rejected) — proving the new guard
is independently load-bearing rather than a restatement of the old one.

Full `axeyum-cas --lib` suite: 936 passed, 0 failed, 5 ignored, unchanged
aside from the 3 new tests. `clippy -p axeyum-cas --lib --tests -D warnings`
clean.

## Scope not covered

`inverse.rs`, `mvt.rs`, `extremum.rs`, and `taylor.rs` all consume
`sturm::count_real_roots_in` with the same
`count_real_roots_in(root.minimal_polynomial(), lower, upper) == Some(1)`
idiom. `inverse.rs`'s `verify_inverse_certificate` already handles the
degenerate point-bracket case explicitly and targets a **closed** interval
`[a, b]` (so it does not have this specific open-vs-half-open boundary risk —
`root == b` is a legitimate accept there, not a forgery). `mvt.rs` and
`extremum.rs` were not audited for the same distinction in this pass; they
are candidates for the same treatment if their certificates make the same
open-interval claim `verify_ivt_certificate` does.

No floating point is used anywhere in `sturm.rs`, `algebraic.rs`, or the
`verify_ivt_certificate` bridge — all sign decisions are over exact
`Rational` arithmetic. `polynomial_ivt` (the producer) does use `f64` to
*select* which isolated root lies near `(a, b)` (an optimization, not a
soundness-bearing step — the checker re-derives everything from exact
arithmetic and does not trust the producer's selection), which is unrelated
to the finding here and not a soundness risk since the checker never reads
the `f64` value.
