# Lane: holomorphy — the complex derivative is the real shelf's UNIFORM one

<!-- plan-section: lane-status -->

**`Complex.HasDerivativeOn` landed; Leibniz did not, and the obstruction is not
algebra** (`WIP`, holomorphy, 2026-09-05). The brief asked for
`Complex.HasDerivAt` "in the ε–δ form the real shelf uses". The real shelf has
no pointwise derivative: `CReal.HasDerivativeOn F F' a b` is Bishop's *uniform*
differentiability on a closed interval, a one-constructor inductive in `Type`
whose first field is a modulus `Nat → Nat` as DATA. So the lane declared the
same shape on a CLOSED disc and no `Complex.HasDerivAt` at all — a pointwise
complex derivative beside a uniform real one makes every future bridge a
conversion rather than a transcription. Nine new checked, axiom-free
declarations in `crates/axeyum-lean-kernel/src/complex/deriv.rs`:
`Complex.abs_zero`, `Complex.InDisc`, `Complex.HasDerivativeOn` with its
`.mk`/`.rec`/`.modulus`/`.spec`, and `hasDerivative_const` / `_id` / `_neg` /
`_add`.

The lane's measurable finding is **which half of the transcription gets
cheaper**. The ALGEBRA does: `complex/ring.rs`'s `ring_law_proof` decides every
error-term identity in one call, replacing ninety lines and five named helpers
(`neg_add_distrib`, `right_distrib`, `add4_comm` ×2, three `add_congr`
liftings) in the real sum rule, and `Complex.abs`'s nonnegativity removes the
real closing step's two-sided `abs_le` split. The ANALYSIS does not:
`hasDerivative_add` uses `Rat.natDivSucc_antitone` at the identical indices and
fuses its two `1/(2e+2)` bounds through `Rat.natDivSucc_add` and
`Rat.natDivSucc_halve` exactly as the real proof does — that bookkeeping is
about rational indices, not about the carrier, and moving up a carrier neither
helps nor hurts it.

**Leibniz is blocked on three missing ℂ ESTIMATES, not on the ring
identity.** The decomposition
`E = EF·G(y) + F'(x)(y−x)(G(y) − G(x)) + F(x)·EG` is one `ring_law_proof`
call; bounding it needs a uniform bound on `|G|`, one on `|F'|`, one on `|F|`,
and a modulus of continuity for `G`. The real `hasDerivative_mul` takes exactly
these as `UniformlyContinuousOn` plus two `Nat` witnesses. Neither
`Complex.BoundedOn` nor `Complex.UniformlyContinuousOn` exists — checked against
the full `Complex.*` inventory. ADR-1642 records both routes and recommends the
hypothesis-carrying one, because `Complex.abs_mul` is an exact `Equiv` where
the real side needed `abs_mul_le_of_bounds`. `polyEval`'s derivative is blocked
behind Leibniz and nothing else; `Complex.Holomorphic` is blocked on a `Sigma`
(not an `Exists` — `HasDerivativeOn` is in `Type 0`); Cauchy–Riemann needs
three named bridge lemmas (`abs_ofReal`, `abs_re_le`, `abs_im_le`). Complex
power series, `exp` on ℂ, and Cauchy's theorem on a triangle were not started.

Detail and the sizing of each obstruction:
[ADR-1642](../../research/09-decisions/adr-1642-the-complex-derivative-is-the-real-shelfs-uniform-one-not-a-pointwise-hasderivat.md).

<!-- plan-section: landed-changes -->

| 2026-09-05 | `a3066cd01` | `complex/deriv.rs`: `Complex.HasDerivativeOn` on a closed disc, the transcription of `CReal.HasDerivativeOn` — carrier, `.modulus`/`.spec` projections, `InDisc`, `abs_zero`, and the constant / identity / negation / sum witnesses. New module registered from `complex.rs` with its own `DerivNames` (the `poly.rs` arrangement: no hub edit for a new declaration inside the file). All nine names registered in `every_named_complex_declaration_is_checked_and_footprint_free`, which derives coverage from the ENVIRONMENT. |
