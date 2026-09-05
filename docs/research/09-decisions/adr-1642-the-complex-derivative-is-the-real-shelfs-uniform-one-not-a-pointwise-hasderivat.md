# ADR-1642: the complex derivative is the real shelf's UNIFORM one, and the ring calculus pays for exactly half of it

Status: proposed
Date: 2026-09-05
Lane: `holomorphy`
Roadmap: W3-5 (complex differentiability, holomorphy, Cauchy's theorem)

Index-summary: The brief asked for `Complex.HasDerivAt` "in the ε–δ form the
real shelf uses". The real shelf has **no pointwise derivative**: `CReal.HasDerivativeOn F F' a b`
is Bishop's *uniform* differentiability on a closed interval, a one-constructor
inductive in `Type` whose first field is a modulus `Nat → Nat` as DATA. So this
lane declared `Complex.HasDerivativeOn F F' c r` — the same shape, on a CLOSED
disc `InDisc c r z := CReal.le (Complex.abs (z − c)) r` — and no
`Complex.HasDerivAt` at all, because a pointwise complex derivative sitting
beside a uniform real one makes every future bridge between the shelves a
conversion rather than a transcription. The interval's FOUR range hypotheses
collapse to TWO disc memberships; everything else is carried across position
for position, and the error bound is a `CReal` on both sides because
`Complex.abs` already is. The lane's measured finding is that the transcription
is **cheap in exactly one half and not the other**: `complex/ring.rs`'s
`ring_law_proof` decides every error-term identity in one call, replacing
ninety lines and five named helpers in the real sum rule
(`neg_add_distrib`, `right_distrib`, `add4_comm` twice, three `add_congr`
liftings), and `Complex.abs`'s nonnegativity removes the real closing step's
two-sided `abs_le` split — but the ANALYTIC half transcribes verbatim, with
`Rat.natDivSucc_antitone`, `Rat.natDivSucc_add` and `Rat.natDivSucc_halve`
used at the identical indices. Leibniz did NOT land, and the obstruction is
named and sized here: it is not the algebra, it is the three missing ℂ-side
estimates (a value bound, a derivative bound, and a modulus of continuity)
that the real `hasDerivative_mul` takes as `UniformlyContinuousOn` plus two
`Nat` witnesses — neither `Complex.BoundedOn` nor `Complex.UniformlyContinuousOn`
exists. `Complex.HolomorphicOn` landed as a `Sigma` (not an `Exists`).

Index-status: proposed

## Context

The lane brief listed four deliverables: (1) `Complex.HasDerivAt` with
constant/identity/sum/product/`polyEval` witnesses and uniqueness under
apartness; (2) `Complex.Holomorphic` on a disc, polynomials holomorphic, and
Cauchy–Riemann in one direction; (3) complex power series with `exp` as an
instance; (4) Cauchy's theorem for a polynomial on a triangle via the
antiderivative.

Before writing anything the lane read the real derivative shelf, because the
brief's own instruction was to "mirror its modulus convention exactly". That
read decided the shape of everything below and is the first thing this ADR
records.

## Decision 1 — there is no `Complex.HasDerivAt`, and that is deliberate

`crates/axeyum-lean-kernel/src/creal/derivative.rs` (9,646 lines) declares
`CReal.HasDerivativeOn (F F' : CReal → CReal) (a b : CReal) : Type`, a
one-constructor inductive with four leading parameters whose constructor is

```
mk (modulus : Nat → Nat) (spec : ∀ e x y, le a x → le x b → le a y → le y b →
      le (abs (y − x)) (ofRat (1/(modulus e + 1))) →
      le (abs ((F y − F x) − F' x · (y − x))) ((1/(e+1)) · abs (y − x)))
```

The modulus is a field in `Type`, not an `Exists`, for the reason that file's
module documentation gives at length: `0 < x` and its `Nat` witness are the
same proposition, yet the witness cannot be pulled out of an `Exists` and used
to build anything in `Type`. There is no pointwise `CReal.HasDerivAt` anywhere
in the development (checked against the whole `CReal.*` declared inventory:
the derivative names are `HasDerivativeOn`, its two projections, and
`hasDerivative_{const,id,sq,neg,add,smul,sub,mul,pow,cube,chain,congr,…}`).

So `Complex.HasDerivativeOn F F' c r` is declared with the identical arity and
the identical constructor shape. The only structural change is the domain: an
interval is two inequalities per point and a disc is one, so the four range
hypotheses become

```
InDisc c r x → InDisc c r y
```

with `Complex.InDisc c r z := CReal.le (Complex.abs (z − c)) r`.

**Why the disc is CLOSED (`le`, not `lt`).** The brief wrote the disc as
`{z : abs (z − c) < r}`. The real shelf's domain is the CLOSED interval
`[a,b]`, and a uniform modulus is precisely the notion that behaves on a
compact domain. Carrying `le` across keeps the two carriers' derivative
predicates transcriptions of each other; a strict disc would have been equally
sound but would have introduced a difference no lemma bridges, for no gain — a
statement about the open disc of radius `r` follows from the closed disc of
every smaller radius.

There is no `Complex.sub`; `a − b` is `add a (neg b)` throughout, which is the
convention both `complex.rs` (see `ComplexPrelude::sub_div`'s field comment)
and `creal/derivative.rs`'s own `cdiff` already use.

## Decision 2 — the module owns its names, and touches no hub

`complex/deriv.rs` follows `complex/poly.rs`'s arrangement (Part B of
`docs/research/11-design-review/2026-08-27-prelude-build-spike.md`): its
declared names live in a `DerivNames` sub-struct reached as `p.deriv.*`, its
`BuildStep` entry `provides: &[]` because nothing outside the file requires any
of them, and adding a declaration inside it touches neither `ComplexPrelude`,
nor `STEPS`, nor `intern_names`. The step's `requires` list is the eleven hub
fields its proof terms actually reference, so the structural preflight
(`validate_step_order`) catches a step reordered before its dependency with a
diagnosis, rather than the kernel emitting an `UnknownConst` that cannot be
told from "never written".

## Decision 3 — what the ring calculus pays for, measured

The interesting result of this lane is not that the transcription works; it is
*which half of it gets cheaper*.

**Cheaper — the algebra.** `complex/ring.rs`'s `ring_law_proof` decides any
commutative-ring identity between `CExpr`s by normalising both sides to a
sorted multiset of signed monomials. Every derivative witness's error-term
identity is such an identity. Concretely:

| step | real (`creal/derivative.rs`) | complex (`complex/deriv.rs`) |
| --- | --- | --- |
| constant's error is zero | `const_error_equiv_zero`, a named helper | one `ring_law_proof` |
| identity's error is zero | `id_error_equiv_zero`, a named helper | one `ring_law_proof` |
| sum's error IS the sum of errors | ~90 lines, steps A–E, five helpers (`neg_add_distrib`, `right_distrib`, `add4_comm` ×2, three `add_congr` liftings) | one `ring_law_proof` |
| negation's error IS the negated error | `neg_mul_equiv_left` + `le_abs_neg_of_le_abs` | one `ring_law_proof` + `Complex.abs_neg` |

The closing step is shorter too. `creal/derivative.rs::close_zero_error` needs
a two-sided `abs_le` split, because `CReal.abs` is a defined lattice operation
and bounding it is bounding two things. `Complex.abs` is `sqrt (normSq ·)` and
`Complex.abs_nonneg` is already available, so an `Equiv`-zero error closes
through `abs_congr` → `Complex.abs_zero` → `le_of_equiv` → `le_trans`, with no
split. `Complex.abs_zero` did not exist (`Complex.abs_one` did) and is declared
here; `CReal.sqrt_zero` plus the `CReal` ring calculus make it three lines.

**Not cheaper — the analysis.** `Complex.hasDerivative_add`'s index arithmetic
is the real proof's, verbatim and for the identical reason. The combined
modulus is `mSum e := mF (2e+1) + mG (2e+1)`, and reading `F`'s and `G`'s own
hypotheses out of the single `mSum` one needs
`Rat.natDivSucc_antitone` at the `Nat` indices `mF (2e+1)` and `mSum e` —
`creal/derivative.rs`'s module documentation records that this lemma was the
*blocker* for the real sum rule and that three other `natDivSucc` lemmas that
"look close" are not it. Fusing the two `1/(2e+2)` bounds into `1/(e+1)` is
`Rat.natDivSucc_add` then `Rat.natDivSucc_halve`, again verbatim. None of that
is about ℂ at all: it is the shared rational-index bookkeeping, and moving up a
carrier neither helps nor hurts it.

The one place ℂ is *ahead* of ℝ analytically is `Complex.abs_mul`, which is an
exact `Equiv` (`abs (z·w) ~ abs z · abs w`) where the real side had to build
`abs_mul_le_of_bounds` before its scalar-multiple rule would close. That is
banked for the next lane, not spent here.

## Consequence — what did NOT land, and the size of each obstruction

Recorded so the next lane does not re-derive the diagnosis.

**Leibniz (`hasDerivative_mul`) — blocked on three missing ℂ estimates, not on
algebra.** The decomposition is standard and the ring calculus discharges it in
one call:

```
E = EF·G(y) + F'(x)(y−x)(G(y) − G(x)) + F(x)·EG
```

Bounding it needs, in order: a uniform bound on `|G|` over the disc, a uniform
bound on `|F'|`, a uniform bound on `|F|`, and a **modulus of continuity for
`G`** to control `|G(y) − G(x)|`. The real `CReal.hasDerivative_mul` takes
exactly these as `UniformlyContinuousOn F a b` plus two `Nat` bound witnesses
`k1 k2`. On ℂ, neither `Complex.BoundedOn` nor `Complex.UniformlyContinuousOn`
exists — checked against the full `Complex.*` inventory. Two routes, both real
work:

1. Declare the two ℂ predicates and transcribe the real estimate. Sized at the
   real file's own `hasDerivative_mul` (lines 4946–5940, ~1,000 lines) plus the
   two carriers.
2. Carry the four bounds as explicit hypotheses on the theorem, as the real
   `hasDerivative_smul` carries its `k`. Cheaper in infrastructure, but the
   three-way split of `1/(e+1)` into `natDivSucc 3 (3e+2)` and the
   `natDivSucc_scale` rescaling of each piece by its own constant is the same
   index arithmetic three times over.

Route 2 is the recommendation: `Complex.abs_mul`'s exactness makes each piece's
bound an equality rather than an estimate, which is the step that cost the real
side its `abs_mul_le_of_bounds`.

**`polyEval`'s derivative — blocked on Leibniz.** The induction over
`Complex.polyEval c n x = sumRange (fun i => c i · xⁱ) n` needs the product
rule at every step. Nothing else is missing: `polyEval_succ`, `polyEval_zero`,
`pow_succ` and `sumRange_succ` are all present.

**`Complex.HolomorphicOn` LANDED, as a `Sigma`.** "Has a derivative at every
point" over a disc is `Σ (F' : Complex → Complex), HasDerivativeOn F F' c r`.
It cannot be an `Exists`: `Exists`'s predicate must land in `Prop`, and
`HasDerivativeOn` is in `Type 0` by Decision 1. `sigma_prelude`'s
universe-polymorphic `Sigma.{u,v}` (ADR-1613) at `u = v = 0` is exactly the
right instance, since `Complex → Complex` and `HasDerivativeOn F F' c r` both
sit in `Type 0`.

This is not a weaker statement than the ∃-form; it is the CONSTRUCTIVE one, and
it is what a later Cauchy-integral argument will need. `Complex.holomorphicDeriv`
(`Sigma.fst`) is a total function on witnesses and `Complex.holomorphic_spec`
(`Sigma.snd`, the DEPENDENT projection) recovers the full ε–δ bound about the
very function `holomorphicDeriv` hands back. `holomorphic_const`,
`holomorphic_id`, `holomorphic_neg` and `holomorphic_add` land with it, each
storing the derivative it used rather than discarding it — which is what the
tests pin: `holomorphic_spec` at `holomorphic_id` is admitted against the
literal `fun _ => Complex.one`, and refused against `fun _ => Complex.zero`.

**Polynomials holomorphic — blocked behind Leibniz**, through `polyEval`.

**Cauchy–Riemann in one direction — the route is identified and the missing
pieces are three `CReal`/`Complex` bridge lemmas.** The honest statement, given
`hd : HasDerivativeOn F F' c r`, is that the real and imaginary component
functions restricted to a horizontal (resp. vertical) segment inside the disc
are `CReal.HasDerivativeOn` with derivatives `re (F' ·)` and `im (F' ·)` (resp.
`−im (F' ·)` and `re (F' ·)`) — which together say `u_s = v_t` and `u_t = −v_s`.
The geometric side condition is taken as a hypothesis
(`∀ t, le a t → le t b → InDisc c r (mk t s)`), which is what keeps it
tractable. What is missing is:

- `Complex.abs_ofReal : Equiv (abs (ofReal t)) (CReal.abs t)`. `CReal.sqrt_sq`
  requires `0 ≤ x`, so this needs `sqrt (t·t) ~ |t|` at a general sign, i.e.
  `sqrt_sq` at `|t|` plus `|t|·|t| ~ t·t`.
- `Complex.abs_re_le : CReal.le (CReal.abs (re z)) (Complex.abs z)` and its
  imaginary twin, from `sqrt_le_sqrt` and `le_add_of_nonneg`.

Those three are the whole gap; the transport of the spec through them is
mechanical.

**Complex power series, `exp` on ℂ, and Cauchy's theorem on a triangle — not
started.** Deliverable 3's data-radius pattern (ADR-1638) transfers, and
deliverable 4 additionally needs a contour integral over a segment as a
`CReal.sumRange` Riemann sum. Neither was reached; neither is blocked by
anything this lane found.

## Alternatives considered

**A pointwise `Complex.HasDerivAt` next to the uniform real one.** Rejected
under Decision 1: it would be the only pointwise derivative in the development
and every bridge to the real shelf would be a conversion. If a pointwise
derivative is wanted, it should be introduced on ℝ first and ℂ should follow.

**An open disc (`lt`).** Rejected under Decision 1 for the same
transcription reason, and because the closed disc is strictly more useful to a
uniform modulus.

**Declaring `Complex.BoundedOn` / `Complex.UniformlyContinuousOn` in this
lane to unblock Leibniz.** Rejected on sizing: it is the larger half of the
real derivative file and would have left nothing else landed. The
hypothesis-carrying form (route 2 above) is the recommendation instead.

## Consequences

- Eighteen new checked, axiom-free declarations in the `Complex` namespace, all
  registered in `every_named_complex_declaration_is_checked_and_footprint_free`
  — a test that derives its coverage from the ENVIRONMENT, so a name omitted
  from its list fails rather than going unchecked.
- The next lane on this shelf starts from Leibniz with a named route and a
  size, not from a blank file.
- `Complex.abs_zero` is now available to every future ℂ estimate whose error
  term vanishes.
