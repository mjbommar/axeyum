# ADR-1656: The ℂ polynomial derivative is a transport, and Cauchy–Riemann is blocked on component extraction rather than on the disc

Status: accepted
Date: 2026-09-06
Index-summary: Closure of `Complex.UniformlyContinuousOn` under `+` and `·` lands, and with it `Complex.hasDerivative_congr` (transport along disc-local `Equiv`) and `Complex.hasDerivative_pow` (the power rule at exponent `succ n`). Three design calls are recorded. First, the accuracy budget on ℂ is `CReal`'s verbatim — `natDivSucc_antitone`, `natDivSucc_scale` via `fold_index0_first`, `natDivSucc_add`/`_halve` — because `Complex.UniformlyContinuousOn`'s bound is `CReal.le (Complex.abs …) (CReal.ofRat …)`, so nothing past the modulus is complex; what ℂ actually buys is the ALGEBRA, and the real shelf's ~60-line private `product_diff_identity` plus its `add4_comm`/`neg_add` shuffle are each ONE `ring_law_proof` call here. Second, the power induction still commutes the product before applying `hasDerivative_mul`, and landing `uniformlyContinuous_mul` does NOT remove that: `hasDerivative_mul` needs continuity of its FIRST factor and the step's first factor is the already-built `pow (·, j)`, whose own continuity is what is missing — closure under products answers a different question. Third, the Cauchy–Riemann bridge is cheap and is NOT the obstruction: `(c + ofReal u) − c ~ ofReal u` is a two-atom ring identity and `Complex.abs_ofReal` converts the modulus, so disc membership from a real offset is two rewriting steps. What CR is blocked on is component extraction — pushing a complex error bound down to its real part — which needs a `re`-distribution law over `add`/`neg`/`mul` that `complex.rs` has as `Equiv` congruences but not as a homomorphism, plus a modulus transport. `hasDerivative_polyEval` did not land; the obstruction is sized in this ADR.
Index-status: accepted

- **Lane**: `complex-polyderiv` (roadmap W3-5, third slice)
- **Follows**: [ADR-1642](adr-1642-the-complex-derivative-is-the-real-shelfs-uniform-one-not-a-pointwise-hasderivat.md)
  (the ℂ derivative is the real shelf's UNIFORM one, with the disc replacing the
  interval) and
  [ADR-1646](adr-1646-the-complex-estimates-are-a-carrier-change-and-the-index-arithmetic-is-not.md)
  (`BoundedOn`/`UniformlyContinuousOn` on ℂ are a carrier change, and the index
  arithmetic beneath them is not).

## Context

ADR-1646 landed `Complex.BoundedOn` and `Complex.UniformlyContinuousOn` and
`complex/leibniz.rs` landed `Complex.hasDerivative_mul`, which takes four
hypotheses it does not derive: uniform continuity of `F`, and `BoundedOn` for
`F`, `G` and `G'`. `leibniz.rs`'s own module documentation named the remaining
obstruction between that and a polynomial's derivative precisely: an induction
over the degree applies the product rule at every step and must **rebuild** all
four for the accumulated partial polynomial. `bounded_on_add` and
`bounded_on_mul` had closed two of the four. This lane closed the other two and
then went as far up the ladder as the closures reach.

## Decision

### 1. The accuracy budget is reused verbatim; only the algebra is re-derived

`Complex.UniformlyContinuousOn`'s spec bounds `CReal.le (Complex.abs (F x − F
y)) (CReal.ofRat (natDivSucc 1 n))`. Everything after `Complex.abs` is
therefore a `CReal` statement, and every lemma the real closure proofs use to
manage indices — `Rat.natDivSucc_antitone` to weaken a summed modulus down to
each summand's own, `Rat.natDivSucc_scale` (through
`creal/derivative.rs::fold_index0_first`) to absorb a magnitude weight,
`Rat.natDivSucc_add` and `Rat.natDivSucc_halve` to fuse two `1/(2n+2)` shares
into `1/(n+1)` — mentions no carrier at all.

So `complex/uc_closure.rs` reuses them, and the reuse is **exact rather than
approximate**. That is the same call ADR-1646 made for `hasDerivative_mul`'s
budget, and this ADR records that it survived contact with a second, harder
consumer: `uniformlyContinuous_mul` needs the weight `e_g := rescale_index(k₁,
m) = (k₁+1)·m + k₁`, and that index may not be spelled any other equal-valued
way, because `natDivSucc_scale`'s statement is what makes the final fold
typecheck.

What is NOT reused is the algebra. `creal/uniform_continuity.rs` carries a
private ~60-line `product_diff_identity` for
`F(x)G(x) − F(y)G(y) = F(x)(G(x) − G(y)) + G(y)(F(x) − F(y))`, built from
`left_distrib`/`mul_comm`/`neg_congr`, and a hand-built `add4_comm`/`neg_add`
shuffle for the `add` case. On ℂ each is a single `super::ring_law_proof` call.
This is the third consumer of `complex/ring.rs` to pay for it outright, after
the ring laws themselves and `hasDerivative_mul`'s six-leaf shuffle.

### 2. The power induction still commutes, and `uniformlyContinuous_mul` does not change that

`creal/derivative.rs::declare_has_derivative_pow` carries a paragraph marked
STALE, noting that `CReal.uniformly_continuous_mul` exists and still does not
close the gap. The same reasoning applies here and this ADR restates it as a
decision rather than leaving it to be rediscovered:

`Complex.pow z (Nat.succ j) ≡ mul (pow z j) z` puts the already-built
`pow (·, j)` on the LEFT, and `hasDerivative_mul` needs
`UniformlyContinuousOn` on its **first** factor. Continuity of `pow (·, j)` at
an arbitrary `j` is exactly what the induction does not have.
`uniformlyContinuous_mul` gives continuity of a product from continuity of its
factors, which is a different statement. So the step builds
`HasDerivativeOn (fun z => mul z (pow z (succ j)))` with `F := id` (continuity
from `uniformlyContinuous_id`, available at every step) and transports across
`Complex.mul_comm`.

That transport is why `Complex.hasDerivative_congr` had to exist. It demands
agreement **only on the disc**, decided from `HasDerivativeOn.spec`'s own type
rather than assumed: `spec`'s conclusion mentions `F x`, `F y`, `F' x` solely
inside a body reached through `InDisc c r x → InDisc c r y → …`, the same
memberships a caller must already hold. It reuses `F`'s modulus verbatim,
because a relabelling is not an estimate.

The exponent is stated as `Nat.succ n`, not `n`. At `n` the derivative would
mention `pow x (n − 1)`, and `Nat.sub` is truncated.

ℂ makes the induction's step case markedly cheaper than the real one for a
reason worth recording: `Complex.ofNat_succ` and `Complex.pow_succ` both close
by `Eq.refl`, so `ofNat (succ (succ j))` **is** `add (ofNat (succ j)) one` and
`pow x (succ j)` **is** `mul (pow x j) x` to the kernel. The whole
derivative-agreement obligation collapses to the polynomial identity
`(C+1)·P·x = 1·(P·x) + x·(C·P)` in three opaque atoms — one `ring_law_proof`
call where the real shelf spends `mul_comm`/`mul_assoc`/`right_distrib`/
`add_comm`/`of_nat_succ_equiv` in sequence.

### 3. Boundedness stays a hypothesis, as two Skolem functions

`hasDerivative_mul` needs three `Nat` magnitude bounds at every step. Deriving
`BoundedOn (pow · n) c r _` and `BoundedOn` of its derivative for every `n`
needs Nat-indexed recursive bound machinery that is a separate undertaking.
`Complex.hasDerivative_pow` therefore takes `kb, kd : Nat → Nat` and proofs
that they work for **every** `n`, the shape `CReal.hasDerivative_pow` already
uses. This is a deliberate repeat of the real shelf's call, not an oversight:
folding the three bounds into one would need a
`natDivSucc(m,0)·natDivSucc(n,0) = natDivSucc(m·n,0)` identity this prelude
does not have.

### 4. The Cauchy–Riemann bridge is cheap; CR is blocked elsewhere

The brief asked for the bridge from `CReal.HasDerivativeOn`'s four interval
hypotheses to disc membership, built first, with its cost reported. Measured:
**two rewriting steps and no estimate.** Parametrising the horizontal segment
through `c` by its real offset `u`, the point is `c + ofReal u`, and

```text
(c + ofReal u) − c  ~  ofReal u
```

is a two-atom ring identity — one `ring_law_proof` call — after which
`Complex.abs_ofReal` (ℝ ↪ ℂ is an isometry, landed with ADR-1646's component
file) converts `Complex.abs` to `CReal.abs` and `CReal.le_congr` carries the
caller's bound across both steps. The vertical segment costs exactly one lemma
more: `Complex.abs_I ~ CReal.one`, by the `normSq`-then-`sqrt` route
`Complex.abs_one` and `Complex.abs_zero` already take, feeding
`Complex.abs_mul`.

The hypothesis shape is the two ONE-SIDED bounds `le u r` and `le (neg u) r`,
not `le (abs u) r`, because that is the form interval facts arrive in:
`le a t` and `le t b` on a segment centred at `c` re-centre to exactly those
two. `CReal.abs_le` (which is `max_le` verbatim) folds them with no order
algebra at the call site.

So the bridge is **not** what blocks Cauchy–Riemann. What blocks it is
component extraction: from `Complex.HasDerivativeOn F F' c r` one must produce
`CReal.HasDerivativeOn (fun t => re (F (c + ofReal t))) (fun t => re (F' (c +
ofReal t))) a b`. Three things are needed and none exists:

1. the complex error bound must be pushed to its real part —
   `Complex.abs_re_le` gives the inequality direction, but not the equality of
   the two error TERMS;
2. the real spec's error `(u(y) − u(x)) − u'(x)(y − x)` must be recognised as
   `re` of the complex one, i.e. `re` must distribute over `add`, `neg` and
   `mul`. `complex.rs` has `re_congr` (a congruence for `Equiv`) but no `re`
   HOMOMORPHISM law, and for `mul` there is none to have — `re (z·w)` is
   `re z · re w − im z · im w`, so the real part of the complex error is not
   the real error unless the imaginary parts are controlled too, which is
   precisely the content of the CR equations;
3. the modulus must transport, since the complex modulus is stated against
   `Complex.abs (y − x)` and the real one against `CReal.abs (y − x)`; on a
   horizontal segment those agree only through this file's own identity.

Item 2 is the real one, and it is why CR is a genuine slice rather than a
corollary: the horizontal and the vertical derivative must be computed
SEPARATELY, each yielding two real component derivatives, and the equations
are the statement that the two computations of `F'(c)` agree. That needs `re`
and `im` of `F'(c) · ofReal u` and of `F'(c) · (I · ofReal v)` written out,
which is `Complex.mk`-level algebra the ring calculus can do but which has no
named lemma yet.

## Consequences

- `Complex.uniformlyContinuous_add` and `Complex.uniformlyContinuous_mul` close
  the last two of `hasDerivative_mul`'s four hypotheses under the operations a
  polynomial induction uses.
- `Complex.hasDerivative_congr` is the first transport on this shelf and is
  reusable by anything that produces a derivative in a non-canonical syntactic
  form.
- `Complex.hasDerivative_pow` gives the monomial derivative at every exponent,
  gated on the two magnitude Skolems, and `Complex.holomorphic_pow` packs it
  into the `Sigma` so a consumer reads the derivative back with
  `Complex.holomorphicDeriv` instead of re-spelling it. The four Skolem
  hypotheses are supplied once per disc rather than once per exponent.
- `Complex.hasDerivative_polyEval` and `Complex.holomorphic_polyEval` did NOT
  land. With `hasDerivative_pow` in place the remaining work is a second
  induction over the coefficient list of `Complex.polyEval`, which needs
  `BoundedOn` and `UniformlyContinuousOn` for each partial sum — both now
  available as closures, but each application needs the Skolem magnitudes
  supplied at the accumulated degree, i.e. a `Nat → Nat` built by recursion
  over the same list. That recursion, not the analysis, is the remaining slice.
- The CR bridge lemmas are landed and cheap; the CR equations are sized above
  and are the next slice.

## Alternatives considered

- **Deriving continuity of `pow (·, j)` by induction so the product rule could
  be applied without commuting.** Rejected: it needs the same Skolem magnitudes
  at every step AND a second induction, and it buys nothing the
  `mul_comm` transport does not already buy in one `hasDerivative_congr` call.
- **Stating the power rule at exponent `n` with `pow x (n − 1)` in the
  derivative.** Rejected: `Nat.sub` is truncated, so the statement would be
  wrong at `n = 0` and the induction would need a case split that the `succ n`
  form does not.
- **Making the bridge take `le (abs u) r` only.** Kept as the core lemma, but
  the two-sided form is exported alongside it, because every caller holds the
  one-sided facts and would otherwise repeat the `abs_le` fold.
