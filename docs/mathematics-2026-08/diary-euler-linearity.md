# Diary — linear elimination, and `euler-line` (lane `euler-linearity`), 2026-08-15

The previous lane left a diagnosis it did not act on:

> All four hypotheses are **linear in `ox, oy, hx, hy`** over `ℚ[ax..cy]` —
> Buchberger is being asked to rediscover Cramer's rule by monomial reduction.

It is right, and acting on it takes `euler-line` from *does not return in 27
minutes* to a **checked certificate in 4–6 ms**. The corpus is eight theorems,
`frontier()` is empty, and the certificate is in the original generators.

---

## 1. The comparison, on the previous lane's own ladder

`geometry_obstruction` reproduces exactly on this box today (15.9 s against the
recorded 15.8 s), so the two columns below are the same measurement of the same
theorem under the same conditions, and only the algorithm differs.

`euler-line`, `grevlex`, full condition set:

| route | S-pairs processed | still queued | basis | widest polynomial | elapsed | outcome |
|---|---|---|---|---|---|---|
| cofactor-tracked Buchberger | 9 | 66 | 12 | 41 | 53 ms | rung ceiling |
| | 33 | 210 | 21 | 278 | 5.7 s | rung ceiling |
| | 65 | **528** | **33** | 477 | 15.9 s | rung ceiling |
| | 129 | — | — | — | **> 27 min, killed** | — |
| **linear elimination** | **0** | **0** | **0** | — | **4–6 ms** | **certified, checker-verified** |

The zero in that last row is not a formatting artefact and it is worth stating
precisely: the elimination's **residue is exactly the zero polynomial**, so no
Gröbner reduction is ever started. That short-circuit is load-bearing rather than
an optimisation — reducing even the zero polynomial computes a Gröbner basis of
the generators first, which is exactly the divergent computation. The first
version of the comparison example asked for the counters unconditionally and hung
on the theorem it was measuring.

What the route actually found:

```text
ogh-collinear   blocks=2   multiplier=21 terms, degree 4   residue=0 terms
    block ["ox","oy"] rows [0,1]  det = 6 terms  ^1
    block ["hx","hy"] rows [2,3]  det = 6 terms  ^1
```

Two 2×2 systems, exactly as the diagnosis predicted. The determinants are
`4·collinear(A,B,C)` and `collinear(A,B,C)`, so the multiplier is
`4·collinear(A,B,C)²` — a **power of the theorem's own non-degeneracy
condition**, which is the fact everything in §2 turns on.

---

## 2. How the certificate survives, which was the actual question

The brief was blunt about this and it is the part worth reading. A `cas-certificate`
route delivers an identity `target = Σ cofactorᵢ·generatorᵢ` that an independent
checker re-derives by polynomial arithmetic. **A linear-elimination step must
produce cofactors in the ORIGINAL generators, or it has proved something else.**

It does, and the mechanism is one line of linear algebra. For a block whose rows
are `gᵢ = Σⱼ M[i][j]·uⱼ + kᵢ`, the adjugate identity

```text
adj(M) · (M·u + k)  =  det(M)·u + adj(M)·k
```

read one unknown at a time says

```text
det(M)·uⱼ  =  Sⱼ  +  Σᵢ adj(M)[j][i] · gᵢ            with  S = −adj(M)·k
```

That is *not* a substitution. It is an explicit statement that `det(M)·uⱼ` equals
a polynomial free of the unknowns **plus a combination of the original rows**,
with cofactors `adj(M)[j][i]` in the coefficient ring. Substituting it into the
target — and clearing the target's degree `d` in the block's unknowns with
`det(M)^d` — gives

```text
det(M)^d · target  =  residue  +  Σᵢ cofactorᵢ · gᵢ
```

where every `gᵢ` is a hypothesis polynomial the problem stated, unchanged.

### Dividing the multiplier out, inside the ideal

`det(M)^d` still has to go. It is divided out **through the Rabinowitsch
generator**, not symbolically. With `g = d·z − 1` we have `d·z = 1 + g`, so
`(d·z)ᴺ = (1 + g)ᴺ` and

```text
1  =  zᴺ·dᴺ  −  g · Σ_{i=1..N} C(N,i)·g^{i−1}
```

Multiplying the elimination identity by `zᴺ` and subtracting leaves cofactors for
the conclusion itself. For `N = 1` this collapses to the shape the Gröbner route
already produces on the six older saturated certificates — the saturation
generator's cofactor is minus the conclusion. `euler-line` has `N = 2`, so its
cofactor is `−conclusion·(1 + collinear(A,B,C)·Zinv0)`, and that exact polynomial
is asserted term-for-term by
`the_squared_multiplier_produces_the_expected_rabinowitsch_cofactor`. A binomial
series off by one term would fail there rather than in a prose claim.

### What makes this auditable rather than asserted

Three things, in order of how much they matter:

1. **The generator list is unchanged, and the checker enforces it.**
   `geometry_check::check_certificate`'s shape pass compares generator `i` against
   the stated hypothesis `i` and *rebuilds* the saturation generator from the
   declared condition. A route that had substituted solved forms would be rejected
   at that pass. There is now an explicit unit assertion of the same thing at the
   certifier, because it is the property the whole design rests on.
2. **The checker is untouched.** Not one line of `geometry_check.rs` changed. It
   knows about neither route — no monomial orders, no S-polynomials, and equally
   no adjugates. A second producer is exactly as untrusted as the first.
3. **The multiplier can only be divided by a *declared* condition.** If the
   determinant is not a product of the problem's stated conditions times a nonzero
   rational, the route returns `GeometryDecline::UndividableMultiplier` rather
   than inventing a side condition. This is the soundness-relevant half of the
   design and it is tested against Thales, where the elimination *does* clear the
   residue with a two-term multiplier that is nobody's declared condition
   (`a_multiplier_outside_the_stated_conditions_declines`).

The emitter is the independent read: **7 unchanged, 1 written.** Every certificate
that predates this lane re-serialises byte for byte.

---

## 3. Non-degeneracy, and a minimality proof that needs no budget at all

The condition is `abc-not-collinear`, `det(B−A, C−A) ≠ 0`, and it is a hypothesis
in the fact's `formal.statement`, not prose.

**The counterexample.** `A = B = (0,0)`, `C = (1,0)`, `O = (1/2,0)`, `H = (0,1)`.
With `A = B` the hypothesis `|OA| = |OB|` is vacuous, so `O` is pinned only to
`x = 1/2`; both perpendicularity hypotheses collapse to `hx = 0`, so `H` is pinned
only to `x = 0`. Every hypothesis holds, the condition vanishes, and `O`,
`G = (1/3,0)`, `H` form a genuine triangle. The checker replays it from the
artifact.

**The on-locus-but-harmless control**, which the previous lane had to build and
this lane had to extend. `A = B = (0,0)`, `C = (1,0)`, `O = (1/2,0)`, **`H = (0,0)`**
— one coordinate away from the counterexample. It violates `abc-not-collinear`
just as thoroughly, satisfies every hypothesis, and yet `O`, `G`, `H` all sit on
the x-axis, so the conclusion **holds**. Offering that as the counterexample is
rejected. Sitting on the degeneracy locus is not enough; a counterexample has to
falsify something.

That control had degraded silently, which is why it is now a table rather than a
constant. It was written for the quadrilateral coordinatisation, so it *skipped*
every triangle theorem — including `centroid-divides-medians`, which had been in
the corpus the whole time. The test now carries one configuration per
coordinatisation, tries each against each certificate, and **asserts full
coverage**, so the next promotion fails loudly instead of opting out. (It also
turned out one configuration covers three theorems: `A=(0,0)`, `B=(1,0)`,
`C=(2,0)`, `D=P=(1,0)` is collinear, the parallelogram's and rhombus's diagonals
behave, and `P` is simultaneously on both medians and equal to the centroid.)
Deleting the counterexample is rejected too, by the pre-existing control, now over
all four saturated certificates.

### ADR-0455, and why the answer here is *absolute*

ADR-0455 says a minimality claim is absolute only if every subset test was
**decided**, and budget-relative otherwise. For the six older facts,
`geometry_order_audit` established absoluteness by deciding every subset with the
Gröbner route. **That instrument does not exist for this theorem** — the whole
point is that its Gröbner reduction does not return — and the linear route cannot
substitute for it, because the multiplier it divides out is an artifact of the
decomposition it chose. A linear route could in principle consume a condition the
theorem does not need.

So the minimality is established a different way, and it is stronger than either:

> If a conclusion `c` lay in the ideal generated by the hypotheses together with
> `d·z − 1` for each `d` in a subset `S`, then `c` would vanish at every common
> zero of those generators. A configuration that satisfies every hypothesis, keeps
> every condition in `S` nonzero (so `z := 1/d` extends it), and **falsifies** a
> conclusion therefore refutes `S` outright.

The only proper subset of a one-element condition set is the empty one, and the
committed degenerate counterexample is exactly such a configuration. So
`euler-line`'s condition set is minimal **absolutely** — no budget, no monomial
order, and no algorithm anywhere in the argument. The certificate's own negative
control is the proof.

`every_used_condition_set_is_minimal_absolutely` states this for arbitrary subsets
so it keeps its force when a theorem needs two, and it runs over every committed
saturated certificate: **6 proper subsets refuted, 0 undecided.** This is a
cheaper and stronger instrument than the `2ⁿ` subset audit, and it is worth
noticing that the ledger already contained the evidence — it just had not been
read as a minimality proof.

---

## 4. Where the route does *not* work, measured

The linear route is not a replacement for the Gröbner one; the sweep says so
plainly. `cargo run -p axeyum-cas --release --example geometry_linear_route`:

| theorem | blocks found | multiplier | residue | outcome |
|---|---|---|---|---|
| `varignon-midpoint-parallelogram` | 0 | 1 | 0 | certifies (identical empty certificate) |
| `thales-right-angle-in-semicircle` | `{ax}` | 2 terms | 0 | **undividable multiplier** |
| `orthocentre-altitudes-concurrent` | `{ax,ay}` | 6 terms | 0 | **undividable multiplier** |
| `medians-concurrent` | `{ax,ay}` | 6 terms | 0 | **undividable multiplier** |
| `centroid-divides-medians` | `{ax,bx}` | 7 terms | 20 terms | **undividable multiplier** |
| `parallelogram-diagonals-bisect` | `{ax,bx}` | 7 terms | 20 terms | **undividable multiplier** |
| `rhombus-diagonals-perpendicular` | `{bx,by}` | 6 terms | 42 terms | **undividable multiplier** |
| **`euler-line`** | `{ox,oy}`, `{hx,hy}` | 21 terms | **0** | **certifies, 4–6 ms** |

The pattern is legible and it is the honest limitation. On those six the block
detector eliminates *vertex* coordinates — `ax`, `bx` — because the hypotheses
happen to be affine in them too, and the resulting determinant is a polynomial no
declined condition licenses. The route then refuses. That is the correct refusal:
dividing by it would prove the theorem only where some unnamed polynomial is
nonzero, which is precisely the hidden-hypothesis failure this whole domain exists
to prevent.

`euler-line` is different because its unknowns are *constructed points*, so its
determinant is the geometric non-degeneracy condition rather than an artifact.
That is the shape the route is for, and it is the shape Simson and Pappus have.

Consequently `certify_any_route` tries **linear first, then Gröbner**. The order
matters: with Gröbner first, `euler-line` would never reach the cheap route at
all. The order was checked the same way the `grevlex` switch was rather than
argued — six decline, Varignon produces the identical empty certificate, and the
emitter reports 7 unchanged.

---

## 5. Two things I would flag to the next reader

**The block detector is a heuristic, and it is allowed to be wrong.** It picks the
variables that occur in the *target* and are at most degree one in every
generator, groups them into connected components of the incidence graph, and takes
the largest nonsingular square subsystem in each. A block it misses costs reach; a
block it should not have chosen produces an identity that fails to check or an
elimination that returns `None`. Nothing about soundness rests on it, and
`a_hand_written_block_that_does_not_hold_is_refused` gives it a deliberately false
decomposition to confirm that.

The one trap inside it worth naming: **per-variable degree is not affineness**.
`x·y` has degree one in each variable and is quadratic in the pair, so the
extraction tests the *joint* degree over the block's unknowns. A detector that
used `degree_in` alone would happily build a 2×2 "linear" system out of `x·y − 1`
and produce a determinant that means nothing.

**The `frontier()` list is empty, and that is a queue rather than a result.** Both
remaining classical targets are dominated by linear constructions and are absent
only because nobody has written them down yet:

- **Simson's line.** Stated with the circumcircle as a *concyclicity determinant*
  rather than an explicit centre, it is 14 coordinates (A, B, C, P and the three
  feet), 7 hypotheses, and **three 2×2 blocks** — each foot satisfies
  `collinear(B,C,X)` and `(X−P)·(C−B) = 0`, both linear in `X`, with determinant
  `−|BC|²`. So it needs three conditions, `|AB|² ≠ 0`, `|BC|² ≠ 0`, `|CA|² ≠ 0`,
  and the residue reduces modulo a **single** remaining generator, which is
  multivariate division with no S-pairs at all. The real work is not the algebra:
  it is that `|BC|² ≠ 0` is **not** `B ≠ C` over an arbitrary field of
  characteristic zero (the isotropic directions over ℂ), so the fact would have to
  name the real-plane assumption in its footprint — a point the `geometry` lane
  already recorded and `squared_distance_vanishes_exactly_at_coincident_points`
  already measures. Three conditions also means three counterexamples and three
  on-locus-but-harmless controls, and those are what the coverage assertion in §3
  will now demand.
- **Pappus.** 18 coordinates, but the three intersection points are each pinned by
  two collinearity hypotheses that are linear in them — three 2×2 blocks again —
  and the residue reduces modulo the two collinearity constraints on the free
  points.

Both were gated on `euler-line` by the previous lane, deliberately and correctly.
The gate is open.

---

## Files

| path | what |
|---|---|
| `crates/axeyum-cas/src/linear_elim.rs` | the elimination engine: block detection, adjugate, cofactor-preserving substitution. Shares no code with `groebner_cert` |
| `crates/axeyum-cas/src/geometry_certify.rs` | `certify_by_linear_elimination`, the Rabinowitsch multiplier division, `certify_any_route` |
| `crates/axeyum-cas/src/geometry_corpus.rs` | `euler-line` promoted into `corpus()`; `frontier()` is empty and says why |
| `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs` | the on-locus control as a covered table, and the absolute-minimality proof |
| `crates/axeyum-cas/examples/geometry_linear_route.rs` | the like-for-like comparison against the S-pair ladder |
| `artifacts/geometry-certificates/euler-line.json` | the eighth certificate, 32 kB, 278 cofactor terms over 5 generators |
| `artifacts/facts/F-geometry-euler-line.json` | `F:geometry-euler-line`, `cas-certificate`, three evidence rows |

## The ranked next steps

1. **Simson, then Pappus**, in that order of size — the gate the previous lane set
   is open and the shape is right. Simson's real cost is the real-plane assumption
   its `|AB|² ≠ 0` conditions carry, not its coordinate count.
2. **Buchberger's criteria in `groebner_cert.rs`** — still worth it for the whole
   crate (92% of the rhombus's pairs reduce to zero), still **not** the thing that
   reaches a divergent theorem. The previous lane's counters stand.
3. **Teach the block detector to prefer determinants that divide a declared
   condition.** Six of the eight corpus theorems decline on a multiplier the route
   chose badly, and the information needed to choose better is right there in the
   problem. This is reach, not soundness.
4. **Audit and switch `Limits::fast()` / `ideal_limits()`** — unchanged from the
   previous lane's list, unchanged in priority.
5. **A surface syntax for the corpus** — open, recommended three times now.
