# Diary — linear elimination, and `euler-line` (lane `euler-linearity`), 2026-08-15

The previous lane left a diagnosis it did not act on:

> All four hypotheses are **linear in `ox, oy, hx, hy`** over `ℚ[ax..cy]` —
> Buchberger is being asked to rediscover Cramer's rule by monomial reduction.

It is right, and acting on it takes `euler-line` from *does not return in 27
minutes* to a **checked certificate in 4–6 ms**. The corpus is eight theorems and
the certificate is in the original generators. The same route then reached
**Pappus** too — and Pappus is still on the frontier, for a reason that turned out
to be the more interesting finding (§6).

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
saturated certificate: **4 proper subsets refuted, 0 undecided** — four saturated
certificates, each using exactly one condition, so each with exactly one proper
subset. The count is asserted against that arithmetic rather than written down,
because a hand-written total is how a gate stops measuring what it claims to. This is a
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

**The `frontier()` list is not empty, and the entry on it is the interesting
part of this session.** I stated **Pappus's hexagon theorem** — 18 coordinates,
8 hypotheses, 3 conditions — and measured it, and the result was not the one I
expected.

---

## 6. Pappus: the route reaches it, and it is still on the frontier

`cargo run -p axeyum-cas --release --example geometry_linear_route -- pappus-hexagon`:

```text
blocks=3  multiplier=468 terms, degree 6  residue=720 terms
    block [xx,xy] rows [2,3]  det = 8 terms
    block [yx,yy] rows [4,5]  det = 8 terms
    block [zx,zy] rows [6,7]  det = 8 terms
    handover over the 2 unconsumed generators: 1 S-pair, basis 2, residue in the ideal
CERTIFIED in 292 s, conditions = all three, 3583 cofactor terms, checker verified
```

Three 2×2 blocks, exactly as the shape predicted: `X` is pinned by
`collinear(A,E,X)` and `collinear(B,D,X)`, both linear in `X`, and the determinant
is `det(E−A, D−B)` — the theorem's own first non-degeneracy condition. The
multiplier is the product of the three, and the three declared conditions divide
it exactly. **The independent checker accepts the certificate.**

### The narrowing that made it work, and why it is not an optimisation

The first attempt did not return. The handover was reducing the 720-term residue
against **all eight** hypotheses — six of which the blocks had just consumed, and
every one of which mentions a variable the residue no longer contains. Reduced
against the two the blocks did not touch, it is a **one-S-pair** question.

That fix alone was not enough either: the subset search adds the Rabinowitsch
generators `d·z − 1` to the reduction, and three fresh variables in three
degree-3 generators is close to the worst input `Buchberger`'s algorithm can be
handed. So the handover is now two passes — unconsumed *hypotheses* first,
unconsumed *generators* only if that fails — on the observation that the
saturation generators are what the **multiplier** needs, not what the residue
needs. With both changes the search finishes; with either missing it does not.

Neither change touches the seven older certificates: the emitter reports **0
written, 8 unchanged** afterwards.

### Why it is still on the frontier

Not reach. **Counterexamples.**

This corpus requires one exact rational configuration per condition a certificate
consumes: satisfying every hypothesis, annihilating *that* condition, and
falsifying a conclusion. Pappus has one for the condition set **as a whole** — six
points on the x-axis makes every incidence hypothesis vacuous and leaves `X`, `Y`,
`Z` free to be a triangle — and I could not find one that isolates a single
condition. Three attempts, each collapsing for a different reason, all through the
same mechanism:

- `AE ∥ BD` with the lines distinct: no `X` exists at all, so the configuration
  does not satisfy the hypotheses and is not a witness.
- `AE = BD` as lines, so `X` is free along it: that forces `A, B, D, E` collinear,
  hence the second carrier line equals the first, hence *every* condition vanishes
  too.
- `A = E`, so `collinear(A,E,X)` is vacuous and `X` is free along `BD`: the other
  two conditions do survive — but line `AF` becomes the second carrier, so `Y = D`,
  and line `CE` becomes the first, so `Z = B`, and `X` is already on line
  `BD = ZY`. The conclusion holds identically.

Killing one intersection forces the two *other* constructed points onto the very
line the freed point is confined to. Whether that is a theorem or an accident of
three attempts I do not know, and saying so is the honest report.

The consequence is exactly ADR-0455's distinction, arriving from the other side.
Pappus's condition set would be minimal only **budget-relative**: the empty subset
is refuted by the committed counterexample, and the size-1 and size-2 subsets are
*undecided*. `every_used_condition_set_is_minimal_absolutely` enumerates every
proper subset and refuses that — so the ratchet §3 introduced blocked the very
next theorem, which is the strongest evidence I have that it is set where it
should be. Filing Pappus with three conditions and a note nobody reads is what it
prevents.

So the decision is stated rather than made. The next lane either finds a
configuration isolating a single condition (or a smaller condition set), **or**
relaxes the ratchet to a named, justified exception and writes a fact whose
`notes` say the minimality is budget-relative — which ADR-0455 explicitly permits
when warranted. What it forbids is making the strong claim by default.

Pappus is committed as a `frontier()` entry with its witnesses replayed, so it is
*stated and checked* rather than described, and the measurement above is
reproducible.

### Simson, unattempted, with the wrinkle named

Stated with the circumcircle as a **concyclicity determinant** rather than an
explicit centre, Simson is 14 coordinates (A, B, C, P and three feet), 7
hypotheses, and three 2×2 blocks again — each foot satisfies `collinear(B,C,X)`
and `(X−P)·(C−B) = 0`, both linear in `X`, with determinant `−|BC|²`. The residue
would reduce modulo a **single** remaining generator. The algebra is easier than
Pappus's.

Its extra wrinkle is one the `geometry` lane already recorded: `|BC|² ≠ 0` is
**not** `B ≠ C` over an arbitrary field of characteristic zero, because of the
isotropic directions over ℂ. Over ℚ the two coincide — which is precisely the
problem, since the configurations that would witness the necessity of `|BC|² ≠ 0`
are *not rational*, and `DegenerateWitness` holds exact rationals. Stating Simson
honestly needs either a witness type over a quadratic extension, or a fact naming
the real-plane assumption in its footprint and saying what that costs. That is a
different kind of work from anything in this session, and guessing at it would
have been worse than leaving it named.

---

## Files

| path | what |
|---|---|
| `crates/axeyum-cas/src/linear_elim.rs` | the elimination engine: block detection, adjugate, cofactor-preserving substitution. Shares no code with `groebner_cert` |
| `crates/axeyum-cas/src/geometry_certify.rs` | `certify_by_linear_elimination`, the Rabinowitsch multiplier division, `certify_any_route` |
| `crates/axeyum-cas/src/geometry_corpus.rs` | `euler-line` promoted into `corpus()`; `pappus-hexagon` stated on `frontier()` with the measurement and the blocker |
| `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs` | the on-locus control as a covered table, and the absolute-minimality proof |
| `crates/axeyum-cas/examples/geometry_linear_route.rs` | the like-for-like comparison against the S-pair ladder |
| `artifacts/geometry-certificates/euler-line.json` | the eighth certificate, 32 kB, 278 cofactor terms over 5 generators |
| `artifacts/facts/F-geometry-euler-line.json` | `F:geometry-euler-line`, `cas-certificate`, three evidence rows |

## The ranked next steps

1. **Decide what to do about Pappus**, which is certified and unfiled. Either
   isolate a single condition with a rational configuration (or find a smaller
   condition set), or relax `every_used_condition_set_is_minimal_absolutely` to a
   named exception and write a budget-relative fact. This is the highest-value
   item because it is a decision about the ledger's honesty rules, not a
   computation, and the computation is already done.
2. **Simson**, whose algebra is easier than Pappus's and whose real cost is the
   real-plane assumption its `|AB|² ≠ 0` conditions carry — see §6.
3. **Buchberger's criteria in `groebner_cert.rs`** — still worth it for the whole
   crate (92% of the rhombus's pairs reduce to zero), still **not** the thing that
   reaches a divergent theorem. The previous lane's counters stand.
4. **Teach the block detector to prefer determinants that divide a declared
   condition.** Six of the eight corpus theorems decline on a multiplier the route
   chose badly, and the information needed to choose better is right there in the
   problem. This is reach, not soundness.
5. **Audit and switch `Limits::fast()` / `ideal_limits()`** — unchanged from the
   previous lane's list, unchanged in priority.
6. **A surface syntax for the corpus** — open, recommended three times now.
