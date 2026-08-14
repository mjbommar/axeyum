# Diary — certified Euclidean geometry (lane `geometry`), 2026-08-14

A new domain on the `cas-certificate` route, unrelated to the combinatorics and
summation families already in the ledger. The machinery it needed already
existed: `crates/axeyum-cas/src/groebner_cert.rs` runs Buchberger while carrying
each polynomial's representation in the original generators and emits

```text
target = Σᵢ cofactorᵢ · generatorᵢ + remainder
```

which is a Nullstellensatz certificate, re-derivable with polynomial addition and
multiplication alone. What was missing was a **front end** — points as
coordinates, predicates as polynomials — and a **corpus**.

Both exist now, six theorems are certified and filed as facts, two are on a
measured frontier, and the headline finding is not the one I expected.

---

## 1. The headline: most of these theorems need no side condition at all

The task brief warned, correctly, that mechanised geometry proofs are notorious
for holding only on non-degenerate configurations, and that a proof silently
assuming non-degeneracy is wrong in the direction that *manufactures* theorems.
So the certifier was built to make that measurable rather than assumable: it
tries the **empty** non-degeneracy set first, then subsets in increasing size,
and the certificate records which conditions it actually consumed.

The measurement, over the committed corpus:

| theorem | conditions used | cofactors |
|---|---|---|
| Varignon's midpoint parallelogram | **none** | none — the conclusion is the zero polynomial |
| Thales, angle in a semicircle | **none** | the constant `+1` |
| altitudes concurrent (orthocentre) | **none** | the constants `−1, −1` |
| medians concurrent | **none** | the constants `−1, −1` |
| the medians meet at `(A+B+C)/3` | `abc-not-collinear` | degree 1, with `Zinv0` |
| parallelogram diagonals bisect | `abd-not-collinear` | degree 1, with `Zinv0` |

Four of six need nothing. Concurrency of the altitudes — the theorem whose
textbook statement always begins "in a triangle" — is, in the universally
quantified incidence form, the bare identity

```text
(P−C)·(B−A) + (P−A)·(C−B) + (P−B)·(A−C) = 0
```

valid for any four points of the plane, degenerate or not. Same for the medians.
Thales is the single identity `(A−C)·(B−C) = |C−O|² − |A−O|²` with `O` the
midpoint of `AB`, and it holds *on* the degeneracy locus, not merely off it: when
`A = B` the circle collapses to a point, the hypothesis forces `C = A = B`, and
the conclusion is true because the zero vector is orthogonal to everything.

**The rule the corpus actually exhibits** is sharper than "geometry needs
non-degeneracy". It is:

> A side condition is needed exactly when the theorem asserts something about a
> point the hypotheses are supposed to **pin down**. Incidence is free;
> *location* is not.

`medians-concurrent` and `centroid-divides-medians` are in the corpus adjacent to
each other, sharing their two hypotheses character for character (they are built
from one shared `median_hypotheses` helper, precisely so the difference cannot be
an accident of transcription). Only the conclusion differs — "P is on the third
median" versus "3P = A+B+C" — and only the second needs a condition. That pair is
the clearest statement of the finding I can make.

The corollary that matters for anyone reading a mechanised geometry claim: the
familiar non-degeneracy conditions attached to concurrency theorems are usually
conditions for the meeting point to **exist and be unique**, which is an
existence claim. The implication "on two ⟹ on the third" does not make it, and
should not be quoted as if it needed it.

---

## 2. The two counterexamples, and why they are mandatory

For each condition a certificate consumes, the corpus commits a
`DegenerateWitness` — exact rational coordinates that satisfy every hypothesis,
**annihilate** the condition, and **falsify** a conclusion. Both are checked from
the artifact, and a certificate whose counterexample fails to break the theorem
is *rejected*.

**`centroid-divides-medians` / `abc-not-collinear`.**
`A = (0,0)`, `B = (1,0)`, `C = (2,0)`, `P = (7,0)`.
The triangle is flat. `B` coincides with the midpoint of `CA`, so the second
hypothesis degenerates to `det(0, P−B) = 0` and is satisfied by every `P`; the
first pins `P` only to the x-axis. Then `3·P.x = 21` while `A.x+B.x+C.x = 3`. The
conclusion is off by 18.

**`parallelogram-diagonals-bisect` / `abd-not-collinear`.**
`A = (0,0)`, `B = (1,0)`, `C = (2,0)`, `D = (5,0)`.
Four collinear points: every direction is parallel to every other, so `AB ∥ DC`
and `BC ∥ AD` both hold vacuously. The midpoint of `AC` is `(1,0)`; the midpoint
of `BD` is `(3,0)`. They are not equal.

Two controls make these load-bearing rather than decorative, and both are tested:

- **Deleting** the counterexample from a certificate makes the checker reject it
  (`removing_the_degenerate_counterexample_is_rejected`).
- **Replacing** it with a configuration that violates the condition but does *not*
  break the theorem also rejects. There is a unit-level version of this too, at
  the certifier: `A=(0,0), B=(1,0), C=(2,0), D=(1,0)` is collinear, so it
  violates `abd-not-collinear`, but its diagonals do happen to bisect — and
  `certify` refuses to emit a certificate backed by it.

The second control is the one I would not have thought to write without the
brief's insistence. A counterexample that merely *sits on* the degeneracy locus
proves nothing; it has to falsify something.

---

## 3. How the side condition enters: Rabinowitsch, in the artifact

A condition `d ≠ 0` is admitted only by being named and turned into a generator

```text
d·z − 1        (z a fresh variable, `Zinv0`, `Zinv1`, …)
```

so the certificate reads `c = Σ uᵢ·hᵢ + w·(d·z − 1)`. Specialising `z := 1/d` —
legitimate **exactly** when `d ≠ 0` — kills the last term and leaves the theorem.
That is the whole role of the condition, and it is the only place it enters.

The saturated certificates come out in the signature Rabinowitsch shape: the
cofactor of the saturation generator is minus the conclusion itself. For the
parallelogram, in full, with `Zinv0` inverting `collinear(A,B,D)`:

```text
conclusion  =  ½(Zinv0·D.x − Zinv0·A.x)·(AB ∥ DC)
             + ½(Zinv0·B.x − Zinv0·A.x)·(BC ∥ AD)
             + ½(B.x − A.x + D.x − C.x)·(collinear(A,B,D)·Zinv0 − 1)
```

Sixteen monomials across all cofactors for the whole theorem. These artifacts are
small enough to read.

**Why saturation is the right variety.** The set of configurations the theorem is
about is the hypothesis variety **minus** the degeneracy locus — the complement
of `V(d)` inside `V(h₁,…,hₙ)`. Its coordinate ring is the localisation at `d`, and
`ideal(h₁,…,hₙ, d·z−1) ∩ ℚ[coordinates]` is exactly the saturation
`(h₁,…,hₙ) : d^∞`. So membership in the saturated ideal is membership in the ideal
of functions vanishing on precisely the configurations claimed, and nothing
weaker or stronger. The alternative — adding `d ≠ 0` to a real-arithmetic solver
— would be a different (and, here, much harder) problem.

---

## 4. The certificate format

`artifacts/geometry-certificates/*.json`, six files, 26 kB in total. Following
the pattern the sibling `telescoping-scale` lane established: rationals are
`[numerator, denominator]` integer pairs, **decimals are refused by the reader**,
polynomials serialise in `MvPoly`'s canonical term order so a regeneration of
unchanged content produces an identical file. The codec
(`crates/axeyum-cas/src/geometry_json.rs`) is hand-rolled and dependency-free; it
is a second implementation of the same conventions as `telescoping_json.rs`, not
a shared one.

Each file carries: the statement in prose, the coordinate gloss (`ax` ↦ `A.x`),
the hypotheses as named polynomials, the saturations (condition id, prose, the
inverse variable, the condition polynomial), the generator list, one conclusion
block per conclusion with its cofactor vector, the degenerate counterexamples,
and the non-degenerate sanity configurations.

Two programs share no derivation:

- `examples/emit_geometry_certificates.rs` writes a file **only after** the
  independent checker has accepted it, and only when the bytes differ.
- `tests/geometry_certificate_artifacts.rs` reads every committed file and
  re-checks it. **Nothing in that path calls the certifier.**

---

## 5. What "independent" means here, precisely

`geometry_check.rs` shares no code with the search. The search is Buchberger with
cofactor tracking (`groebner.rs`, `groebner_cert.rs`); the checker touches
neither, and knows nothing about monomial orders, S-polynomials or bases. Both
share `MvPoly`, the crate's exact-rational polynomial arithmetic — that is the
trusted core, and it is named in every footprint as
`cas.exact-rational-polynomial-normal-form`.

The checker runs five passes, in this order, and each is a distinct kind of check:

1. **Shape.** The saturation generators are *rebuilt* here as `d·z − 1` from the
   condition polynomial the file declares, and compared against the generator the
   cofactors are actually taken against. Without this a certificate could
   advertise a weak side condition and use a strong one.
2. **The identity, symbolically.** `Σ uᵢ·gᵢ` expanded and compared to the
   conclusion, in canonical normal form, so the comparison is decisive.
3. **The identity, numerically.** The same identity re-evaluated at 24
   deterministic integer points through `MvPoly::evaluate` — a different code
   path from the symbolic expansion, so agreement is a cross-check rather than a
   restatement.
4. **Usage.** Every declared saturation must carry a nonzero cofactor somewhere,
   or the certificate is advertising a weaker theorem than it proved.
5. **The configurations.** Every degenerate counterexample and every generic
   witness replayed at exact rational coordinates.

Passes 4 and 5 are the ones specific to this domain. They are what stop the route
from manufacturing theorems that hold only off a degeneracy locus.

### The coordinatisation is attacked from outside

Nothing in a polynomial identity can tell you that `det(B−A, C−A)` *means*
collinearity. That link is the coordinatisation, and it is the one assumption
here that no amount of exact arithmetic verifies — so it is checked against a
second implementation instead.

`crates/axeyum-cas/src/geometry.rs` is a separate, older module that decides the
same predicates at concrete rational coordinates, written against `ax+by+c = 0`
line normals and a cross-product helper rather than against `MvPoly`.
`tests/geometry_encoding_agreement.rs` makes the two decide the same questions
over 244 integer configurations, opening with hand-picked degenerate shapes (two
coincident points, four collinear points, four collinear vertical points, all
four coincident) because that is where two encodings of one predicate part
company. All six predicates agree:

| polynomial | second implementation |
|---|---|
| `collinear` | `Point::collinear` (cross product) |
| `parallel` | `Line::is_parallel` (proportional normals) |
| `perpendicular` | `Line::is_perpendicular` (orthogonal normals) |
| `midpoint` | `Point::midpoint` |
| `equidistant` | `Point::distance` equality — **exact surds** through `simplify_radicals` over `CasExpr`, a completely different route from the squared-distance polynomial |
| `dist_sq = 0` | coincidence of the two points |

The parallelism row is the instructive one. When two points coincide, the older
module refuses to call the segment a line at all, while the determinant vanishes
because the zero vector is parallel to everything. The test asserts that this is
the **only** way the two can differ, rather than skipping the case — and it is
exactly the configuration class both counterexamples live in.

---

## 6. Two frontier theorems, measured rather than guessed

`geometry_corpus::frontier()` keeps two correctly-stated theorems the route does
not reach. They stay in the tree because a measured limit is only worth having if
it is reproducible: `cargo run -p axeyum-cas --release --example geometry_probe 1
<id>` re-derives each decline, and their witnesses are still checked by a unit
test, so they are unproved rather than unchecked.

| theorem | coords | conditions | outcome |
|---|---|---|---|
| `rhombus-diagonals-perpendicular` | 8 | none | 4.6–8.9 s, correctly reports a nonzero remainder |
| `rhombus-diagonals-perpendicular` | 8 | `abd-not-collinear` | **declined after 247–365 s** |
| `rhombus-diagonals-perpendicular` | 8 | `abd-not-collinear`, **untracked** | no verdict in > 12 min |
| `euler-line` | 10 | none | no verdict within 600 s |

For contrast, everything in the committed corpus decides in **under 250 ms**, and
the whole certification run is 176 ms wall.

The rhombus differs from the parallelogram by exactly one extra hypothesis — the
quadratic `|AB| = |BC|` — and that one generator moves the reduction from 197 ms
to a decline three orders of magnitude later. Euler's line adds two more
coordinates and two more quadratic hypotheses and does not return at all.

### What actually fails, as far as I established it

I instrumented the probe to run the *same* ideal-membership question **without**
cofactor tracking, through `axeyum_cas::ideal_contains`. On the rhombus's
empty-condition attempt the two agree to within noise (4.6 s tracked, 4.6 s
untracked), which says the expense is the **Gröbner basis itself**, not the
representation carried alongside it. So this is not the same wall the
`telescoping-scale` lane hit.

**That distinction matters and I want to be precise about what I did and did not
establish.** The saturated rhombus run declined after 247 s under
`geometry_limits` (`reduction_steps 50 000`, `pair_iterations 2 000`,
`basis_size 200`, `poly_terms 8 000`), so *some* ceiling tripped — but
`groebner_cert` returns a bare `CofactorOutcome::Declined` for a tripped ceiling
and for an `i128` overflow alike, and I did **not** separate the two. The
untracked comparison for that case had not finished when this was written. So:

- **Established:** the plain-ideal question is already seconds-expensive at 8
  coordinates and 3 quadratic generators, and cofactor tracking is not what makes
  it so.
- **Established after the first draft of this note:** the *untracked* saturated
  rhombus, running under `groebner.rs`'s own far more generous fixed caps
  (`1e6` reduction steps, `5e6` pairs, `1e5` basis elements), produced **no
  verdict in over twelve minutes** — three times longer than the tracked run
  spent before its ceiling tripped. So the basis computation itself is the
  expense, and the tracked decline at 247 s is a budget ceiling reached while
  doing genuinely enormous work, not an early arithmetic failure.
- **Still not established:** whether an `i128` coefficient overflow in `MvPoly`
  *also* occurs somewhere in that computation. `CofactorOutcome::Declined` is one
  value for a tripped ceiling and for an overflow alike, so the question cannot be
  answered from the outside. Reporting it either way would be a guess, and the
  sibling lane's precedent is that this exact guess is worth measuring properly —
  which is why splitting `Declined` into two reasons is ranked second below.

The structural suspect is the **monomial order**. This crate uses pure
lexicographic order everywhere (`groebner.rs`, module docs), which is the order
with the worst complexity for computing a basis and the best for elimination —
and ideal *membership* needs no elimination at all. A degree-reverse-lexicographic
order is the standard remedy and is routinely orders of magnitude faster on
systems of exactly this shape. Adding one is a change to `groebner.rs`, which the
rest of the crate depends on, so this lane did not make it at the end of its own
work.

Two smaller things I did try:

- **Variable order.** Naming the constructed/unknown points so they rank above or
  below the free vertices under `lex` (`'d' < 'u'` versus `'a' < 'z'`) changed the
  fast cases by a factor of about two and did not move the frontier cases at all.
  Not the binding constraint.
- **The inverse variables** are named `Zinv0`, `Zinv1`, … deliberately: `'Z' < 'a'`
  as bytes, so they rank above every coordinate and are eliminated first. This is
  a performance choice only; membership does not depend on the order.

### Not attempted, and why

**Frame normalisation.** Placing `A` at the origin and `B` on the x-axis removes
three coordinates and would very likely bring Euler's line into range. I did not
do it, because it buys the reduction at the cost of an extra assumption — that
every predicate involved is invariant under the rigid motion taking a generic
`(A,B)` to `((0,0),(u,0))` — and that assumption is *about the degenerate case*,
since the motion does not exist when `A = B`. Trading a soundness-relevant
hypothesis for a speedup, in the one domain whose characteristic failure is
exactly a hidden hypothesis, is the wrong trade. Everything in this corpus is
stated in **fully generic coordinates**: every point is two free indeterminates,
no WLOG anywhere.

**Simson's line and Pappus** were scoped and not attempted. Simson needs 16
coordinates and about 11 hypotheses, Pappus 18 coordinates; the Euler measurement
above puts both far outside what this route reaches today.

---

## 7. Design notes worth keeping

**`A ≠ B` as a polynomial condition.** The corpus never uses one, but the front
end has `dist_sq`, and if a condition `|AB|² ≠ 0` is ever used, it is *not* the
same as `A ≠ B` over an arbitrary field of characteristic zero: over ℂ there are
distinct points with vanishing squared distance (the isotropic directions). Over
ℝ they coincide, and `squared_distance_vanishes_exactly_at_coincident_points`
measures that rather than remarking on it. Any future fact using such a condition
must name the real-plane assumption in its footprint.

**Constructed points cost nothing.** A `Pt` holds two arbitrary polynomials, not
two variables, so a midpoint or a centroid is carried out in the coefficient
field instead of being asserted as two extra equations over two extra variables.
For `centroid-divides-medians` that is the difference between 8 coordinates and
12.

**`Constraint` and `Condition` are separate types** that hold the same data.
Confusing "must vanish" with "must not vanish" is the mistake this whole module
exists to make impossible, so the type system is asked to help.

**The minimality claim is scoped.** `certify` reports the smallest condition
subset **among those the budget decided**; a subset that declines is skipped. That
direction is conservative — a certificate using a condition it did not need proves
a weaker theorem — and the identity is independently checked either way. The
dangerous direction cannot arise: claiming no condition is needed requires the
empty-subset reduction to produce an identity the checker then re-derives.

---

## 8. Six facts

All on `proof_route: cas-certificate`, all `epistemic_status: proved`,
`external_status: proved` (these are classical), `validate-facts.py` at 0 errors,
and every `checker_command` replays in about a second.

| fact | conditions |
|---|---|
| `F:geometry-varignon-midpoint-parallelogram` | — |
| `F:geometry-thales-right-angle-in-semicircle` | — |
| `F:geometry-orthocentre-altitudes-concurrent` | — |
| `F:geometry-medians-concurrent` | — |
| `F:geometry-centroid-divides-medians` | `abc-not-collinear` |
| `F:geometry-parallelogram-diagonals-bisect` | `abd-not-collinear` |

`formal.language` is `smtlib2` with `fragment: NRA`, not `cas-term`. The
statements really are first-order sentences over the reals — quantified,
polynomial, with the non-degeneracy conditions as explicit `(not (= … 0.0))`
antecedents — so writing them that way is both faithful and machine-readable.
`cas-term` is documented as a `HyperTerm` summation specification and would have
been a mislabel. No fragment we have decides `NRA`; the certificate is what
settles them, which is exactly the situation `proof_route` exists to record.

New axiom names, used where they apply:

- `geometry.cartesian-coordinatisation-of-the-euclidean-plane` — points are pairs
  of reals and each named predicate is the stated polynomial. The assumption
  attacked in §5.
- `geometry.characteristic-zero-specialisation` — an identity in `ℚ[vars]` holds
  at every tuple of values in any field of characteristic zero, ℝ included.
- `geometry.rabinowitsch-inverse-specialisation` — substituting `z := 1/d` in the
  identity, valid exactly off the degeneracy locus. **Only** on the two saturated
  facts.
- `geometry.nondegeneracy.<condition-id>` — one per condition consumed. These also
  appear as hypotheses in `formal.statement`; they are duplicated into the
  footprint deliberately, because the footprint is the field a reader scans to see
  what a proof rests on, and a side condition invisible there is precisely how a
  mechanised geometry proof comes to be quoted as unconditional.

`cas.exact-rational-polynomial-normal-form` is reused from the telescoping lane —
it is the same trusted `MvPoly` core.

---

## Files

| path | what |
|---|---|
| `crates/axeyum-cas/src/geometry_certify.rs` | the front end (points, predicates, constructions) and the certifier; untrusted |
| `crates/axeyum-cas/src/geometry_check.rs` | the independent re-derivation; shares no code with Buchberger |
| `crates/axeyum-cas/src/geometry_json.rs` | the deterministic codec, decimals refused |
| `crates/axeyum-cas/src/geometry_corpus.rs` | the eight stated theorems, six reached and two on the frontier |
| `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs` | re-checks every committed certificate from the file, plus 8 tamper controls |
| `crates/axeyum-cas/tests/geometry_encoding_agreement.rs` | the coordinatisation control against `geometry.rs` |
| `crates/axeyum-cas/examples/emit_geometry_certificates.rs` | regenerates the artifacts, checker-gated |
| `crates/axeyum-cas/examples/geometry_probe.rs` | the per-subset cost measurement, tracked and untracked |
| `artifacts/geometry-certificates/*.json` | six certificates, the evidence itself |
| `artifacts/facts/F-geometry-*.json` | six facts |

## The ranked next steps

1. **A degree-reverse-lexicographic monomial order in `groebner.rs`.** The single
   change most likely to move the frontier, and it helps every consumer of
   Gröbner bases in the crate, not just geometry. Ideal membership needs no
   elimination, so nothing here wants `lex`.
2. **Separate a tripped ceiling from an `i128` overflow in
   `CofactorOutcome::Declined`.** Right now they are the same value, which is why
   §6 has to say "not established" about the rhombus. A two-variant decline
   reason would have made that measurement free — and it is the same distinction
   the `telescoping-scale` lane needed for `MvPoly::gcd`.
3. **Then re-attempt Euler's line, Simson's line and Pappus**, in that order of
   size, and record whichever still declines.
4. **A surface syntax for the corpus.** The same recommendation the telescoping
   lane left open, with the same obvious target: emit a `GeometryProblem`, not a
   Rust value.
