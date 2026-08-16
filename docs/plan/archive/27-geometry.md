# Lane: geometry (certified Euclidean geometry on the `cas-certificate` route)

<!-- plan-section: lane-status -->

**New domain, opened 2026-08-14.** The certifier already existed —
`groebner_cert.rs` emits `target = Σ cofactorᵢ·generatorᵢ + remainder`, which is a
Nullstellensatz certificate — so this lane built the two missing halves: a
**coordinatisation front end** (points as symbolic coordinate pairs; collinear,
parallel, perpendicular, equidistant, midpoint, centroid as polynomials) and a
**corpus**. Six theorems certified and filed as facts, two on a measured
frontier, `validate-facts.py` at 0 errors.

**The headline finding is not the expected one.** The brief warned, correctly,
that a mechanised geometry proof silently assuming non-degeneracy is wrong in the
direction that manufactures theorems — so the certifier tries the **empty**
condition set first and records what it consumed, making the question measured
rather than assumed. **Four of six theorems need no side condition at all.**
Concurrency of the altitudes, the theorem whose textbook statement always begins
"in a triangle", is in the universally quantified incidence form the bare identity
`(P−C)·(B−A) + (P−A)·(C−B) + (P−B)·(A−C) = 0`, with constant cofactors `(−1,−1)`,
valid for any four points. Same for the medians. Thales is the single identity
`(A−C)·(B−C) = |C−O|² − |A−O|²` and is true *on* the degeneracy locus, not merely
off it.

The rule the corpus exhibits is sharper than "geometry needs non-degeneracy":
**a side condition is needed exactly when the theorem locates a point the
hypotheses are supposed to pin down; incidence is free, location is not.**
`medians-concurrent` and `centroid-divides-medians` sit adjacent in the corpus and
share their two hypotheses character for character (one shared helper builds
both); only the conclusion differs, and only the second needs a condition.

**Non-degeneracy is explicit, saturated, and broken by a committed
counterexample.** A condition `d ≠ 0` is admitted only via Rabinowitsch — a fresh
variable and the generator `d·z − 1` — so it is visible in the artifact, and
`ideal(h, d·z−1) ∩ ℚ[coords]` is exactly the saturation `(h) : d^∞`, the ideal of
the configurations actually claimed. Both conditions used carry exact rational
counterexamples: `A=(0,0), B=(1,0), C=(2,0), P=(7,0)` satisfies both median
hypotheses (`B` is the midpoint of `CA`, so one becomes vacuous) while `3P.x = 21`
against `A.x+B.x+C.x = 3`; and `A=(0,0), B=(1,0), C=(2,0), D=(5,0)` satisfies both
parallelism hypotheses while the diagonal midpoints are `(1,0)` and `(3,0)`. Two
controls keep these load-bearing: **deleting** a counterexample rejects, and
**replacing** it with a configuration that violates the condition but fails to
break the theorem also rejects.

**Everything is in fully generic coordinates** — every point two free
indeterminates, no WLOG frame anywhere. Frame normalisation would have brought
Euler's line into range and was deliberately not used: it buys the reduction with
an invariance assumption about exactly the degenerate case, which is the wrong
trade in the one domain whose characteristic failure is a hidden hypothesis.

**Evidence.** `artifacts/geometry-certificates/*.json` (six files, 26 kB,
readable), written by a checker-gated emitter and re-checked **from the file** by
a suite that never calls the certifier. `geometry_check.rs` shares no code with
Buchberger and runs five passes: rebuild the saturation generators and compare
them with the ones the cofactors are taken against; expand the identity
symbolically; re-evaluate it at 24 integer points through a different code path;
require every declared condition to carry a nonzero cofactor; replay every
degenerate and generic configuration. The **coordinatisation** — the one
assumption exact arithmetic cannot verify — is attacked from outside by
`tests/geometry_encoding_agreement.rs`, which makes the older concrete
`geometry.rs` decide the same six predicates over 244 integer configurations,
opening with the degenerate shapes; the equidistance row goes through exact surds
in `CasExpr`, a completely different route.

**The frontier, measured.** `rhombus-diagonals-perpendicular` (one extra
quadratic hypothesis beyond the parallelogram) declines after 247–365 s;
`euler-line` returns no verdict in 600 s. Everything in the corpus decides under
250 ms. Instrumenting the probe to ask the same question **without** cofactor
tracking gives the same 4.6 s on the rhombus's empty-condition attempt, so the
expense is the Gröbner basis itself, not the representation carried alongside —
this is **not** the `MvPoly::gcd` wall the `telescoping-scale` lane hit. Stated
honestly: whether the saturated rhombus decline is a tripped ceiling or an `i128`
overflow is **not** established, because `CofactorOutcome::Declined` is one value
for both. The structural suspect is the **pure lexicographic monomial order** this
crate uses everywhere — the worst order for computing a basis, the best for
elimination, and ideal membership needs no elimination.

**Next, ranked.** (1) A degree-reverse-lexicographic order in `groebner.rs` — the
single change most likely to move the frontier, and it helps every consumer of
Gröbner bases in the crate. (2) Split `Declined` into ceiling-vs-overflow, the
same distinction `telescoping-scale` needed for `MvPoly::gcd`. (3) Re-attempt
Euler's line, then Simson's line (16 coordinates), then Pappus (18). (4) A surface
syntax emitting a `GeometryProblem`.

Full write-up:
[`docs/mathematics-2026-08/diary-geometry.md`](../../mathematics-2026-08/diary-geometry.md).

<!-- plan-section: landed-changes -->

| 2026-08-14 | `geometry` | new domain on the `cas-certificate` route: coordinatisation front end + Rabinowitsch saturation + independent checker; 6 classical theorems certified with committed degenerate counterexamples for every side condition used; measured that 4 of 6 need NO non-degeneracy condition; 2 frontier theorems recorded with timings; 6 new facts | `crates/axeyum-cas/src/geometry_certify.rs`, `crates/axeyum-cas/src/geometry_check.rs`, `crates/axeyum-cas/src/geometry_json.rs`, `crates/axeyum-cas/src/geometry_corpus.rs`, `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs`, `crates/axeyum-cas/tests/geometry_encoding_agreement.rs`, `crates/axeyum-cas/examples/emit_geometry_certificates.rs`, `crates/axeyum-cas/examples/geometry_probe.rs`, `artifacts/geometry-certificates/*.json`, `artifacts/facts/F-geometry-*.json` |
