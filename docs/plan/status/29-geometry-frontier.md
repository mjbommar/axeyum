# Lane: geometry-frontier (the monomial-order decision, the rhombus, and `euler-line`)

<!-- plan-section: lane-status -->

**Continuation lane, 2026-08-15.** `mvpoly-bignum` measured that
degree-reverse-lex reaches a frontier theorem and then deliberately left the
default alone, because `certify` returns the certificate for the *smallest
condition subset that succeeds* — so a faster order can change **which
non-degeneracy conditions a certificate uses**, and those conditions are
hypotheses in six proved facts' `formal.statement`. This lane took that decision
with the evidence it requires.

**(1) `geometry_limits()` is now `DegRevLex`, and no fact's claim moved.** The
new `geometry_order_audit` example runs **every** condition subset of every corpus
theorem under both orders, then runs the full `certify` under both and compares
the condition set *and the serialized certificate byte for byte*: **six condition
sets unchanged, zero moved, six certificates byte-identical**. The emitter agrees
independently — after the switch it reported *6 unchanged, 1 written*, the one
being the newly reachable rhombus. Not a byte of existing evidence changed.

**The audit proved something stronger than "nothing moved."** For all six, under
both orders, every subset is **decided** (`in ideal` / `not in ideal`), never
declined. Ideal membership does not depend on the order — only whether a verdict is
reached inside the ceilings does — so once every subset is decided, the reported
condition set is smallest **absolutely**. That discharges the qualifier the
`geometry` lane was careful to attach ("smallest among the subsets the budget
decided"). Had any subset declined, the honest move would have been to leave the
default alone. Scope was kept deliberate: `Limits::fast()` and the solver's
`ideal_limits()` still say `Lex`, because the same audit has not been run on their
corpus.

**(2) `rhombus-diagonals-perpendicular` is promoted — the seventh certified
theorem.** `{}` decided *not in ideal* in 0.9 s and `{abd-not-collinear}` *in
ideal* in 25.0 s (under `lex`: 5.1 s and a `ReductionSteps` decline after
301.8 s), 34 cofactor terms, 8.7 kB certificate, and the cofactor of the
saturation generator is exactly minus the conclusion — the signature Rabinowitsch
shape, verified term-for-term from the committed file. Both subsets are decided
under `grevlex`, so its condition set is absolutely minimal too; under `lex` they
are not, which is why the audit now reports that row as `REACH ONLY` rather than
`MOVED` — one order certifies and the other does not, so the failing order's
condition set is *unknown* rather than different and there is nothing to compare.
Headroom on every ceiling axis is 3–9×: 253 S-pairs of
2 000, basis 23 of 200, widest polynomial 1 678 of 8 000, 15 788 reduction steps
of 50 000. `F:geometry-rhombus-diagonals-perpendicular`, `validate-facts.py` 83
facts / 0 errors.

Non-degeneracy is treated in full, and one control had to be **built** rather than
inherited. The saturation controls ran against `first()` — the alphabetically
first saturated certificate — so a newly promoted theorem would have inherited the
*claim* that its counterexample is load-bearing without inheriting the test; they
now iterate over every saturated certificate and assert there are at least two.
And the "violates the condition but does not break the theorem" control was
sharpened: the pre-existing version substituted a *generic* configuration, which
fails on two counts at once and would pass a checker that only tested one.
`A=(0,0), B=(1,0), C=(2,0), D=(1,0)` is collinear — so the condition genuinely
fails — and the diagonals of both the parallelogram and the rhombus still behave;
the test asserts both halves before tampering. Separately, the fact's SMT-LIB
`formal.statement` was cross-evaluated against the certificate's own polynomials
at 300 random rational configurations (1 500 comparisons, 0 mismatches), because
prose review does not catch a transposed sign.

**(3) `euler-line` stays on the frontier, but is no longer described by a
stopwatch.** "No verdict in 600 s" and "no verdict in 1200 s" name no obstruction.
The new `geometry_obstruction` example runs the reduction under a **ladder** of
S-pair ceilings and reports the new `ReductionStats` at each rung, with the
rhombus — which finishes — as the control:

- **Not width.** At 65 S-pairs the rhombus is carrying a **733**-monomial
  polynomial against `euler-line`'s **477**, and finishes at 1 678. Not an
  overflow either; nothing here reported one, and the rhombus decline was
  `ReductionSteps`. Widening `MvPoly` past `i128` would not move this theorem.
- **It is basis growth and the quadratic backlog it creates.** The rhombus's basis
  **saturates at 23 by pair 65** and its queue drains at pair 253, where it
  completes. `euler-line`'s basis is 33 at pair 65 and still climbing ~1 element
  per 2 pairs; each new element queues a pair against every existing one, so 65
  processed leaves **528** outstanding and the ratio is worsening. The `lex` run
  reached one rung further and states it without needing a comparison: going from
  65 to 129 pairs **tripled** the backlog (1 081 → 3 403), added 36 basis elements
  (47 → 83) and cost **ten times** the wall clock (65.0 s → 635.4 s). The order
  changes the constant, not the shape. Memory is a non-issue throughout: peak RSS
  117 MB against a 6 GB cap.
- **The missing lever is identified *and* shown to be insufficient.** This
  `Buchberger` loop applies **no criteria**: on the completed rhombus run **234 of
  253 pairs (92%) reduced to zero** and taught the basis nothing. But the coprime
  counter says the product criterion would skip only 46% of them (28% on
  `euler-line`) — a constant factor under two. The quantity that must change is
  the **basis size**, since the pair count is quadratic in it, and no pair-skipping
  criterion makes a Gröbner basis smaller.

Frame normalisation is still refused, for the `geometry` lane's original reason:
its invariance assumption is an assumption *about the degenerate case*. Everything
stays in fully generic coordinates. Simson (16 coordinates) and Pappus (18) were
gated on `euler-line` and not attempted — a 16-coordinate attempt on a route whose
10-coordinate case diverges produces a longer timeout, not information.
`euler-line` remains **unproved rather than unchecked**, and that half was
strengthened rather than left alone: the corpus now constructs its circumcentre
and orthocentre **exactly** (Cramer's rule over the rationals) for eight triangles
— obtuse, right, isosceles, generic — and asserts on each that the hypotheses
vanish, the condition does not, and the conclusion holds. Not a proof; a guard
against a mis-transcribed predicate sitting unnoticed because no search ever got
far enough to reject it. Its self-control had to be fixed rather than written: the
first version perturbed `O` by one unit in `x` and demanded the conclusion break,
and **failed on the first triangle**, whose Euler line is horizontal — a step
along `x` slides `O` along the line. It now tries both axes and requires one to
break, which a line can never satisfy vacuously.

Full write-up:
[`docs/mathematics-2026-08/diary-geometry-frontier.md`](../../mathematics-2026-08/diary-geometry-frontier.md).

**Next, ranked.** (1) Buchberger's criteria in `groebner_cert.rs` — product first
(four lines, 28–46% of pairs *by measurement*), then chain; worth it for the whole
crate, and it will **not** by itself reach `euler-line`, which is why the counters
are committed. (2) Audit and switch `Limits::fast()` / `ideal_limits()` the same
way: measure first, flip second. (3) `euler-line` needs an algorithm, not a knob —
F4-style linear algebra over the S-pair matrix, or exploiting that all four of its
hypotheses are **linear in the four unknown coordinates** over `ℚ[ax..cy]`, so the
natural derivation is Cramer's rule over that coefficient ring and Buchberger is
being asked to rediscover it by monomial reduction. (4) Simson and Pappus remain
gated on (3). (5) A surface syntax for the corpus, still open.

<!-- plan-section: landed-changes -->

| 2026-08-15 | `geometry-frontier` | default geometry monomial order switched to degree-reverse-lex, justified by a per-subset per-order audit showing 6 unchanged condition sets and 6 byte-identical certificates — and every subset *decided*, which upgrades the corpus's minimality claim from budget-scoped to absolute; `rhombus-diagonals-perpendicular` promoted off the frontier as the seventh certified theorem with its non-degeneracy counterexample and both tamper controls, the controls now running over every saturated certificate rather than the first; `euler-line`'s obstruction measured rather than timed (basis growth and a quadratic S-pair backlog, not width and not overflow) via new `ReductionStats` and an S-pair ladder | `crates/axeyum-cas/src/geometry_certify.rs`, `crates/axeyum-cas/src/geometry_corpus.rs`, `crates/axeyum-cas/src/groebner_cert.rs`, `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs`, `crates/axeyum-cas/examples/geometry_order_audit.rs`, `crates/axeyum-cas/examples/geometry_obstruction.rs`, `artifacts/geometry-certificates/rhombus-diagonals-perpendicular.json`, `artifacts/facts/F-geometry-rhombus-diagonals-perpendicular.json` |
