# Lane: simson (a minimality claim that is true over one field and false over another)

<!-- plan-section: lane-status -->

**Continuation lane, 2026-08-15.** `pappus-minimality` deliberately left Simson
unstated — not even on `frontier()` — on the grounds that what was missing was a
**decision about which field the fact is over**, not a `GeometryProblem`. Both
halves of that question are now answered, and the answers point opposite ways.

**`F:geometry-simson-line` is PROVED, `cas-certificate`, three evidence rows.**
Tenth certificate, 14 coordinates, 7 hypotheses, **322 ms**, checker-verified.
`validate-facts.py` 100 facts / 0 errors, `cas-certificate` 19.
Closed through `close-fact.py`, which executed all three `checker_command`s.

**The implication transfers for free; the minimality does not.** A cofactor
identity has rational coefficients, so it holds in every ℚ-algebra: substitute
reals, take `Zinvₖ := 1/conditionₖ`, done. No Nullstellensatz, no closure, no
model theory — the standard reading (Pottier 2010 certificate-level, Harrison 2009
model-level). What does **not** transfer is which conditions are needed, and here
it fails in the direction that inflates: `|BC|² ≠ 0` is strictly stronger than
`B ≠ C` over ℂ.

**Over ℝ one condition suffices; over characteristic zero three are needed; both
are witnessed.** Over ℝ, `B = C` makes lines `CA` and `AB` the same line, so
`Y = Z`, so the feet are collinear whatever `X` does — every single collapse is
harmless and only `A = B = C` breaks the theorem. Over ℚ(i) the picture inverts:
`A=(1,i)`, `B=(1,0)`, `C=(0,0)`, `P=(−i,1)` lie on the genuine circle
`−(x²+y²) + x + i·y = 0` with `|CA|² = 0` at `C ≠ A`; `Y`'s two hypotheses become
*dependent* rather than contradictory, `Y` floats along the isotropic line, `X` and
`Z` stay pinned, and `Y = (0,0)` gives `collinear(X,Y,Z) = i ≠ 0`. The same four
points relabelled cyclically necessitate the other two. **7 of 7 proper subsets
refuted, 0 undecided** — absolute in ADR-0455's sense and independent of the
producer's decomposition in ADR-0460's, since no search is consulted at all.

**This is the textbook obstruction and Simson is the textbook example**, which is
worth having as an outside check rather than only internal consistency. Chou and
Gao (CADE-11, 1992, §2, ex. 2.1) use *this theorem* as their case that Wu's method
and Gröbner bases "cannot confirm" under `¬collinear(A,B,C)` alone, and prescribe
`isotropic(A,B) := perpendicular(A,B,A,B)` on each side; Harrison (2009, p. 423)
states the redundancy over ℝ and its failure over ℂ in as many words. The
coordinatisation here reached the same three conditions from the block
determinants **before** that search returned. What is new is the witnesses.

**`DegenerateWitness` now carries an optional imaginary part**, `evaluate_gaussian`
is a second code path (the rational one is untouched), the checker replays negative
controls over ℚ(i), and `imaginary` is serialised only when non-empty.
`emit_geometry_certificates`: **0 written, 10 unchanged** on the first full run after
both landed (**1 written, 9 unchanged** later, the write being this certificate's
own witness prose) — the nine predecessors are untouched either way, so the format
extension and the search change together altered no committed evidence. The load-bearing control
is `a_gaussian_counterexample_with_its_imaginary_part_dropped_is_rejected`: the real
parts alone are an ordinary configuration that **satisfies** Simson, so a checker
ignoring the new field would accept a certificate whose negative controls prove
nothing, and would look exactly like a passing run.

**ADR-0460's remedy, applied where it is cheapest: the subset search is now pruned
by the committed counterexamples** (`searchable_subsets`, `subset_is_refuted`). A
refuted subset cannot contain the conclusion in its saturated ideal, so searching it
measures the search. That is not mainly an optimisation — a subset that was never
searched cannot have its minimality confused with a property of the producer's
decomposition. On Simson it removes all seven proper subsets and leaves one
elimination: **322 ms**, against the same route before the pruning existed, which
was **killed at 12 minutes without returning**. `geometry_order_audit` prints `REFUTED (counterexample)` rather
than running a reduction it would not return from. New decline
`GeometryDecline::RefutedByOwnWitness` for when the pruning removes *everything* —
the stated theorem is false, which previously surfaced as whatever the last futile
reduction did.

**Two defects this lane created and caught, both worth the record.** (a) Two of
the three ℚ(i) witnesses shipped a description naming the wrong circle. The
coordinates were right and every checker reads the coordinates, so nothing caught
it — an artifact can be entirely correct and still carry a false statement about
itself, in the one field a human reads. Found by evaluating both candidate
equations, not by re-reading. (b) A corpus theorem the Gröbner route cannot reach
must be named in **two** hand-written `UNREACHED_BY_BUCHBERGER` lists (the
`geometry_certify` unit test and `geometry_order_audit`), and nothing connects
either to the corpus. Omitting it does not fail, it **stalls** — bounded by
`geometry_limits` and so it terminates, but not within 90 s in release — and a
stall reads like a slow machine. `euler-line` was the first instance,
`pappus-hexagon` the second, this the third, so it is a fact about the design.
With both lists updated the geometry unit tests run in **0.58 s**.

**A gate three lanes had been running by hand.**
`scripts/check-geometry-fact-transcription.py` cross-evaluates each geometry fact's
SMT-LIB `formal.statement` against the certificate it cites, at 400 random rational
configurations, requiring a constant nonzero ratio per atom. It independently
reproduces both hand counts (`euler-line` 2400, `pappus-hexagon` 4000), which is the
only reason to trust it. **All 10 geometry facts transcribe faithfully**; wired into
`just facts` and `scripts/check.sh`.

Full write-up:
[`docs/mathematics-2026-08/diary-simson.md`](../../mathematics-2026-08/diary-simson.md).

**Next, ranked.** (1) **The `fact.schema.json` minimality field**, now on its fourth
instance and with a new axis — the regime is no longer the whole story, because a
minimal set is minimal *over a field*, and this fact carries both answers in prose
in exactly the place ADR-0455 and ADR-0460 warned a wrong value would hide.
(2) **Generic witnesses over ℚ(i)**: the positive controls are still rational only,
and the asymmetry is now visible. (3) **The converse of Simson** — a genuinely
different algebraic question, since the conclusion becomes the concyclicity
determinant and the block route has nothing to eliminate. (4) **Teach
`detect_linear_blocks` to prefer determinants a declared condition divides** —
carried from the previous two lanes, now less urgent since the pruning removes most
of the subsets it would have helped on. (5) **Derive `UNREACHED_BY_BUCHBERGER` instead of hand-writing it twice** — a
flag on the corpus entry or a small-budget probe; three lanes have now paid for
the omission and the failure mode is a stall, not a failure. (6) **Raise
`AnsatzLimits::geometry().max_cofactor_degree`** — unchanged in priority.

<!-- plan-section: landed-changes -->

| 2026-08-15 | `5e63d2d2d` | `F:geometry-simson-line` proved on `cas-certificate`: Simson's line certified in 322 ms with three isotropy conditions, minimal over characteristic zero and witnessed at exact ℚ(i) points, plus witness-pruned subset search and a committed transcription gate. |
