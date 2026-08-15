# Lane: euler-linearity (linear elimination, and `euler-line` off the frontier)

<!-- plan-section: lane-status -->

**Continuation lane, 2026-08-15.** `geometry-frontier` measured that `euler-line`
does not fail on width, memory or arithmetic — it *diverges*: the basis never
saturates and the S-pair queue is quadratic in it, so 65 pairs processed leaves
528 queued and the next rung was killed after 27 minutes. It left a structural
observation it did not act on: all four hypotheses are **affine in the four
unknowns** `ox, oy, hx, hy` over `ℚ[ax..cy]`, so Buchberger was being asked to
rediscover Cramer's rule by monomial reduction. This lane acted on it.

**`euler-line` is the eighth certified theorem, and `frontier()` is empty.**
Certified in **4–6 ms** with **0 S-pairs, 0 basis, and a residue of exactly zero**,
against a Gröbner run that had not returned in 27 minutes on the same ladder
(reproduced on this box: 65 pairs / 528 queued / basis 33 / 15.9 s, matching the
recorded 15.8 s). `F:geometry-euler-line`, `validate-facts.py` 98 facts / 0
errors, `cas-certificate` 17 facts.

**The certificate stays in the original generators, which was the actual
requirement.** `crates/axeyum-cas/src/linear_elim.rs` does not substitute solved
forms; it uses the adjugate identity `adj(M)·(M·u + k) = det(M)·u + adj(M)·k` to
express `det(M)·uⱼ` as a polynomial free of the unknowns **plus a combination of
the original rows**, so every cofactor is against a hypothesis the problem stated.
The `det(M)^d` multiplier is then divided out **through the Rabinowitsch
generator** rather than symbolically: `1 = zᴺdᴺ − g·Σ C(N,i)g^{i−1}`. `euler-line`
has `N = 2` (its multiplier is `4·collinear(A,B,C)²`, a power of its own
non-degeneracy condition), so the saturation cofactor is
`−conclusion·(1 + collinear(A,B,C)·Zinv0)` — the `N = 1` case is the familiar
minus-the-conclusion shape of the six older certificates, and the exact polynomial
is asserted term-for-term. **`geometry_check.rs` is untouched**; it knows about
neither route, and its shape pass compares each generator against the stated
hypothesis, so a solved-form substitution would be rejected there. The emitter
agrees independently: **7 unchanged, 1 written**.

**A multiplier the stated conditions do not license is a refusal, not a licence.**
`GeometryDecline::UndividableMultiplier`. This is the soundness-relevant half and
it is tested against Thales, where the elimination *does* clear the residue but
with a two-term multiplier that is nobody's declared condition. Six of the seven
older theorems decline for exactly that reason — the block detector eliminates
*vertex* coordinates there, so its determinant is an artifact rather than the
geometric condition. `euler-line` is different because its unknowns are
constructed points. `certify_any_route` therefore runs **linear first, then
Gröbner** (with Gröbner first, `euler-line` never reaches the cheap route), and
that order was checked rather than argued.

**Minimality is ABSOLUTE, established by a cheaper and stronger instrument than
the `2ⁿ` audit (ADR-0455).** `geometry_order_audit` cannot apply here — the whole
point is that the Gröbner reduction does not return — and the linear route cannot
substitute for it, since its multiplier is an artifact of the decomposition. So:
if `c` lay in the ideal of the hypotheses plus `d·z − 1` for `d ∈ S`, it would
vanish at every common zero; a configuration satisfying every hypothesis, keeping
every condition of `S` nonzero and **falsifying** a conclusion refutes `S`
outright — no budget, no monomial order, no algorithm. The committed degenerate
counterexample *is* such a configuration, so the ledger already held the proof and
had not read it as one. `every_used_condition_set_is_minimal_absolutely` states it
for arbitrary subsets: **6 proper subsets refuted across 4 saturated certificates,
0 undecided.**

**Non-degeneracy in full, and one control that had silently stopped applying.**
Counterexample: `A = B = (0,0)`, `C = (1,0)`, `O = (1/2,0)`, `H = (0,1)` — every
hypothesis holds, the condition vanishes, `O`, `G = (1/3,0)`, `H` form a triangle.
On-locus-but-harmless: the same configuration with **`H = (0,0)`**, one coordinate
away, which violates the condition just as thoroughly and leaves `O`, `G`, `H`
collinear on the x-axis; offering it as the counterexample is rejected. That
control was written for the quadrilateral coordinatisation and therefore *skipped*
every triangle theorem, `centroid-divides-medians` included, since the day it
landed. It is now a table keyed by coordinatisation with a **full-coverage
assertion**, so the next promotion fails loudly rather than opting out. The fact's
SMT-LIB `formal.statement` was cross-evaluated against the certificate's own
polynomials at 400 random rational configurations (2 400 comparisons, 0
mismatches), with a control confirming a one-unit coefficient perturbation is
detected.

Full write-up:
[`docs/mathematics-2026-08/diary-euler-linearity.md`](../../mathematics-2026-08/diary-euler-linearity.md).

**Next, ranked.** (1) **Simson, then Pappus** — the gate `geometry-frontier` set is
open and the shape is right: Simson is 14 coordinates and **three 2×2 blocks** when
the circumcircle is stated as a concyclicity determinant instead of an explicit
centre, with the residue reducing modulo a *single* remaining generator. Its real
cost is not the coordinate count but that `|BC|² ≠ 0` is **not** `B ≠ C` over an
arbitrary characteristic-zero field, so the fact must name the real-plane
assumption in its footprint. Pappus is three more 2×2 blocks. (2) Buchberger's
criteria in `groebner_cert.rs` — still worth it for the whole crate, still not what
reaches a divergent theorem. (3) Teach the block detector to prefer determinants
that divide a **declared** condition; six of eight corpus theorems decline on a
badly-chosen multiplier and the information to choose better is in the problem.
Reach, not soundness. (4) Audit and switch `Limits::fast()` / `ideal_limits()`.
(5) A surface syntax for the corpus, open and recommended three times now.

<!-- plan-section: landed-changes -->

| 2026-08-15 | `euler-linearity` | `euler-line` certified and promoted off the frontier by **linear elimination** rather than a bigger budget — 4–6 ms and 0 S-pairs against a Gröbner run that had not returned in 27 minutes — with the cofactors derived from the adjugate identity so they stay against the ORIGINAL hypothesis generators, and the `det^d` multiplier divided out through the Rabinowitsch generator (`N = 2`, so the saturation cofactor is `−conclusion·(1 + d·z)`); a multiplier the stated conditions do not license is a refusal; condition-set minimality established **absolutely** by refuting every proper subset with a committed counterexample rather than by a `2ⁿ` budget-relative audit; the on-locus-but-harmless tamper control repaired from a constant that skipped every triangle theorem into a covered table; `geometry_check.rs` untouched and the seven older certificates byte-identical | `crates/axeyum-cas/src/linear_elim.rs`, `crates/axeyum-cas/src/geometry_certify.rs`, `crates/axeyum-cas/src/geometry_corpus.rs`, `crates/axeyum-cas/src/lib.rs`, `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs`, `crates/axeyum-cas/examples/geometry_linear_route.rs`, `crates/axeyum-cas/examples/emit_geometry_certificates.rs`, `artifacts/geometry-certificates/euler-line.json`, `artifacts/facts/F-geometry-euler-line.json` |
