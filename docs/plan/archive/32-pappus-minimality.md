# Lane: pappus-minimality (a minimality claim that was decided and wrong)

<!-- plan-section: lane-status -->

**Continuation lane, 2026-08-15.** `euler-linearity` left `pappus-hexagon`
certified, checker-verified, and deliberately **unfiled**: 292 s, three
non-degeneracy conditions, and a note saying the three "can only be necessitated
as a set", so its minimality would be budget-relative and
`every_used_condition_set_is_minimal_absolutely` refused it. The brief was to
decide that question rather than route around it. The answer is that the premise
was false.

**Pappus's three conditions are not needed as a set. Each one suffices on its
own.** The three-condition set was not "minimal but unprovably so" — it was **not
minimal**. `pappus-hexagon` is the ninth certified theorem, in `corpus()`, with
**one** condition, certified in **6.7 ms** against the previous 292 s, and its
minimality is **absolute**: the only proper subset of a singleton is the empty
one, and the counterexample the previous lane already committed refutes it.
`F:geometry-pappus-hexagon`, `validate-facts.py` 99 facts / 0 errors,
`cas-certificate` 18 facts.

**The previous lane had the proof and read its sign backwards.** Its three
attempts to isolate one condition collapsed, always because "killing one
intersection forces the two other constructed points onto the very line the freed
point is confined to" — recorded as an obstruction to *claiming* minimality. It is
a **proof of redundancy**. The hypotheses assert that `X`, `Y`, `Z` *exist* on
their line pairs, so a degenerate line pair does not lose its point, it frees it
along a line — and every way that can happen drags the other two cross points onto
that same line. It does not run for all three at once, which is why the empty set
is still refuted and one condition is still needed.

**Why the route said three, which is the transferable part (ADR-0460).** Not a
budget. `detect_linear_blocks` picks its decomposition from the shape of the
generators, so the multiplier was always `c₁·c₂·c₃` and every proper subset failed
at `invert_multiplier` — **decisively**, since exact division always answers. Under
ADR-0455's dichotomy that reads as the *absolute* regime, and the route's own doc
comment said exactly that. The decided test was "can this subset divide **that**
multiplier?", which is a question about a producer-side choice, not about the
theorem. **Decidedness is necessary and not sufficient.** ADR-0460 refines
ADR-0455 with a third regime — *representation-relative*: every test decided,
against a fixed representation, therefore reporting as absolute while being wrong,
and no amount of patience discovers it. The remedy is preferred to the disclosure:
`licensed_blocks` admits a block only when its determinant is a nonzero rational
times a product of powers of the conditions **currently being inverted**, so the
subset chooses the decomposition instead of inheriting it.

**`cofactor_ansatz`: bounded-degree ideal membership by exact sparse linear
algebra.** With one block licensed the elimination leaves a 48-term degree-4
residue over six untouched hypotheses. Buchberger was **killed at 7.5 minutes without returning**;
the new module settles it at cofactor degree 2 in ~25 ms with every coefficient
`±1`. It is incomplete on purpose — `NotInDegree(d)` is a *decided* statement about
a degree slice and says nothing about the ideal — its limits bound the shape of the
system and never the solve, and it re-expands its own answer before returning it.
It is tried before Buchberger in the handover, and that ordering is load-bearing:
second, the subset search never reaches the answer.

**Nothing committed changed.** `geometry_check.rs` untouched — it has now not
changed across three different producers (Buchberger, adjugate elimination, a
Macaulay-style solve), which is the property the design rests on. Enabling the
handover in `certify_any_route` was necessary and would otherwise have turned the
linear route into a second general-purpose prover on theorems whose conclusion is
in the plain hypothesis ideal, so the handover refuses to run when the elimination
consumed **no block**. `emit_geometry_certificates`: **8 unchanged, 1 written**.

**Evidence, ascending in strength.** (1) A synthetic case analysis over the strata
where a cross point is under-determined. (2) `pappus_condition_subsets` decides the
question exhaustively over `F_p` for `p = 5, 7, 11, 13, 17, 19, 23` — reading the
polynomials **out of the committed corpus** and reducing them mod `p`, over every
carrier pair up to the affine group and every solution including the
positive-dimensional ones — and finds exactly one refuting pattern, the all-zero
one; the orbit reduction is itself checked against a full enumeration at `p = 5`.
(3) `each_pappus_condition_alone_certifies` demands a **certificate** for each of
the three conditions in isolation; all three certify at cofactor degree 2. A
certificate is a polynomial identity, so that is the statement about ℚ the sweep
only suggested.

**One bug worth recording.** `factors_into` loops forever on the zero polynomial —
`exact_div(0, d)` is `Some(0)` for every `d`. It cannot arise from a block
determinant, and "cannot arise" is exactly the reasoning that leaves a loop
unguarded; the unit test written to exercise the licensing rule *directly* rather
than only through a theorem hung the suite and found it.

Full write-up:
[`docs/mathematics-2026-08/diary-pappus-minimality.md`](../../mathematics-2026-08/diary-pappus-minimality.md).

**The shared index is not made safe by discipline, in either direction.** Two
lanes hit the same race inside twelve minutes, once each way. `c391b36d4`
(`lra-dispatch`) carries one line of `docs/reference/examples.md` that is this
lane's, because `git commit -- <pathspec>` commits the *worktree* content of
those paths and discards the hunk they had carefully staged with
`git apply --cached`. `1725615688` (`lra-dispatch`) then carries five files that
are this lane's — `cofactor_ansatz.rs`, `geometry_probe.rs`,
`F-geometry-pappus-hexagon.json`, `diary-pappus-minimality.md` and one
`examples.md` row — because the remedy for the first failure, a bare
`git commit` after confirming `git diff --cached --numstat`, takes whatever is in
the index at commit time, and this lane had staged into it between their check
and their commit. Both were disclosed rather than rewritten; nothing is lost in
either direction, and the content of both is exactly as written.

The rule that follows is not a better incantation. `git commit -- <paths>` reads
the worktree and defeats index-level hunk staging; bare `git commit` reads the
index and is defeated by any concurrent `git add`. **There is no form of the
command that is safe for two lanes sharing one index**, which is the same lesson
CLAUDE.md draws for per-lane state files, arriving one level down: the index is
per-checkout state that every lane writes. What actually works is a worktree per
lane, or not sharing the file.

**Simson, answered rather than restated.** The brief asked whether
`geometry.characteristic-zero-specialisation` licenses the real-plane reading of
`|BC|² ≠ 0`. It does not, and the reason is sharper than "the witnesses are
irrational": the *certificate* is fine over every characteristic-zero field, and
it is the **minimality** side where the readings come apart, in opposite
directions. Over ℂ the isotropic directions make `|BC|² = 0` possible with
`B ≠ C`, so the condition may be genuinely necessary — and `DegenerateWitness`
holds exact rationals, so we could not state the witness. Over ℝ, `|BC|² = 0` is
`B = C` and nothing else, and if that forces the conclusion (the same shape as
Pappus) then the condition is **redundant over ℝ** and ADR-0460 forbids filing it.
These are two different theorems and the footprint entry currently papers over the
difference. Simson is deliberately **not** stated on `frontier()`: the missing
piece is a decision about which field the fact is over, not a `GeometryProblem`.
`frontier()` is empty, and `every_frontier_witness_is_consistent` says so out loud
rather than silently examining nothing.

**Next, ranked.** (1) **Simson** — decide the field first, then the algebra;
a rational configuration is an hour's work (`A=(5,0)`, `B=(0,5)`, `C=(−3,4)`,
`P=(4,−3)` on `x²+y²=25`, concyclicity as the 4×4 determinant, feet `(6/5,27/5)`,
`(27/5,−1/5)`, `(6,−1)`, verified collinear). (2) **Teach
`detect_linear_blocks` to prefer determinants a declared condition divides** —
now half-done, since the filter *rejects* unlicensed blocks but the detector still
proposes them; reach, not soundness. (3) **Raise
`AnsatzLimits::geometry().max_cofactor_degree`** and measure where the corpus's
residues stop falling to it. (4) **The `fact.schema.json` minimality field**, on
its third instance now, and the argument for deferring is thinner because the
wrong value here would have been the *strong* one. (5) Buchberger's criteria in
`groebner_cert.rs`, unchanged in priority from the last two lanes' lists.

<!-- plan-section: landed-changes -->

| 2026-08-15 | `pappus-minimality` | Pappus's hexagon theorem promoted into the corpus with **one** non-degeneracy condition instead of three (6.7 ms against 292 s), and its minimality established **absolutely** — the previous lane's three collapsed attempts to necessitate a single condition turned out to be a *proof that each condition is individually redundant*, confirmed three ways (synthetic strata argument; exhaustive `F_p` decision for seven primes over the committed polynomials, orbit reduction cross-checked against a full enumeration; and a **certificate for each condition in isolation**). The root cause is ADR-0460: the route's subset tests were all *decided* and therefore read as absolute under ADR-0455, but they tested the subset against a decomposition the producer had already fixed, so they were **representation-relative** — decided and wrong. Fixed by `licensed_blocks`, which lets the condition subset choose its own block decomposition. New `cofactor_ansatz` module: bounded-degree ideal membership by exact sparse linear algebra, which settles in ~25 ms with `±1` coefficients a residue Buchberger was killed on after 7.5 minutes without returning; incomplete on purpose, bounds the shape of the system and never the solve, self-checks its own identity. `geometry_check.rs` untouched across a third independent producer; the handover refuses to run when no block was consumed, which is what keeps the eight older certificates byte-identical (**8 unchanged, 1 written**) | `crates/axeyum-cas/src/cofactor_ansatz.rs`, `crates/axeyum-cas/src/geometry_certify.rs`, `crates/axeyum-cas/src/geometry_corpus.rs`, `crates/axeyum-cas/src/lib.rs`, `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs`, `crates/axeyum-cas/examples/pappus_condition_subsets.rs`, `crates/axeyum-cas/examples/geometry_cofactor_routes.rs`, `artifacts/geometry-certificates/pappus-hexagon.json`, `artifacts/facts/F-geometry-pappus-hexagon.json`, `docs/research/09-decisions/adr-0460-a-decided-subset-test-may-still-be-a-test-of-the-route.md` |
