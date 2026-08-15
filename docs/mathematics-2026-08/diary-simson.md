# Lane diary: `simson` — the field question, answered in both directions

**2026-08-15.** Brief: add `F:geometry-simson-line` to the ledger, PROVED on the
`cas-certificate` route, and *decide* the question the `pappus-minimality` lane
left as its deliverable — whether `geometry.characteristic-zero-specialisation`
licenses the real-plane reading of `|BC|² ≠ 0`.

The answer has two halves and they point opposite ways, which is why the lane
before this one was right to refuse to guess.

---

## 1. The forward implication needs no transfer principle at all

A cofactor certificate is an identity in `ℚ[coordinates, Zinv₀…]`:

```text
conclusion = Σᵢ qᵢ·hypothesisᵢ + Σₖ q₀ₖ·(conditionₖ·Zinvₖ − 1)
```

with **rational** coefficients. Substitute real numbers for the coordinates, take
`Zinvₖ := 1/conditionₖ` — legitimate exactly because the conditions are nonzero —
and every generator vanishes, so the conclusion does. That is the whole argument.
It uses the ring axioms and the existence of an inverse for a nonzero element,
and nothing else. No Nullstellensatz, no algebraic closure, no model theory.

So the real-plane reading of the *implication* is licensed, and it is licensed for
the boring reason rather than a subtle one. This is standard in the literature and
stated in both idioms: Pottier gives the certificate-level version (a `P^r = Σ Qᵢ
Pᵢ` identity makes `P` vanish wherever the `Pᵢ` do, "the converse is also true when
`K` is algebraically closed", so closure buys *completeness*, never soundness), and
Harrison the model-level one — "if a universal formula holds over `C` it also holds
over `R`", with the converse explicitly false.

**The lane before this expected the certificate side to be fine and it is.** What
it could not settle from where it stood is the other half.

## 2. Where the readings genuinely come apart is the CONDITIONS — and the answer is
the reverse of what was expected

The `pappus-minimality` lane laid out two possibilities and predicted the second:

> - Over ℂ, `|BC|² = 0` has solutions with `B ≠ C` — the isotropic directions
>   `(1, ±i)`. If a witness of that shape satisfies the hypotheses and falsifies the
>   conclusion, the condition is genuinely necessary *over ℂ* — and
>   `DegenerateWitness` holds exact rationals, so we cannot state it.
> - Over ℝ, `|BC|² = 0` is `B = C` and nothing else. If `B = C` forces the
>   conclusion … then `|BC|² ≠ 0` is **redundant over ℝ**.

**Both halves are correct.** Neither is a dead end, and the resolution is that they
are statements about two different theorems, both of which this fact now carries.

Over `ℝ`, the case analysis is three lines. `B = C` makes lines `CA` and `AB` the
same line, so `Y = Z`, and three points two of which coincide are collinear whatever
the third does. Same for the other two collapses. So the conclusion survives every
*single* coincidence and fails only at `A = B = C`, which annihilates all three
conditions at once. Over `ℝ` any one condition suffices; the minimal real sets are
the three singletons. Exactly Pappus's shape, exactly as predicted.

Over a field containing `i` it is the opposite. Take

```text
A = (1, i)   B = (1, 0)   C = (0, 0)   P = (−i, 1)
```

All four lie on the genuine circle `−(x²+y²) + x + i·y = 0` (`λ = −1`, so it is a
circle and not a degenerate line case). Then `|BC|² = 1`, `|AB|² = −1`, and
`|CA|² = 1 + i² = 0` **at `C ≠ A`**. The foot `Y`'s two hypotheses,
`collinear(C,A,Y)` and `(Y−P)·(A−C) = 0`, do not become contradictory — they become
*dependent*, and `Y` ranges over the whole isotropic line. The other two feet stay
pinned at `X = (−i, 0)` and `Z = (1, 1)`, and `Y = (0, 0)` gives
`collinear(X,Y,Z) = i ≠ 0`.

So `|CA|² ≠ 0` is necessary over characteristic zero even with the other two
conditions in hand, and the same four points relabelled cyclically give the other
two necessities. **Three conditions, minimal, decided at exact points.**

### This is the textbook obstruction, and the theorem is the textbook example

Worth stating plainly, because it makes the result checkable against something
outside this repository rather than only against itself. Chou and Gao's CADE-11
paper opens its section on non-degeneracy with *this theorem*:

> "The obvious non-degenerate condition for this statement seems to be 'A, B and C
> are not collinear'. Indeed, in Euclidean geometry, Simson's theorem is valid under
> this condition. However, if we try to prove Simson's theorem under this condition
> with Wu's method or the GB method … then the statement cannot be confirmed."

and prescribes `isotropic(A,B) := perpendicular(A,B,A,B)`, i.e. `|AB|² = 0`, on each
side. Harrison's run of Wu's method on Simson says the rest:

> "In the intended interpretation as real numbers, there is some redundancy, since
> `bx − cx = 0` implies `(bx − cx)² + (by − cy)² = 0`. However, this is not in
> general the case over the complex numbers."

The corpus entry was written before that search came back and arrived at the same
condition set from the block determinants, which is the useful kind of agreement.
What is added here is the **witness**: the literature asserts the redundancy over
`ℝ` and the necessity over `ℂ`; this ledger exhibits both at exact points, on both
sides of the field question.

## 3. What that cost, mechanically

`DegenerateWitness` gained an optional `imaginary: BTreeMap<String, Rational>`, and
`evaluate_gaussian` evaluates a polynomial at a `ℚ(i)`-point on a second code path
(the rational path is untouched, so the nine older certificates are decided by
exactly the arithmetic they were before). `geometry_check` replays negative controls
over `ℚ(i)`; `geometry_json` emits the field only when non-empty.

The control that matters is `a_gaussian_counterexample_with_its_imaginary_part_dropped_is_rejected`.
The real parts of these witnesses alone are a perfectly ordinary configuration that
**satisfies** Simson, so a checker that read the file and ignored the new field
would accept a certificate whose negative controls prove nothing — and would look
exactly like a passing run. That is this repository's most-repeated failure mode and
it was one `serde` shrug away here.

`emit_geometry_certificates`: **0 written, 10 unchanged** on the first full run after
both changes landed, and **1 written, 9 unchanged** on a later one whose single
write was this certificate's own witness prose (§5a). Either way the nine
predecessors are untouched: the format extension and the search change together
altered no committed evidence.

## 4. ADR-0460's remedy, applied where it is cheapest

The subset search now **prunes by the committed counterexamples**
(`searchable_subsets` / `subset_is_refuted`). A subset with a configuration that
satisfies every hypothesis, keeps that subset's conditions nonzero and falsifies a
conclusion cannot contain the conclusion in its saturated ideal — a member would
have to vanish there — so searching it is measuring the search.

This is not primarily an optimisation, though the numbers are stark: on
`simson-line` all seven proper subsets are refuted, leaving one elimination, and the
theorem certifies in **322 ms**. Before the pruning existed, the same route on the
same theorem was **killed at 12 minutes without returning** — that is what was
measured, and which of the seven futile subsets it was inside at the time was not,
because the run produced no output past the elimination report. It is ADR-0460's
preferred remedy in its cleanest form. That ADR's failure is a minimality claim that
is really a claim about the producer's decomposition, and it cannot arise for a
subset that was never *searched*: a pruned subset is settled by a fact about the
theorem, a rejected one by a fact about the search. Making the first set as large as
the evidence allows shrinks the second.

`geometry_order_audit` learned the same verdict and prints `REFUTED
(counterexample)` instead of running a reduction. Without that it would not come
back on this theorem.

There is a new decline for the case where the pruning removes *everything*:
`GeometryDecline::RefutedByOwnWitness` — the problem's own counterexample refutes its
full condition set, i.e. the theorem as stated is false. Previously that would have
surfaced as whatever the last futile reduction happened to do.

## 5. The certificate

Fourteen coordinates, seven hypotheses, one conclusion. The circle is a
[`concyclic`] 4×4 determinant with the column of ones row-reduced away, so `P ∈ Γ`
costs no centre variable, no radius variable and no extra hypothesis — and the
"circle **or** line" it also admits is harmless rather than something to condition
away, since collinear `A, B, C` makes all three side lines equal and all three feet
the same point.

Three 2×2 blocks, one per foot, determinants `−|BC|²`, `−|CA|²`, `−|AB|²`, six terms
each, each to the **first** power. Multiplier 164 terms of degree 6, divided back out
through three Rabinowitsch generators. Residue 576 terms, handed to the **single**
unconsumed generator — the circle. Simson's theorem past the three Cramer solves is
one division by the circle, and the certificate's cofactor against that generator is
21 terms. `geometry_linear_route` measures the Buchberger arm of that handover at
**0 S-pairs processed, 0 queued, basis 1**, which is what a one-generator ideal
costs; which arm the emitted certificate itself took is not recorded in the artifact
and is not claimed, since `settle_residue` tries `cofactor_ansatz` first, both arms
re-expand their answer, and the checker verifies the identity knowing neither.
1875 cofactor terms over 10 generators; 4 degenerate witnesses (3 Gaussian, 1
rational), 1 generic, 24 numeric points.

## 5a. One error, caught by arithmetic rather than by reading

Two of the three `ℚ(i)` witnesses shipped a description naming the circle as
`−(x²+y²) + y + i·x = 0`. The correct equation is `−(x²+y²) + x + i·y = 0`, and
the wrong one does not pass through three of the four points. Nothing caught it,
because the *coordinates* were right and every checker in this repository reads
the coordinates: the concyclicity hypothesis is verified at the point, the
condition is verified at the point, the conclusion is verified at the point. The
sentence naming the circle is prose in a committed artifact and prose is not
checked.

Found by evaluating both candidate equations at the four points rather than by
re-reading the sentence, which is the general remedy — and the general lesson is
that an artifact can be entirely correct and still carry a false statement about
itself, in the one field a human is most likely to read.

## 5b. One omission, on its third instance, in two places at once

A corpus theorem the Gröbner route cannot reach has to be named in **two**
hand-written lists — `UNREACHED_BY_BUCHBERGER` inside
`geometry_certify`'s `the_route_selector_reproduces_the_groebner_certificate_exactly`,
and a second one of the same name inside `geometry_order_audit` — and nothing
connects either to the corpus.

Adding `simson-line` and not updating them does not fail anything. It **stalls**:
the test runs Buchberger on fourteen coordinates and three Rabinowitsch
generators, which is bounded by `geometry_limits` and therefore does terminate,
but had not returned after 90 s in release. A stall reads like a slow machine, and
it cost this lane most of an hour of misdiagnosis — the unit-test binary sat at
"11 of 12 passed" while I looked for a hang in the code I had just written.

The unit test's own comment predicted this exactly:

> The hazard this list carries is worth naming: a new divergent theorem added to
> the corpus and *not* added here makes this test hang rather than fail, and a hang
> reads like a slow machine.

It was right, it was ignored, and the reason it was ignored is that the warning
lives next to the list rather than next to the corpus. `euler-line` was the first
instance, `pappus-hexagon` the second, `simson-line` the third — three lanes, one
omission, and by now that is a fact about the design rather than about any of the
lanes. The list should be derived (a `reachable_by_buchberger` flag on the corpus
entry, or a measured probe with a small budget) rather than written twice by hand.
Recorded as a ranked next step rather than done here, because changing it touches
both consumers and this lane's diff is already large.

## 6. A gate that three lanes had been running by hand

`scripts/check-geometry-fact-transcription.py`. A `cas-certificate` geometry fact
states its theorem twice — as SMT-LIB in `formal.statement`, as polynomials in the
artifact — and nothing connected them. The fact is `proved` because the certificate
re-derives; the certificate knows nothing about the transcription. Three lanes in a
row noticed, cross-evaluated by hand at 400 random rational configurations, and
wrote the count in a diary.

It is now a script: split the antecedent into atoms, match them positionally against
the certificate's hypotheses and saturations, evaluate both sides exactly, require a
**constant nonzero ratio**. Proportionality rather than equality, because a
polynomial and a nonzero rational multiple of it state the same hypothesis — and the
ratio is printed, so the one place it is not 1 (`parallelogram-diagonals-bisect`'s
conclusions, factor 2) is visible rather than absorbed.

It independently reproduces the two hand counts — `euler-line` 2400 comparisons,
`pappus-hexagon` 4000 — which is the only reason to believe it. **All 10 geometry
facts transcribe faithfully.** Wired into `just facts` and `scripts/check.sh`.

## Files

| path | what |
|---|---|
| `crates/axeyum-cas/src/geometry_certify.rs` | `Gaussian`, `evaluate_gaussian`, `DegenerateWitness::{point, is_gaussian, rational}`, `concyclic`, `searchable_subsets`, `subset_is_refuted`, `RefutedByOwnWitness` |
| `crates/axeyum-cas/src/geometry_corpus.rs` | `simson_line()` promoted straight into `corpus()`, its three `ℚ(i)` witnesses and one rational one, and the necessity test |
| `crates/axeyum-cas/src/geometry_check.rs` | negative controls replayed over `ℚ(i)` |
| `crates/axeyum-cas/src/geometry_json.rs` | `imaginary` emitted only when non-empty, so nine files stay byte-identical |
| `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs` | the dropped-imaginary-part control, the `ℚ(i)` minimality replay, the Simson on-locus row |
| `crates/axeyum-cas/examples/geometry_order_audit.rs` | `REFUTED (counterexample)` instead of a reduction that does not return |
| `scripts/check-geometry-fact-transcription.py` | the hand-work three lanes repeated, as a gate |
| `artifacts/geometry-certificates/simson-line.json` | the tenth certificate |
| `artifacts/facts/F-geometry-simson-line.json` | `F:geometry-simson-line`, three evidence rows |

## 7. What I would tell the next reader

**Ask what field a certificate is a theorem of before asking whether its conditions
are minimal.** The implication transfers for free; the *minimality* does not, and it
can be strictly stronger in the field the proof lives in than in the field the
reader has in mind. A characteristic-zero minimality claim quoted as a real-plane
one is a real overstatement, and nothing in the artifact marks the difference — the
condition polynomials look identical.

**A collapsing search for a witness still has a sign, and now there are two ways to
read it.** ADR-0460 says the live hypotheses are "our witnesses are too weak" and
"the condition is redundant". This lane adds a third: **"our witnesses live in the
wrong field."** All three were true here of different conditions at once, and they
license different actions — file a smaller set, file the larger one, or extend the
witness type.

**When a search cannot find a counterexample, check whether one is even expressible
before concluding anything from the failure.** `DegenerateWitness` held rationals,
so the search for a `ℚ(i)` witness was not failing — it was not being run.

## The ranked next steps

1. **`fact.schema.json`'s minimality field**, now on its fourth instance and with a
   new axis: the regime (`absolute` / `budget-relative` / `representation-relative`)
   is no longer the whole story, because a minimal set is minimal *over a field*.
   This fact carries both answers in prose in `statement` and `notes`, which is
   exactly where ADR-0455 and ADR-0460 said the wrong value would be hardest to see.
2. **Generic witnesses over `ℚ(i)` too.** The positive controls are still rational
   only. A theorem whose *generic* configurations are all rational is not thereby a
   theorem about the reals, and the asymmetry is now visible.
3. **The converse of Simson** — collinear feet imply `P` on the circle. It is the
   other half of the classical iff and is a genuinely different algebraic question:
   the conclusion is the concyclicity determinant, which is not linear in anything,
   so the block route has nothing to eliminate.
4. **Derive `UNREACHED_BY_BUCHBERGER` rather than hand-writing it in two places** —
   §5b. A flag on the corpus entry, or a probe with a deliberately small budget.
   Three lanes have now paid for the omission and its failure mode is a stall, which
   is the worst kind: it reads like a slow machine.
5. **Teach `detect_linear_blocks` to prefer determinants a declared condition
   divides** — carried unchanged from the previous two lanes' lists. Reach, not
   soundness, and now less urgent, since the pruning removes most of the subsets it
   would have helped on.
6. **Raise `AnsatzLimits::geometry().max_cofactor_degree`** — unchanged in priority;
   nothing has measured where the cliff is.
