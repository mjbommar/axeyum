# Diary — Pappus, and a minimality claim that was decided and wrong (lane `pappus-minimality`), 2026-08-15

The brief gave me three honest outcomes and a fourth about the ADR. The answer
was none of them, and it is better than all of them:

> Pappus's three non-degeneracy conditions are **not** needed as a set. Each one
> suffices **on its own**. The three-condition set the previous lane certified was
> not "minimal but unprovably so" — it was **not minimal**, and the ratchet that
> refused it was refusing a false claim rather than an unestablished one.

`pappus-hexagon` is now in `corpus()` with **one** condition, certified in
**6.7 ms** against the 292 s the three-condition certificate cost, checker-verified
from the artifact, and its minimality is **absolute**: the only proper subset of a
singleton is the empty one, and the counterexample the previous lane already
committed refutes it.

---

## 1. The previous lane had the proof and read its sign backwards

This is the whole finding, so it goes first. Three attempts to isolate a single
condition had collapsed, and the diagnosis was exactly right:

> Killing one intersection forces the two *other* constructed points onto the very
> line the freed point is confined to. Whether that is a theorem or an accident of
> three attempts I do not know, and saying so is the honest report.

It is a theorem. And it is not an obstruction to minimality — **it is a proof of
redundancy.** Here is the argument, which needs no algebra.

The eight hypotheses assert that `X`, `Y`, `Z` *exist* on their line pairs. So a
configuration on which, say, `AF ∩ CD` degenerates is not one where `Y` is
missing; it is one where `Y` is **under-determined**, free along a line. There are
exactly three ways that happens — `A = F`, or `C = D`, or the two lines coincide —
and in each of them the two *other* cross points land on precisely the line `Y` is
free along, so `collinear(X,Y,Z)` holds for every admissible `Y`. The condition
was carrying no weight. The same argument runs for each condition separately.

It does **not** run for all three at once: collapse the whole configuration onto
one line and every hypothesis is vacuous while `X`, `Y`, `Z` are free to be a
triangle. That is the committed counterexample, and it is why the empty set is
refuted.

So: three minimal condition sets, each a singleton, permuted by the symmetry that
exchanges `(B,E)` with `(C,F)`.

Three confirmations, ascending in strength.

**Exhaustive over `F_p`.** `examples/pappus_condition_subsets.rs` enumerates every
carrier-line pair up to the affine group and every solution of the six incidence
hypotheses — *including the positive-dimensional solution sets*, which is exactly
where the question bites — and asks which zero/nonzero patterns of `(c₁,c₂,c₃)`
admit a configuration that satisfies every hypothesis and falsifies the
conclusion. For `p = 5, 7, 11, 13, 17, 19, 23` the answer is the same and it is a
single pattern:

| pattern | refuting configuration? |
|---|---|
| `c₁=0 c₂=0 c₃=0` | **yes** |
| all seven others | no |

Two things make that evidence rather than a re-derivation. It reads the
hypothesis, condition and conclusion polynomials **out of the committed corpus**
and reduces them mod `p` term by term, so it cannot agree with a formula the
corpus does not hold; and the affine-orbit reduction that makes `p = 23` reachable
is itself checked — `--full` enumerates every first carrier triple and agrees at
`p = 5` (5,580,000 configurations with all three conditions nonzero, same single
refuting pattern, 3m44s against 6 ms).

**Certificates, which settle it over ℚ.** A finite-field sweep is a statement about
the primes it covered. `each_pappus_condition_alone_certifies` restricts the
problem to one stated condition at a time — so the subset search has no other
option — and demands a *certificate* for each. All three certify, at cofactor
degree 2, 52 / 52 / 56 cofactor terms. A certificate is a polynomial identity, so
that is the fact about ℚ that the sweep only suggested.

---

## 2. Why the route said three, and why that is the transferable part

Not a budget. This is the part that matters beyond geometry.

`detect_linear_blocks` picks its decomposition from the *shape of the generators*,
knowing nothing about which conditions the caller is currently inverting. On
Pappus it always finds all three intersection blocks, so the multiplier is always
`c₁·c₂·c₃`, so every proper subset fails at `invert_multiplier` — and fails
**decisively**, because exact division always terminates and always answers.

Read against ADR-0455's dichotomy, that is the *absolute* regime. The route's own
doc comment said as much:

> Here every subset test is *decided* — factoring a multiplier by exact division
> always terminates and always answers — so the reported set is smallest among the
> subsets this route can use.

Every word true; the conclusion wrong. The test that was decided was

> can this subset's conditions divide **that** multiplier?

and the claim is about the theorem, not about a decomposition the producer chose
for its own reasons. **Decidedness is necessary and not sufficient.** That is
[ADR-0460](../research/09-decisions/adr-0460-a-decided-subset-test-may-still-be-a-test-of-the-route.md),
which refines rather than withdraws ADR-0455 and names the third regime:
*representation-relative* — every test decided, against a producer-side choice,
and therefore reporting as absolute while being wrong. It is worse than
budget-relative, because no amount of patience discovers it.

The remedy is one filter, and it is preferred to the disclosure:

```rust
fn licensed_blocks(blocks: Vec<LinearBlock>, conditions: &[MvPoly]) -> Vec<LinearBlock>
```

A block may be eliminated only when its determinant is a nonzero rational times a
product of powers of the conditions **currently being inverted**. The condition
subset chooses the decomposition instead of inheriting it. It is a
soundness-shaped rule — never divide by something no declared condition licenses —
doing an honesty-shaped job.

### It changed no committed evidence

The filter drops every block on the six theorems whose determinant no condition
licenses (Thales and friends), so those now reach `invert_multiplier` never rather
than reaching it and being refused. Same outcome, earlier. `euler-line`'s two
blocks have determinants `4·collinear(A,B,C)` and `collinear(A,B,C)`, both
licensed, so it is untouched. `emit_geometry_certificates`: **8 unchanged, 1
written**.

The one thing I had to guard by hand is the reason that number holds. Enabling the
handover in `certify_any_route` — necessary, because Pappus's residue is not zero —
would otherwise have turned the linear route into a second general-purpose prover:
Thales's conclusion is in the plain hypothesis ideal, so a handover given the whole
untouched target would very likely have proved it, by a *different* identity than
the certificate already committed. So the handover refuses to run when the
elimination consumed no block. `an_unlicensed_determinant_is_never_used_as_a_multiplier`
asserts both halves, with and without a handover.

---

## 3. `cofactor_ansatz`: the residue Buchberger does not return on

With one block licensed, the elimination leaves a **48-term, degree-4** residue
over the six untouched hypotheses. I handed it to `reduce_many_with_cofactors` on
an idle host and killed it after **7 minutes 34 seconds** without an answer.

It is in that ideal, and the representation is small: cofactors of degree 2, and
every coefficient `±1`. That is not a Gröbner question at all, it is linear
algebra — write each cofactor as an unknown combination of the degree-≤2
monomials, expand, match coefficients. `crates/axeyum-cas/src/cofactor_ansatz.rs`
does exactly that:

```text
ansatz     solved at cofactor degree 2, 52 cofactor terms   in 17.7 ms
buchberger killed at 7.5 minutes, no answer
```

Three properties are deliberate.

**Incomplete on purpose.** `NotInDegree(d)` says nothing about the ideal, only
about its degree-`d` slice — and it is *decided*, with no ceiling, no queue and no
basis. A caller who needs the ideal question must still go to `groebner_cert`.
The limits bound the **shape** of the system (cofactor degree, matrix size), never
the solve; once a system is built it is solved to completion, so an outcome is
never "we ran out of budget mid-answer".

**It re-expands its own answer before returning it.** A producer that trusts its
own linear algebra is one arithmetic slip from emitting a certificate that says
nothing. The self-check costs one multiplication per generator.

**Row-major with sparsest-first pivoting**, which earns its place arithmetically
rather than in speed: it holds every intermediate coefficient at `±1`, so exact
`i128` rationals never approach the ceiling that naive pivoting walks into. The
first version was column-major and its pivot scan alone was `rows × columns` map
probes before any arithmetic happened.

It is tried *before* Buchberger in the handover, and that ordering is load-bearing
rather than an optimisation: second, the subset search would never reach the
answer.

### The one bug worth recording

`factors_into` loops forever on the zero polynomial — `exact_div(0, d)` is
`Some(0)` for every `d`, so the fixed point is never reached. It cannot arise from
a block determinant, which `detect_linear_blocks` guarantees nonzero. "Cannot
arise" is exactly the reasoning that leaves a loop unguarded, and the unit test I
wrote to exercise the licensing rule directly — rather than only through a theorem —
hung the suite. The guard is three lines; finding it without that test would have
been a mystery hang in someone else's session.

---

## 4. What is committed

| path | what |
|---|---|
| `crates/axeyum-cas/src/cofactor_ansatz.rs` | bounded-degree ideal membership by exact sparse linear algebra; shares no code with `groebner_cert` or `linear_elim` |
| `crates/axeyum-cas/src/geometry_certify.rs` | `licensed_blocks` / `factors_into`, the empty-block handover guard, the ansatz pass, `each_pappus_condition_alone_certifies` |
| `crates/axeyum-cas/src/geometry_corpus.rs` | `pappus-hexagon` promoted into `corpus()`; the frontier note rewritten, because it had recorded the opposite conclusion |
| `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs` | the on-locus-but-harmless control extended to the 18-coordinate coordinatisation |
| `crates/axeyum-cas/examples/pappus_condition_subsets.rs` | the exhaustive `F_p` decision, over the committed polynomials |
| `crates/axeyum-cas/examples/geometry_cofactor_routes.rs` | ansatz against Buchberger on the residues the linear route hands over |
| `artifacts/geometry-certificates/pappus-hexagon.json` | the ninth certificate, one condition, 74 cofactor terms over 9 generators |
| `artifacts/facts/F-geometry-pappus-hexagon.json` | `F:geometry-pappus-hexagon`, three evidence rows |
| `docs/research/09-decisions/adr-0460-…` | decidedness is necessary, not sufficient |

The checker is untouched. `geometry_check.rs` has now not changed across three
different producers — Buchberger, adjugate elimination, and a Macaulay-style
linear solve — which is the property the whole design rests on.

The SMT-LIB `formal.statement` was cross-evaluated against the certificate's own
polynomials at 400 random rational configurations, 4000 comparisons, zero
mismatches — with the checker first validated by reproducing `F:geometry-euler-line`'s
own claim of 2400 comparisons and zero mismatches. Prose review does not catch a
transposed sign, and neither does a checker nobody checked.

---

## 5. Simson, and the answer to the wrinkle rather than a restatement of it

The brief asked whether `geometry.characteristic-zero-specialisation` licenses the
real-plane reading of `|BC|² ≠ 0`. It does not, and the reason is sharper than
"the witnesses are irrational".

The certificate side is fine. A cofactor identity over ℚ is valid over every
ℚ-algebra, so a Simson certificate saturated by `|BC|²` proves the theorem over
any field of characteristic zero, ℂ included. Nothing there needs a real-plane
assumption.

The **minimality** side is where the two readings come apart, and they come apart
in opposite directions:

- Over ℂ, `|BC|² = 0` has solutions with `B ≠ C` — the isotropic directions
  `(1, ±i)`. If a witness of that shape satisfies the hypotheses and falsifies the
  conclusion, the condition is genuinely necessary *over ℂ* — and
  `DegenerateWitness` holds exact rationals, so we cannot state it.
- Over ℝ, `|BC|² = 0` is `B = C` and nothing else. If `B = C` forces the
  conclusion (which is what I would expect, and it is the same shape as Pappus:
  the collapse frees a foot along a line that the other two feet are already on),
  then `|BC|² ≠ 0` is **redundant over ℝ**, exactly as Pappus's second and third
  conditions were — and by ADR-0460 the fact must not be filed with it.

So the honest position is that these are **two different theorems** and the
footprint entry currently papers over the difference. A Simson fact must either
(a) state itself over characteristic zero and carry a witness type over a
quadratic extension, so the necessity of `|BC|² ≠ 0` can be exhibited where it is
true; or (b) state itself over the real plane, and then *first check whether the
condition survives minimality there at all*, because the Pappus experience says
the default answer is no.

I did not state Simson on `frontier()`, and that is deliberate rather than a
shortfall: an entry whose generic witness replays fine but whose condition set is
about to be decided by (a)-versus-(b) would be a fourth statement of the same open
question. The question is the deliverable, and it is above. What the next lane
needs is not a `GeometryProblem` — that is an hour's work with a rational
circumcircle, e.g. `A=(5,0)`, `B=(0,5)`, `C=(−3,4)`, `P=(4,−3)` on `x²+y²=25`,
concyclicity as the 4×4 determinant so no centre variable is needed, feet
`X=(6/5,27/5)`, `Y=(27/5,−1/5)`, `Z=(6,−1)`, which are collinear — it is a
decision about which field the fact is stated over, and that decision is now
stated rather than implied.

`frontier()` is empty, and the list handles that: `every_frontier_witness_is_consistent`
says so out loud rather than silently examining nothing.

---

## 6. What I would tell the next reader

**The ratchet was right and its reason was wrong, and both halves matter.**
`every_used_condition_set_is_minimal_absolutely` blocked a fact that should have
been blocked. But the note explaining *why* said the conditions were inseparable,
and that was false — so a reader trusting the note would have concluded the
right thing about filing and the wrong thing about the mathematics. A gate's
verdict and a gate's rationale are separate artifacts and can disagree.

**A search for a counterexample that keeps collapsing is evidence with a sign.**
The two live readings are "our witnesses are too weak" and "the condition is
redundant", and they license opposite ledger actions. Say which one you are
testing, and how you would tell them apart, before you write down either.

### The ranked next steps

1. **Simson**, per §5 — and the first question is which field, not which algebra.
2. **Teach `detect_linear_blocks` to prefer determinants a declared condition
   divides**, which was the previous lane's item 4 and is now half-done: the
   filter *rejects* unlicensed blocks, but the detector still proposes them, so on
   the six theorems that decline it proposes a block and we throw it away rather
   than proposing a better one. That is reach, not soundness.
3. **Raise `AnsatzLimits::geometry().max_cofactor_degree`** and see what else the
   corpus's residues fall to. Degree 3 is head-room over the degree-2 answers we
   have; nothing has measured where the cliff is.
4. **The `fact.schema.json` minimality field**, now on its third instance
   (ADR-0460's closing note). The argument for deferring is thinner than it was:
   the wrong value here would have been the *strong* one.
5. **Buchberger's criteria in `groebner_cert.rs`** — unchanged in priority from
   the last two lanes' lists, still worth it for the whole crate, still not the
   thing that reaches a divergent theorem.
