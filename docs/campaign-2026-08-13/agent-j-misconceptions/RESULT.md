# agent-j — the misconception corpus as a negative-control evaluation

**Question.** Does axeyum *detect* plausible-but-wrong mathematics, or does it
only verify things already believed?

**Answer, measured.** Of 147 live misconceptions in the `math-education` corpus,
**86 are formalisable and refutable** in a fragment axeyum decides. I built **32**
of them as negative controls. Axeyum refuted **32 of 32**, produced **0**
`unknown`, and — the headline — **0 wrong answers**. Three deliberately
*satisfiable* companions came back `sat` with witnesses the evaluator re-checked,
which is what proves the 32 refutations are refutations of something rather than
artefacts of a broken encoder.

Everything below is computed from `census.tsv` and `logs/`, not asserted.

---

## 1. Reading `census.tsv` (please read this before quoting a number)

The file is **15 header lines beginning with `#`, then exactly 148 data rows**,
one per `.md` file, tab-separated with four columns. A naive count of non-empty
lines gives 163 and appears to show "15 unlabelled rows" — those 15 are the
comment header, and **there are no unlabelled data rows**. The file now says so
in its own header, and:

```
awk -F'\t' '!/^#/ && NF==4' census.tsv | wc -l     -> 148
awk -F'\t' '!/^#/' census.tsv | awk -F'\t' 'NF!=4' -> 0 rows
```

Columns: `slug`, `class`, `fragment`, `note`.

### What each class code means

| code | meaning | count |
|---|---|---:|
| `A1` | Formalisable **and refutable**, and the distractor text *is itself* a false ground or universal proposition in a fragment axeyum decides. No modelling choice is needed beyond writing the arithmetic down. | **49** |
| `A2` | Formalisable **and refutable** after exactly **one** standard, uncontroversial formalisation choice — probability = counts / \|Ω\|; "best fit" = least squares; "rectangle" = four right angles. | **37** |
| `B` | A genuine proposition, but **out of every fragment axeyum decides**. The `fragment` column names what it would need. | **17** |
| `C-epistemic` | Not a checkable proposition: a claim about what evidence licenses (base rates aside — those are `A2`), sampling, causal inference, effect size. | **20** |
| `C-definitional` | Not a checkable proposition: a vocabulary, naming, or classification question ("does *side* apply to a circle"). | **8** |
| `C-process` | Not a checkable proposition: about method, instruction, disposition, or self-assessment. | **7** |
| `C-perception` | Not a checkable proposition: about how a picture reads (axis scale, iconic misreading of a plot). | **6** |
| `C-empirical` | Not a checkable proposition: a measurement claim about the physical world (the length of a solar year; the growth ratio of nautilus shells). | **3** |
| `DEP` | `status: deprecated` in the corpus. Excluded from the denominator. | **1** |

Regenerate with:
`awk -F'\t' '!/^#/ && NF==4 {print $2}' census.tsv | sort | uniq -c`
(output committed as `counts.txt`).

### The census, rolled up

| | count | share of 147 |
|---|---:|---:|
| **A — refutable in a fragment we decide** (`A1` + `A2`) | **86** | 58.5% |
| **B — formalisable, out of fragment** | **17** | 11.6% |
| **C — not a checkable proposition** (all four `C-*`) | **44** | 29.9% |
| deprecated, excluded | 1 | — |

Denominator is **147**, not 148: `accurate-test-means-positive-result-is-reliable`
carries `status: deprecated` and `replaced_by: M:base-rate-neglect-error`. 148 is
the file count and is the number the roadmap note quotes; 147 is the number of
live misconceptions.

### Reading these numbers honestly

The brief expected category C to be large. It is 30% — **smaller** than
predicted, and I do not want that read as a win. Two caveats:

1. **This is a school-mathematics corpus.** Its misconceptions are
   disproportionately about arithmetic, fractions, percentages and elementary
   algebra, which is exactly where our fragments live. A research-mathematics
   misconception corpus would invert the ratio. The 58.5% measures the overlap
   between *this* corpus and our fragments, not between "real mathematical error"
   and our fragments.
2. **`A1` (49, 33%) is the number that survives a hostile reading.** `A2` (37)
   each require a modelling choice. They are all standard choices, but they are
   choices, and someone who disagreed with one would move that row to C. I split
   the categories rather than reporting a single padded 86 for this reason.

Five `A2` rows are weak enough to name: `equals-is-directional` and
`probability-of-rare-event-is-zero` formalise to near-tautologies (symmetry of
equality; `p > 0 ∧ p = 0`); `a-drawn-trendline-proves-a-strong-relationship`,
`shape-must-sit-flat-to-be-a-square` and `time-order-does-not-matter-in-a-series`
need me to supply the dataset or the coordinates. I kept them in A because the
underlying claim really is false and really is decidable, but a reader who moved
all five to C would get 81 / 147 = 55%, and I would not argue.

### The 17 in category B, and what they would need

Real analysis and limits (7): `a-limit-is-a-value-you-cant-quite-reach`,
`a-limit-is-just-a-good-approximation`, `decimal-expansion-must-end`,
`infinitely-many-steps-cant-add-to-a-finite-amount`, `pi-equals-22-over-7`,
`point-nine-recurring-is-less-than-one`,
`zero-point-nine-repeating-is-slightly-less-than-one`.
Cardinality / Cantor (3): `all-infinities-are-the-same`,
`you-could-list-them-if-you-tried-harder`, plus the reals-are-listable framing.
Extended reals / ordinals (2): the two `infinity-is-a-…-number` duplicates.
Metatheory (3): `godel-means-math-is-broken`, `liar-paradox-is-just-wordplay`,
`halting-problem-means-cant-debug`.
Quantification over functions (1): `a-fairer-voting-method-must-exist…` (Arrow —
finite for fixed candidates and voters, but the quantifier ranges over
6^(6^n) social welfare functions, so it is not a benchmark).
Real/trigonometric geometry (1): `angle-size-depends-on-arm-length`.

That list is a decent statement of the ladder above the finite-domain core:
**limits first, cardinality second.** Seven of seventeen are limits.

---

## 2. J2 — the suite

`crates/axeyum-scenarios/src/misconception.rs`, wired into `catalog()` at
`crates/axeyum-scenarios/src/lib.rs:537`.

**35 scenarios: 32 refutations (`unsat`) and 3 degenerate controls (`sat`).**

### Why an unsat-expecting suite, and the shape problem underneath it

A suite of things that *should* be provable degrades silently — this repository
shipped a corpus gate that ran zero tests for fifteen days while exiting 0. A
suite whose expected answers are refutations fails the moment the refutations
stop arriving.

But there is a wrinkle that nearly sank the design. A misconception is normally a
false **universal**, and refuting a false universal is a *satisfiability*
question: you exhibit a counterexample. Taken naively the whole suite would be
`sat`-expecting and would have exactly the vacuity problem it exists to avoid. So
each control is built in one of two shapes:

- **`UniversallyFalse` (28 of 32).** The misconception's rule fails at *every*
  point of a nondegenerate box, so asserting it over the box is `unsat` and the
  `unsat` is a real search. `(a+b)² = a²+b²` for `a, b ≥ 1` is this shape; so is
  `1/(a+b) = 1/a + 1/b`, so is `x + x = 7`, so is the base-rate one.
- **`PropertyPinned` (4 of 32).** The rule fails only somewhere, so the
  counterexample region is pinned **by properties, not by literals**. "A
  non-square rectangle and a square of equal perimeter have equal area" —
  `a+b = c+d`, `c = d`, `a < b`, claim `ab = cd` — is `unsat` over the whole box
  (it is strict AM–GM) and is still a four-symbol search. Likewise
  `century_year_is_a_leap_year` is pinned by "divisible by 100 but not 400"
  rather than by writing 1900 in.

A misconception that could only be made `unsat` by writing its counterexample in
as constants is **deliberately not built**. A one-case "search" would overstate
what the suite proves.

### The anti-vacuity guards, and the mutation test that shows they fire

Five tests, not a comment (`misconception.rs`, `mod tests`):

1. `control_table_matches_what_is_built` — the `CONTROLS` metadata table and the
   catalog must agree name-for-name.
2. `every_control_self_checks_and_refutations_are_exhaustive` — every refutation
   must self-check to `UnsatEvidence::Exhaustive`, never `Sampled`. A sampled
   refutation is a spot check, not a proof.
3. `MIN_REFUTATIONS = 30` — a hard floor, so an emptied catalog fails.
4. **The degenerate controls must be `sat`.** `(a+b)² = a²+b²` *does* hold at
   `a = 0`; `(p→q) ↔ (q→p)` *does* hold at `p = q`; `n²−n+41` *does* factor at
   `n = 41`. If the builders were emitting malformed queries that happened to be
   trivially unsatisfiable, guards 1–3 would still pass and this one would not.
5. `premises_alone_are_satisfiable` — for every refutation, the constraints
   *without* the misconception's claim must admit a model. Without this, a
   mistyped range bound would make a query unsatisfiable for reasons having
   nothing to do with the misconception, and the suite would look healthy.

Guards 4 and 5 are the ones that earn their keep, and I can show it rather than
claim it.

**Guard 5 caught a real error of mine, unprompted.** My first encoding of
`one_has_two_distinct_divisors` put `d ≠ e` in the *premises* and made the claim
a tautology. Every other test stayed green; `premises_alone_are_satisfiable`
failed with "the premises alone are unsatisfiable, so its refutation proves
nothing about the misconception". That is the bug class the campaign kept hitting
— a control that does not fire — caught mechanically, on the first run, by a
guard written before the bug existed.

**Guard 2 and 4 verified by deliberate mutation** (`logs/mutation.log`; baseline
6/6 green):

| mutation | result |
|---|---|
| `binomial_square_spread` loses its no-wraparound range bounds | **FAILED** — `self_check` finds the wraparound model at width 8 |
| `REFUTATIONS` emptied | **FAILED** — "only 0 refutations; the floor is 30" |
| a degenerate control made unsatisfiable | **FAILED** — 4 of 6 tests red |

So the guards are not removable with the suite still green, which is the property
two other lanes found they lacked yesterday.

### What it refutes

32 controls, covering 41 distinct corpus entries (several controls formalise more
than one entry — `(a+b)² = a²+b²`, `√(a+b) = √a+√b` and "3 east then 4 north is
7 away" are one term).

Algebra and arithmetic: `binomial_square_spread`, `distribute_first_only`,
`subtraction_commutes`, `negative_times_negative`, `exponent_is_a_multiplier`,
`exponent_counts_one_extra_factor`, `same_letter_two_values`,
`students_and_professors`, `doubling_the_side_doubles_area`,
`doubling_the_side_doubles_volume`, `equal_perimeter_equal_area`.

Fractions, ratio and percentage: `proper_fraction_scaling`,
`equal_numerators_bigger_denominator`, `mediant_is_the_sum`,
`reciprocal_distributes`, `part_to_part_ratio_is_part_to_whole`,
`percent_up_then_down`, `stacked_discounts_add`.

Probability and counting: `base_rate_neglect`, `second_draw_unchanged`,
`complement_is_one_outcome`, `disjoint_addition_rule`, `plurality_is_a_majority`.

Number theory and divisibility: `two_is_prime`, `one_has_two_distinct_divisors`,
`odd_plus_odd_is_odd`, `century_year_is_a_leap_year`, `small_scope_pattern_trap`.

Logic and proof: `converse_is_the_contrapositive`,
`counterexample_is_an_exception`, `elapsed_time_is_decimal`,
`matrix_product_entrywise`.

The one I would single out is **`small_scope_pattern_trap`**. It asserts that
`n² − n + 41` has a factor in `[2, 40]` for some `n ≤ 40`, and that is `unsat` —
Euler's polynomial really is prime at all 41 points. Its companion
`small_scope_break_at_41` is `sat`: at `n = 41` it factors as `41 × 41`. Together
they *are* the misconception `proof-is-just-checking-lots`: the pattern survives
every check a patient learner would run, and then breaks one step past where
patience ends. It is the only control where the `unsat` is the trap rather than
the correction.

### Overflow: the live soundness hazard, and how it is contained

Over `BV(w)` many false identities become **true** by wraparound.
`(a+b)² = a²+b²` holds whenever `2ab ≡ 0 mod 2^w` — at width 8, `a = 16, b = 8`
satisfies it. Every control therefore carries an explicit range constraint chosen
so no intermediate value wraps, and computes in a zero-extended width when the
arithmetic needs more headroom than the enumeration budget allows. This is not
enforced by a comment: `self_check` enumerates the whole domain, so a wrong bound
surfaces as a found model. The first mutation above is precisely that check
firing.

### What it declines, and why

**Eleven `A2` misconceptions in QF_LRA are censused but not built** —
`expected-value-is-the-most-likely-outcome`, `gamblers-fallacy-belief`,
`law-of-averages-corrects-past-outcomes`, `probability-of-two-options-is-always-half`,
`p-value-is-probability-hypothesis-true`, `loan-total-is-just-principal`,
`compound-growth-looks-linear-at-first`, `percentage-over-100-impossible`,
`elevation-and-depression-are-different-sizes`,
`a-best-fit-line-must-pass-through-the-most-points`,
`a-drawn-trendline-proves-a-strong-relationship`.

The reason is structural and is filed as feedback B1: `Scenario::check_unsat`
establishes UNSAT by **enumerating every declared symbol**, and
`crates/axeyum-scenarios/src/lib.rs:544` `unreachable!()`s on `Sort::Int` and
`Sort::Real`. An UNSAT scenario in this crate can therefore only live over
`Bool`/`BitVec`. I hand-translated four of the fifteen QF_LRA candidates into
scaled integers over bit-vectors (`base_rate_neglect`, `percent_up_then_down`,
`stacked_discounts_add`, `second_draw_unchanged`); the rest would be the same
translation with no new content, so I stopped rather than pad.

**Seventeen category-B misconceptions are declined outright** as out of fragment,
listed in §1. That is the honest decline the brief asked for, and it is a pass:
the suite says nothing about limits or cardinality rather than guessing.

**Six `A1`/`A2` rows are refutable only by witness**, not by a nondegenerate box
or a property-pinned region — `inequality-has-one-answer`, `area-and-perimeter`
in its second reading, `zero-is-not-even`, `equal-shares-means-envy-free` (which
is only false for three or more agents; for two, proportional *is* envy-free),
`sequence-pattern-is-unique`, `a-square-is-not-a-rectangle` (needs EUF over
predicates). Building these would have meant writing counterexamples in as
constants, which §2 explains I refused to do.

---

## 3. Measurement

Snapshot `eb94e8f9a` in `~/.cache/axeyum-agent-j`, per rule 7. Full table in
`logs/solver-verdicts.log`.

```
refuted (unsat as expected): 32
witnessed (sat as expected):  3
unknown (honest decline):     0
WRONG ANSWERS:                0
```

Every scenario decided in ≤ 37 ms through `SatBvBackend`, the real
lower-to-AIG-to-CNF-to-SAT path; total solver time across all 35 was ~90 ms.
Ground truth in every case came from `Scenario::self_check` — exhaustive
enumeration by the `axeyum-ir` evaluator — before the solver was asked, so no
verdict here rests on the search path agreeing with itself.

The solver-side wiring needed **no edit under `crates/axeyum-solver/`** (agent-k's
territory): `crates/axeyum-solver/tests/scenarios.rs` iterates `catalog()`, so
adding to `catalog()` puts every control through the differential test. That
suite passes unmodified: `1 passed`, 6.50 s (`logs/solver-scenarios.log`).

Gates, all with counts confirmed nonzero:

| gate | result |
|---|---|
| `cargo test -p axeyum-scenarios` | **71 passed**, 0 failed, 70.4 s (65 before this change + 6 new) |
| doctests | 1 passed |
| `cargo clippy -p axeyum-scenarios --all-targets -- -D warnings` | clean (one `single_match_else` fixed) |
| `RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-scenarios --no-deps` | clean (one private intra-doc link fixed) |
| `./scripts/check-fmt-complete.sh` | checked **882** files |
| `cargo test -p axeyum-solver --features full --test scenarios` | 1 passed, 6.50 s |

Added cost to the shared `catalog()`: ~0.70 s of self-check and ~0.09 s of solver
time. That is after I measured and shrank three domains —
`matrix_product_entrywise` originally declared four symbols its assertion never
reads, quadrupling its enumeration for 854 ms of nothing.

---

## 4. J3 — curriculum links, and what the linkage reveals

Every control records `curriculum_nodes`, validated against `math_node()` by
`every_control_cites_a_corpus_entry_and_a_curriculum_node`, so the link cannot
drift from `docs/curriculum/curriculum.toml`. Measured coverage:

| decidability class | nodes | with a negative control |
|---|---:|---:|
| `decidable` | 1 | **1** |
| `computable` | 6 | **6** |
| `bounded` | 16 | **8** |
| **total** | **23** | **15** |

`computable` was 5 of 6 when I first measured it: **`divisibility-and-euclid`
claimed `computable` and `covered` with no misconception-backed evidence at all**,
even though the corpus is full of divisibility and parity errors. That is exactly
the finding J3 asked for, and rather than only report it I closed it — the four
controls `two_is_prime`, `one_has_two_distinct_divisors`, `odd_plus_odd_is_odd`
and `century_year_is_a_leap_year` were added specifically for that node.

Eight `bounded` nodes still have no negative control. Four of them
(`cardinality`, `complex`, `sequences-and-limits`, `calculus`) are already
`status = "lean-horizon"` and are honestly labelled — the corpus's misconceptions
in those areas are exactly my category B, so the classification and the evidence
agree.

The four that claim `status = "covered"` with no refutable misconception behind
them are the finding worth reporting:

- **`induction`** — the corpus's inductive-reasoning misconceptions
  (`examples-are-proof`, `proof-is-just-checking-lots`) are about the *gap*
  between checking and proving, which I routed to `proof-methods` and
  `number-theory` instead. Nothing in the corpus attacks the induction schema
  itself.
- **`relations-and-functions`** — `any-rule-is-a-function` is the natural
  candidate (`x² + y² = 1` is not a function of `x`), but every encoding I tried
  either needed a witness or collapsed into contradicting its own premise. A real
  control here wants finite function tables, which the `Relation` family already
  has.
- **`reals`** — every reals misconception in the corpus is category B (limits,
  irrationality, `0.999…`). The `bounded` class is defensible, but there is no
  misconception-shaped evidence for it and there will not be until the ladder
  climbs.
- **`rings`** — the corpus has no ring-theoretic misconception at all. This is a
  gap in the *corpus*, not in axeyum.

So: the `decidable` and `computable` classes now carry real negative-control
evidence, and exactly one `bounded` node (`reals`) claims coverage that the
corpus cannot supply evidence for at our current fragment.

---

## 5. Misconceptions I believe are themselves wrong

Detail and line citations in `FEEDBACK.md` §A. In short:

1. **`fraction-is-two-numbers-not-one.md:25`** — the distractor's stated
   conclusion, `3/4 > 1/2`, is **true**. Only the reasoning is wrong. Every other
   distractor I read is false as stated. An assessment generator or a
   negative-control suite that treats these uniformly will mark a correct answer
   wrong. Reported, not corrected.
2. **`even-means-ends-in-even-digit.md:16`** — "3.4 is even" is ill-typed rather
   than false, by the file's own diagnosis. Different kind of object from its
   sibling distractor.
3. **Ten live near-duplicate pairs** beyond the one deprecation, two of which
   share an identical distractor string. "148 misconceptions" overstates the
   distinct content by roughly 7%.
4. **147, not 148** live misconceptions.

---

## 6. Top three roadmap items

**1. An UNSAT evidence route for `Int` and `Real` in `axeyum-scenarios`.**
This is the single change that would most enlarge this suite, and it is the one
place where the crate's design actively blocked me. Fifteen of the eighty-six
refutable misconceptions are naturally QF_LRA — Bayes, conditional probability,
expected value, compound growth, least squares. Today an UNSAT scenario must live
over `Bool`/`BitVec` because `check_unsat` proves UNSAT by enumeration and
`lib.rs:544` `unreachable!()`s on `Sort::Int`. I hand-translated four into scaled
integers; the translation is sound but it is a step the reader has to trust, and
it does not scale. What is wanted is a second `UnsatEvidence` kind for ordered
fields — a bounded rational grid, or explicit certificate-carrying evidence
(Farkas is already in the `artifacts/examples/math/` packs) — so the `Rational`,
`Real` and `RealAlgebra` families can carry negative controls at all. Right now
those four families are structurally confined to SAT-by-construction, which means
**the ordered-field half of the stack has no negative controls whatsoever.**

**2. Promote `premises_alone_are_satisfiable` and the must-be-SAT control into a
general pattern for every self-checking family.**
Two campaign lanes yesterday found controls that did not fire and guards that
were removable with everything still green. My guard 5 caught exactly that class
of bug in my own code, first run, before I had any reason to suspect it. The
pattern generalises cheaply: any suite asserting `unsat` should also assert that
its constraints minus the claim are `sat`, and should carry at least one
deliberately satisfiable sibling. Neither costs more than a few lines, and
neither can be satisfied by a suite that has quietly stopped working. I would
also make `UnsatEvidence::Sampled` opt-in per scenario rather than a silent
degradation above `EXHAUSTIVE_BIT_LIMIT` — today a scenario that grows past 20
bits keeps returning `Ok` while its proof becomes 4096 spot checks.

**3. Grow the corpus upward, not the suite sideways.**
Seven of the seventeen out-of-fragment misconceptions are about **limits**, three
about **cardinality**. That is a sharper statement of what the next rung buys than
any roadmap prose: closing limits alone would move 7 of 17 declines into the
refutable set and would give `reals` and `sequences-and-limits` the evidence their
decidability classes currently lack. Conversely, adding a thirty-third control in
QF_BV arithmetic adds nothing — the fragment is already demonstrated at 32-for-32
with zero wrong answers. The marginal value is entirely upward. A secondary note
for the corpus owners: `rings` has no misconception at all and
`relations-and-functions` has one that resists formalisation, so if the corpus is
meant to double as an evaluation set, those are the two areas worth authoring
into.

---

## 7. Not done, deliberately

I did **not** add a pack under `artifacts/examples/math/`. The 174 existing packs
are validated by `scripts/validate-foundational-example-pack.py` and gated by
`just foundational-resources` inside `scripts/check.sh`; a pack that did not
conform would break the aggregate gate for every other lane. The Rust suite is
the stronger artefact anyway — it is executed by `axeyum-solver`'s differential
test on every run, which no example pack is. If a pack is wanted, it should be a
separate, reviewed change.
