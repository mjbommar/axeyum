# agent-j — feedback

Two audiences: the `math-education` corpus, and axeyum itself. Everything is
cited by file and line. Per the brief I have **not** edited anything in
`math-education`; these are reports for review.

---

## A. The corpus may itself be wrong (report, do not silently correct)

### A1. A distractor whose stated conclusion is TRUE

`../math-education/graph/misconceptions/fraction-is-two-numbers-not-one.md:25`

```
  - text: "3/4 has to be bigger than 1/2, because 3 and 4 are both bigger than 1 and 2."
```

`3/4 > 1/2` **is true**. Only the reasoning is wrong. Every other
`distractor_forms[].text` in the corpus that I read is a claim that is false as
stated; this one is not, and the file gives no signal that it differs.

Why this matters beyond pedantry: `AUTHORING.md:57` describes
`distractor_forms` as text "an assessment item can reference by id, so a wrong
answer says HOW a learner is wrong". An assessment generator, or a
negative-control suite like mine, that treats these as false statements will
mark a **correct** answer wrong here. I classified it `A2` in `census.tsv`
rather than `A1` precisely because the refutable object is the extracted rule
("`a > c` and `b > d` implies `a/b > c/d`", refuted by `3/10 < 1/2`), not the
sentence.

Suggested fix, for a human to make: either change the numbers so the conclusion
is also false (e.g. "3/10 has to be bigger than 1/2, because 3 and 10 are both
bigger than 1 and 2"), or add a field marking that this distractor's error is in
the justification rather than the conclusion.

The sibling file `fraction-is-two-numbers.md:25` has the same misconception with
distractors that *are* false ("3/4 is smaller than 5/8"), so the pattern is
achievable.

### A2. A distractor that is a category error rather than a false claim

`../math-education/graph/misconceptions/even-means-ends-in-even-digit.md:16`

```
  - text: "3.4 is even, because it ends in a 4."
```

The file's own diagnosis says evenness "isn't even defined" for a non-integer.
So this distractor is not false, it is ill-typed. That is a legitimate
pedagogical object but it is a different kind of thing from the second
distractor in the same file ("24 isn't even"), which is straightforwardly false.
Worth a schema distinction if the corpus is ever consumed mechanically.

### A3. Eleven near-duplicate pairs, one of them deprecated

Exactly one file carries `status: deprecated`
(`accurate-test-means-positive-result-is-reliable.md:14`, replaced by
`base-rate-neglect-error`). The remaining ten pairs are live duplicates:

| | |
|---|---|
| `fraction-is-two-numbers-not-one` | `fraction-is-two-numbers` |
| `proof-means-formal-symbols` | `proof-needs-symbols` |
| `infinity-is-a-number` | `infinity-is-a-very-big-number` |
| `zero-is-neither` | `zero-is-not-even` |
| `point-nine-recurring-is-less-than-one` | `zero-point-nine-repeating-is-slightly-less-than-one` |
| `longer-decimal-is-bigger` | `more-decimals-is-just-more-digits` |
| `survivorship-bias-error` | `studying-winners-explains-winning` |
| `gamblers-fallacy-belief` | `law-of-averages-corrects-past-outcomes` |
| `random-means-patternless` | `random-means-uniform` |
| `examples-are-proof` / `one-example-proves-it` | `proof-is-just-checking-lots` |

`longer-decimal-is-bigger.md:19` and `more-decimals-is-just-more-digits.md:16`
carry the **identical** distractor string, "0.45 is bigger than 0.5, because 45
is bigger than 5."

This is a measurement, not a complaint: it means "148 misconceptions" overstates
the distinct content by roughly 7%. Anything that reports coverage as a fraction
of 148 should say so.

### A4. The count everyone will quote is 148; the live count is 147

`grep -c` over the directory gives 148 files.
`grep -h '^status:' * | sort | uniq -c` gives **147 draft, 1 deprecated**.
`coordinator/NEXT-MATH-STACK.md` says 148, which is right as a file count and
wrong as a count of live misconceptions. My census uses 147 as the denominator
and says so.

---

## B. axeyum

### B1. `Sort::Int` and `Sort::Real` are `unreachable!()` in the scenarios enumerator

`crates/axeyum-scenarios/src/lib.rs:544` and `:547`

```rust
Sort::Int => {
    unreachable!("scenarios do not declare integer symbols for enumeration")
}
```

Consequence, which I hit head-on: **an UNSAT scenario in this crate can only be
over `Bool`/`BitVec` symbols.** `Scenario::check_unsat` enumerates every declared
symbol, and an `Int` or `Real` symbol aborts the process rather than returning an
error. So the `Integer`, `Real`, `Rational` and `RealAlgebra` families are
structurally confined to SAT-by-construction scenarios.

That is a real gap for exactly this task. 15 of the 86 refutable misconceptions
in the census land naturally in QF_LRA (`base-rate-neglect-error`,
`the-second-probability-stays-the-same`, `expected-value-is-the-most-likely-outcome`,
`gamblers-fallacy-belief`, `probability-of-two-options-is-always-half`, …). I
encoded four of them by hand as scaled integers over bit-vectors, which works but
is a translation the reader has to trust. The other eleven are in the census as
`A2`, unbuilt.

Suggestion: an UNSAT evidence variant for `Int`/`Real` that is *not* enumeration
— a bounded-box rational grid, or an explicit "checked by construction" evidence
kind carrying the algebraic derivation. The current design says "UNSAT means we
enumerated it", and that is precisely why the ordered-field families have no
negative controls.

### B2. `EXHAUSTIVE_BIT_LIMIT = 20` is the right idea but the cliff is silent

`crates/axeyum-scenarios/src/lib.rs:157`

Above 20 bits, `check_unsat` silently degrades to `UnsatEvidence::Sampled` — 4096
draws — and `self_check()` still returns `Ok`. A scenario that grew past the
limit would keep passing while its "proof" quietly became a spot check. Nothing
in the crate distinguishes the two at the call site.

My suite asserts `matches!(evidence, UnsatEvidence::Exhaustive { .. })` in
`misconception.rs` for exactly this reason, and the builder asserts the bit
budget at construction time. I would promote both: either make `Sampled` opt-in
per scenario, or have `catalog()`-level tests refuse it by default. This is the
same shape as the failures in the CLAUDE.md gotchas list — a green result that
does not mean what it says.

### B3. Adding a family to `catalog()` silently widens three solver test suites

`crates/axeyum-scenarios/src/lib.rs:537` is now the only edit needed to put a new
scenario through `axeyum-solver`'s `tests/scenarios.rs`, `tests/incremental.rs`
and `tests/incremental_bv.rs`. That is a genuinely good property — it let me wire
32 negative controls into the solver differential path without touching
`crates/axeyum-solver/`, which is another lane's territory.

It is also a hazard: a lane adding an expensive scenario to `catalog()` slows
three other suites with no local signal. Measured cost of my 35 scenarios:
**~0.70 s** of self-check (`logs/` has the per-scenario table) and **~0.09 s** of
solver time. Cheap, but only because I went back and shrank three domains after
measuring — `matrix_product_entrywise` originally declared four symbols its
assertion never reads, which alone cost 854 ms. A `catalog()`-budget test would
have told me that instead of a stopwatch.

### B4. `docs/curriculum/curriculum.toml` decidability classes now have uneven evidence

Measured against the 32 controls (script output in `RESULT.md`): 14 of 23 nodes
carry a negative control. Breaking that down by the class the node *claims*:

- `decidable` — 1 of 1 has one.
- `computable` — 5 of 6 have one. The exception is
  **`divisibility-and-euclid`** … which I then closed, deliberately, by adding
  `two_is_prime`, `one_has_two_distinct_divisors`, `odd_plus_odd_is_odd` and
  `century_year_is_a_leap_year`. So `computable` is now 6 of 6.
- `bounded` — 8 of 16.

The eight `bounded` nodes with no negative control are `induction`,
`relations-and-functions`, `cardinality`, `reals`, `complex`, `rings`,
`sequences-and-limits`, `calculus`. Four of those are already
`status = "lean-horizon"` and are honestly labelled. The four that claim
`status = "covered"` and have no refutable misconception behind them are
**`induction`, `relations-and-functions`, `reals`, `rings`** — see RESULT.md for
which corpus entries would serve and why I did not build them.
