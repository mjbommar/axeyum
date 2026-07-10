# ADR-0069: Ground-Distinct UFBV Interface Pruning

Status: accepted
Date: 2026-07-09

## Context

ADR-0066 initially generated argument and result equalities for every pair of
applications of the same uninterpreted function. ADR-0068 made those equalities
useful to the BV theory, but the pair set remained quadratic. On `bug520`, four
tables are each applied at four distinct concrete byte keys and one symbolic
key. Pairwise generation produced result equalities even between, for example,
`table0(#x00)` and `table0(#x01)`, although their congruence antecedent is
identically false.

This is more than redundant Boolean structure. The impossible pairs consume
the interface admission budget and the bounded implication-probe budget, and
they make the canonical driver search arrangements that cannot correspond to a
UF congruence obligation. Arbitrarily omitting dynamic pairs would be
incomplete; using syntax alone would incorrectly omit syntactically different
ground expressions that denote the same value.

## Decision

Filter same-function application pairs by exact ground argument values before
generating interface atoms.

- Evaluate each distinct original argument at most once under an empty
  assignment, caching either its exact `Value` or evaluation failure.
- Omit an application pair only when at least one corresponding argument pair
  evaluates successfully on both sides and the resulting values differ. Then
  the conjunction of argument equalities is false in every model, so UF
  congruence imposes no result equality for that pair.
- Keep a pair when arguments are syntactically equal, evaluate to equal values,
  mention symbols/functions, or otherwise fail ground evaluation. Unknown is
  never treated as disequality.
- Preserve deterministic discovery order. Poll the shared deadline while
  filtering, and stop as soon as retained pairs exceed the 512 raw-interface
  admission budget so the cap also bounds temporary pair storage.
- Generate the existing argument/result equality atoms, BV propagation
  candidates, e-graph terms, and replay route unchanged for every retained
  pair. Eager Ackermann elimination remains the certifying fallback.

This is an exact static relevance slice, not dynamic model-based combination.
Pairs with symbolic arguments remain quadratic and conservatively bounded.

## Soundness Argument

For applications `f(a1, ..., an)` and `f(b1, ..., bn)`, functional consistency
requires

`(a1 = b1 and ... and an = bn) -> f(a1, ..., an) = f(b1, ..., bn)`.

If ground evaluation proves `ai` and `bi` denote different values for any
position `i`, then `ai = bi` is false under every assignment. The implication
is therefore valid without a result-equality atom. No other pair is omitted.
Ground evaluation uses the same total Bool/BV reference semantics that anchors
model replay, and any evaluation error conservatively retains the pair.

## Evidence

- A mechanism gate with keys `0`, `1`, and symbolic `x` retains only the two
  potentially congruent pairs: four deduplicated argument/result atoms.
- An adversarial gate uses syntactically different ground terms `1 + 1` and
  `2`; equal evaluation keeps the pair and unequal UF results are refuted.
- A 24-entry concrete-key table previously exceeded the quadratic 512-interface
  cap. It now solves `Sat` with zero generated interface atoms. The control with
  24 symbolic keys remains a first-class `ResourceLimit` outcome.
- `bug520` drops from 50 to 20 deduplicated interface atoms. A diagnostic run
  records 69 implication probes, 14 BV hits, and 16 combined driver
  propagations, versus 93/31/46 before pruning.
- Three deterministic 512-case matrices remain clean: direct online/eager,
  front-door/eager, and direct online/Z3 (1,536 comparisons). The public corpus
  remains 6/6 decided and agreeing with zero replay failures.

An exact release-mode A/B changed only the relevance predicate. The disabled
control has five stable samples; enabled has ten samples because two scheduler
outliers were observed and retained:

| configuration | corpus PAR-2 mean | `bug520` |
|---|---:|---:|
| pruning enabled | median 2.89 ms (2.64-5.06 ms) | median 8.88 ms (8.35-19.19 ms) |
| pruning disabled | median 3.84 ms (3.78-3.90 ms) | median 15.32 ms (15.06-15.76 ms) |

The median improvement is about 1.33x for the six-row mean and 1.72x for
`bug520`. Z3 measured 8-10 ms on that row in the same enabled runs, so Axeyum's
median is in the same narrow row-level band. This is not a division-wide or
general UFBV parity claim; the public corpus contains only six instances.

## Alternatives

- **Keep all pairwise atoms.** Sound and complete, but measured slower and
  rejects concrete lookup tables solely because of impossible pairs.
- **Compare argument syntax only.** Rejected: different ground terms may denote
  the same value, as the `1 + 1` versus `2` gate demonstrates.
- **Treat failed ground evaluation as distinct.** Rejected as unsound. Failure
  means unknown, not disequal.
- **Use current BV model values to omit pairs permanently.** Rejected: model
  choices are not entailments. Dynamic model-based interface creation requires
  a refinement mechanism that can add obligations after a candidate model.
- **Pre-solve every symbolic argument pair for disequality.** Exact but too
  expensive at construction time; bounded online implication probes already
  own that reasoning during search.

## Consequences

- Concrete table applications no longer create quadratic impossible
  congruence obligations or consume the online interface cap.
- `bug520` reaches row-level median performance comparable to Z3 in release
  mode, while all agreement and replay gates remain clean.
- Symbolic application sets still require pairwise candidates. The next scale
  step is dynamic/model-based interface creation or another entailment-backed
  relevance mechanism, not a larger static cap.
- Arrays, mixed BV+LIA, and online proof production are unchanged. The eager
  reduction and evidence routes remain available.
