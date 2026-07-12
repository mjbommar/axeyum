# ADR-0131: Checked signed-interval quantified-BV models

Status: accepted
Date: 2026-07-12

## Context

After ADR-0130, `intersection-example-onelane` is the smallest unsupported row
in the public cvc5 quantified-BV slice. Its one assertion has shape
`not (exists b. antecedent => conclusion)`. Under a suitable complete model for
12 free `BV32` symbols, the outer conclusion is false and every ground
antecedent fact is true. The only binder-dependent antecedent is itself an
implication from a signed interval `lower <=s b <=s upper` to ground facts and
`b <=s cap`.

The source contains signed division, including `bvsdiv 1 2`, but all division
terms are binder-free. Candidate search may exploit their evaluated values;
the evidence must not assume a normalization such as mathematical rational
division, trust implication vacuity, or accept a solver model without checking
the quantified source.

cvc5's `BvInverter` finds invertible paths and its CEGQI-BV instantiator
separately normalizes binder-bearing additions and multiplications. Signed
division is deliberately absent from the inverter's direct invertible-path
list. Z3's model checker evaluates uninterpreted symbols in the candidate
model, substitutes fresh skolems, asserts the negated quantified body in an
auxiliary context, and accepts a model only when that counterexample query is
unsatisfiable. These are candidate-generation guides, not Axeyum evidence.

## Decision

**Extend `QuantifiedBvModelSatCertificate` with one directly checked
`NegatedExistentialIntervalImplication` proof form. Search may propose a
complete free-BV model through QF_BV, but canonical SAT credit requires an
independent proof over the untouched source.**

The checker admits exactly one directly negated existential binder and one
outer implication. It flattens the outer antecedent and requires exactly one
binder-dependent conjunct. That conjunct must be an implication whose premise
is exactly two signed bounds, `lower <=s b` and `b <=s upper`, and whose
conclusion contains exactly one binder-dependent leaf, `b <=s cap`. Every
other term must be binder-free.

Under the certificate's exact, sorted, complete free-symbol assignment, the
checker:

1. evaluator-replays every binder-free antecedent leaf to `true`;
2. evaluator-replays the untouched outer conclusion to `false`, including all
   signed-division semantics;
3. evaluates `lower`, `upper`, and `cap` as exact BV values; and
4. proves both `lower <=s upper` and `upper <=s cap` using arbitrary-width
   two's-complement comparison.

The first comparison is mandatory. Empty intervals decline rather than receive
credit through vacuity. Together the comparisons prove that every binder value
inside the nonempty source interval satisfies its required cap; values outside
the interval satisfy the inner implication directly. Thus the outer antecedent
is true and its conclusion false for every binder value, so the existential is
false and the asserted negation is true.

Existing ADR-0130 source admission remains in force: Bool/BV only, no function
applications, unique binders, exact free-symbol coverage, at most 128 binders,
4,096 complete source DAG nodes, depth 256, and 4,096 total free-BV bits.

Untrusted search extracts only the corresponding sufficient ground QF_BV
obligations: all ground antecedent leaves, `lower <=s upper`, `upper <=s cap`,
and the negated outer conclusion. The ordinary QF_BV solver proposes values for
all free symbols under the shared deadline. Missing unconstrained values are
deterministically completed with zero. The result is discarded unless the
source checker and canonical `check_model` both accept it.

## Evidence

`intersection-example-onelane` moves from unsupported to checked SAT. Five
release corpus samples report target solve times 36.477393, 36.338867,
38.899419, 39.272877, and 37.681117 ms (median 37.681117 ms). Separate
evidence-production samples are 32.651, 32.914, 33.267, 33.429, and 34.863 ms
(median 33.267 ms).

The 54-row public cvc5 quantified-BV slice is now 34 SAT / 17 UNSAT / 0 unknown
/ 3 unsupported, with 51 expected-status agreements and no disagreement,
error, or replay failure. Five PAR-2 samples are 1.200739, 1.200402, 1.200617,
1.200837, and 1.200235 seconds (median 1.200617 seconds). Exactly the target
changes outcome.

The dominance audit certifies and checks all 51 decisions, marks 42/51 dominant
candidates, and retains Lean coverage at 8/17 UNSAT. The target evidence kind
is `quantified-bv-model-sat`; it rechecks with no trust steps or holes.

Nine focused tests cover both public models, evidence replay, free-value,
binder, witness, source, and certificate tampering, empty-interval and
binder-leakage rejection, source caps, nonlinear/polarity near misses, and 96
direct-Z3 comparisons. The 32 new interval cases comprise 16 certified SAT
models and 16 UNSAT controls; controls are decided or safely declined. The
cumulative quantified-BV direct-Z3 suite now covers 1,816 cases and controls
with no disagreement. Strict all-target solver Clippy and adjacent evidence,
free-Boolean model, alternation, and quantified-BV differential suites pass.
The complete workspace `just check` also passes, including formatting, strict
Clippy, all tests, warning-denied rustdoc, foundational-resource validation,
generated-document consistency, and link checking.

## Alternatives

- **Trust QF_BV obligations as a proof of the quantified source.** Rejected:
  those obligations are a sufficient-condition search query assembled by
  untrusted code. The source checker re-extracts and proves the contract.
- **Normalize `bvsdiv 1 2` to zero before checking.** Rejected: the checker
  evaluates the untouched ground term using SMT-LIB total BV semantics.
- **Accept an empty interval.** Rejected: although the source implication would
  be vacuous, this certificate intentionally requires a positive containment
  proof and cannot use vacuity as evidence.
- **Enumerate all 32-bit binder values.** Rejected: interval containment is a
  constant-size complete proof for this source class.
- **Generalize to arbitrary binder-dependent consequents.** Deferred: the next
  row contains a nonlinear polynomial under a ground zero multiplier and needs
  its own exact proof rule, not an unchecked extension of interval matching.
- **Treat the candidate solver's SAT model as MBQI evidence.** Rejected: model
  search and source validation remain separate.

## Consequences

Axeyum can now certify a complete free-BV model for one directly negated
existential implication when all binder dependence is isolated in a nonempty
signed interval contained by a signed cap. Ground signed division is supported
only by exact evaluator replay after model completion. This is not general BV
MBQI, arbitrary implication reasoning, nonlinear binder arithmetic, nested
alternation, functions/arrays, proof serialization, or Lean SAT
reconstruction.

The next measured unsupported row is `gn-wrong-091018` at 88 DAG nodes. It has
a similar directly negated existential implication, but its interval conclusion
contains nonlinear binder arithmetic under a binder-free zero-producing signed
division factor. Any next contract must prove that annihilation from exact
source semantics and then replay the remaining inequality; ADR-0131 does not
silently admit it.
