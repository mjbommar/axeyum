# ADR-0117: Source-bound detached quantifier-literal propagation

Status: accepted
Date: 2026-07-11

## Context

ADR-0110 classifies an e-matched equality/disequality clause as redundant,
conflicting, unit-like, or unresolved, but still sends a complete source
instance to the QF solver. This preserves soundness because a universal entails
the complete instance. It cannot send only the one undetermined literal: the
universal does not entail that literal without the current facts that make every
sibling false.

Z3's `q_eval` records e-graph equality/disequality evidence while evaluating a
quantifier clause, and its SAT justification contains the quantified clause,
binding, and those context antecedents. Axeyum has the same ingredients in a
different architecture: retained e-matching carries the source quantifier and
witness tuple, the e-graph can explain derived equalities by input reason ids,
and recorded disequalities retain direct ground assertions. The QF boundary is
currently a fresh `check_auto` call rather than one online SAT instance, so the
derived literal must be checked before it enters that call.

Generated full instances can themselves become equality premises in later
rounds. Accepting them without recursively carrying their instantiation
provenance would merely move the trust hole. The first route therefore uses only
original quantifier-free source assertions as false-sibling reasons.

## Decision

Introduce a public arena-bound
`QuantifierClausePropagationCertificate` containing:

1. the original universal assertion and one ordered ground binding tuple;
2. the exact reconstructed complete source instance;
3. the detached equality/disequality literal;
4. every false sibling literal; and
5. for each false sibling, the sorted source ground equality/disequality terms
   that justify its value.

An independent checker accepts a certificate only when:

1. the asserted universal and every reason occur in the untouched original
   assertion set, with reasons restricted to quantifier-free top-level
   equality/disequality assertions;
2. substituting the carried tuple for the universal prefix reconstructs the
   exact source instance;
3. flattening that instance as a Boolean disjunction yields the detached literal
   exactly once and every other literal exactly as carried;
4. a fresh e-graph built only from each sibling's named reasons evaluates that
   sibling false; and
5. the clause contains exactly one undetermined literal and at least one false
   sibling in the producer's current source-ground context.

The quantifier loop checks every certificate before adding its detached literal
to the next QF call. All-false clauses still add the complete source instance;
multi-undetermined and unsupported clauses retain the deferred complete-instance
fallback. Public one-shot instantiation remains unchanged.

The checker is the soundness boundary. Search-side e-graph explanations and
disequality lookup are untrusted certificate construction. A malformed,
non-source, incomplete, duplicated, or stale reason set can only make the
checker decline and fall back to the complete source instance.

## Acceptance

- Reflexive, direct-equality, transitive/congruence-equality, direct-disequality,
  equality-transported disequality, positive/negative literal, and Boolean-false
  sibling justifications replay from named source facts.
- Wrong quantifier, tuple, instance, detached literal, sibling, reason,
  missing reason, duplicate literal/reason, and generated-premise tamper cases
  are rejected.
- Checked detached and complete-instance modes return identical decisions and
  complete witness sets across single/multi-pattern and multi-round cases.
- A committed one-undetermined-clause target materially reduces active QF DAG or
  wall time versus adding complete instances, with identical ground verdict.
- Quantified-BV/LIA decisions, replay, direct-Z3 differential results, and PAR-2
  do not regress; evidence production from original assertions remains unchanged.
- Solver, bounded-instance, evidence, MBQI, bench, Clippy, rustdoc, links,
  foundational resources, formatting, and generated-matrix gates pass.

## Acceptance result

Accepted on 2026-07-11. The public arena-bound certificate carries the original
universal, ordered binding tuple, exact complete instance, propagated literal,
and ordered false siblings with sorted source reasons. The batch checker builds
one fresh context from original top-level equality/disequality assertions,
reconstructs every instance, confirms its unique unit shape, and independently
replays each sibling from only its named reason subset. It never reads retained
matching state.

Producer explanations cover direct/reflexive/transitive/congruence equality,
direct and equality-transported disequality, negative/positive literals, and
Boolean false. Wrong assertion, tuple, source instance, propagated/sibling
literal, missing/wrong/duplicate/non-source reason, duplicate sibling, and
generated-premise cases reject. A generated equality used by a later clause
therefore falls back to the complete source instance. Existing single-literal,
all-false, multi-undetermined, non-clausal, multi-pattern, and multi-round paths
retain their prior behavior.

The committed target has 128 matches and six false siblings per instance. Full
and detached modes both refute, but reachable query DAG nodes fall
4,230→2,438 (42.4%) and tree nodes 10,121→4,745 (53.1%). Five optimized
eager/detached QF measurements in microseconds were 8265/3222, 7244/3152,
7823/3226, 8250/3297, and 8285/3312: medians 8.250/3.226 ms, a 60.9% reduction
and 2.56x speedup. Checked end-to-end measurements were 11301/9886,
10240/10245, 10801/10100, 11695/9325, and 12184/9542: medians
11.301/9.886 ms, a 12.5% reduction and 1.14x speedup including matching,
certificate construction/replay, and QF solving.

The cvc5 quantified-BV slice remains 29 SAT / 9 UNSAT / 5 unknown / 11
unsupported with zero status mismatches, errors, or replay failures and PAR-2
7.46892 s. Three quantified-LIA runs remain 12/12 with PAR-2 means
0.11825/0.11765/0.11850 s (median 0.11825 s). All 1,000 direct-Z3 quantified-BV
and 900 bounded-instance cases agree. The Bitwuzla slice retains four expected
UNSAT decisions and its pre-existing SAT model-replay rejection.

E-graph 35/35, quantifier matching/propagation 47/47, solver library 851/851,
evidence 69/69, MBQI 13/13, and bench 7/7 pass, as do workspace
all-target/all-feature Clippy, warning-denied rustdoc, links, formatting/diff,
generated capability and support matrices, and 137-concept/174-pack
foundational resources. All 26 configured reference checkouts remain present.

## Alternatives

- **Trust the retained clause classification.** Rejected: producer and consumer
  would share mutable e-graph state, so no independent replay boundary exists.
- **Name the complete ground vector as reasons.** Rejected: it obscures the
  antecedent and can admit generated terms without their provenance.
- **Allow generated full instances as reasons.** Deferred until certificates can
  recursively bind each generated premise to its source quantifier and tuple.
- **Wait for one monolithic online CDCL(T)+MAM rewrite.** Rejected: the checked
  implication is useful and measurable at the existing QF boundary, and its
  certificate is reusable by the future online justification object.
- **Detach an all-false clause.** Rejected: it has no remaining literal; the
  complete source instance is already a direct conflict consequence.

## Consequences

- Unit-like equality clauses can cross the current QF boundary as one checked
  literal instead of a complete disjunction.
- The retained session gains source-ground provenance and deterministic reason
  extraction, but public decision/evidence envelopes do not change.
- Recursive generated-premise chains, direct SAT-clause insertion, non-equality
  theory literals, and proof-format serialization remain later integrations.
