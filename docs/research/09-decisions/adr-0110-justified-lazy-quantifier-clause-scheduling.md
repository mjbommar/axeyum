# ADR-0110: Justified lazy quantifier-clause scheduling

Status: accepted
Date: 2026-07-11

## Context

P2.6 T2.6.3 calls for Z3-style lazy evaluation of ground instances of
clause-form universals: an already-true clause is redundant, an all-false
clause is a conflict, and a clause with one undetermined literal is unit-like.
The current e-matching loop instead adds every matched full body before asking
the ground solver to check it. A quantifier with many matches can therefore
flood the ground query even when all but one instance is already satisfied by
the current equality context.

Z3's `q_clause`/`q_eval` can propagate only the remaining literal because it
records SAT/e-graph justifications for every false literal. Axeyum's current
quantified evidence route records genuine source instances, but does not yet
carry a solver-context implication that would justify a detached literal.
Emitting the remaining literal by itself would therefore outrun the replay
contract: a universal clause does not entail one of its literals
unconditionally.

The exact public quantified-UF corpus cannot measure this engine boundary yet:
all five rows stop earlier at uninterpreted-sort parsing. A ground-BV/UF stress
shape can isolate it without that front-end dependency: many distinct `f(a_i)`
trigger matches, clauses made true by `g(a_i) = one`, and one match whose two
literals are both false.

## Decision

Add an internal, justification-aware scheduler for e-matched universal
instances, while retaining full source instances as the only asserted
consequences.

For a quantifier-free body that is a disjunction of equality or disequality
literals, the scheduler:

1. builds congruence closure from top-level asserted equalities and records
   top-level asserted disequalities;
2. evaluates each matched ground clause in three values against only those
   recorded unit facts and their congruence consequences;
3. drops an instance from the current batch when any literal is true;
4. schedules the complete genuine source instance first when all literals are
   false or exactly one is undetermined;
5. defers clauses with multiple undetermined literals until no fresh
   conflict/unit-like instance is available; and
6. treats unsupported/non-clausal bodies as deferred legacy instances.

The public `instantiate_forall_via_egraph` and
`witness_tuples_via_egraph` APIs keep returning the complete deterministic
match set. Proof/evidence generation therefore remains independent of search
scheduling. The solver loop still grants `Unsat` only after the ordinary
quantifier-free solver refutes the ground assertions plus complete source
instances.

This is the first T2.6.3 slice, not the final incremental quantifier engine.
Detached-literal propagation requires explicit equality/disequality
justifications integrated with the online SAT context and receives a later ADR.

## Acceptance

- A deterministic stress test produces hundreds of genuine matched instances,
  classifies all but one as redundant, and schedules the single all-false source
  instance first.
- Unit tests cover true, all-false, one-undetermined, multi-undetermined, and
  non-clausal fallback behavior, including congruence-derived equality truth.
- The stress query remains `Unsat`; the selected term is verified to be one of
  the legacy complete source instances and independently refutes with the
  original ground assertions.
- Existing bounded-instance soundness, multi-round e-matching, quantified
  evidence, and public quantified LIA/BV regressions do not lose decisions or
  replay coverage.
- The selected batch materially reduces first-check ground assertions and wall
  time on the committed stress target, without disagreement or a new trust
  step.
- Workspace tests, Clippy, warning-denied rustdoc, links, foundational
  resources, formatting, and generated matrices pass, subject to documented
  pre-existing aggregate-test exclusions.

## Alternatives

- **Assert only the undetermined literal.** Rejected for this slice: the false
  sibling literals are context assumptions, not universal consequences, and
  the current evidence object cannot replay their implication.
- **Drop every multi-undetermined instance permanently.** Rejected: several
  clauses may constrain one another only after entering the ground solver.
- **Replace the loop with a full MAM plus incremental SAT integration now.**
  Deferred: it is the destination, but clause scheduling is independently
  measurable and preserves the current proof boundary.
- **Use the exact quantified-UF public slice as the gate.** Deferred until
  uninterpreted-sort parsing reaches the quantifier engine.

## Consequences

- Redundant matches no longer enlarge the active ground conjunction, and an
  immediate conflict/unit-like instance reaches the QF solver before unresolved
  clause traffic.
- Classification remains conservative: absent a recorded unit justification,
  a literal is undetermined. This can miss pruning but cannot create a verdict.
- The implementation initially rebuilds a small equality context per
  quantifier batch. T2.6.1 MAM/incremental e-graph work can make that state warm
  after measurement shows construction cost is material.
- The next T2.6.3 step is to expose replayable clause-evaluation justifications
  to the online CDCL(T) loop; T2.6.1 then makes matching incremental on merges.

## Validation

- The committed 256-match stress shape produces 256 complete legacy source
  instances. Lazy evaluation proves 255 redundant from recorded equality facts
  and schedules the one all-false complete source instance. The selected term is
  in the legacy match set, and the original ground assertions plus that term
  independently re-decide `Unsat`.
- Five optimized repetitions measured median end-to-end batch-plus-QF time of
  4.237 ms for eager full-instance insertion and 2.524 ms for lazy scheduling, a
  40.4% reduction. Median QF time fell from 2.605 ms to 1.692 ms (35.0%); active
  instances fell 256 to 1 (99.6%). Timing is informational, while semantic and
  work-count assertions are deterministic test gates.
- The 54-row cvc5-derived quantified-BV slice is decision-identical to its
  committed baseline: 29 SAT, 9 UNSAT, 5 unknown, 11 unsupported, no expected
  status mismatch, error, or replay failure. PAR-2 changed 7.4696 to 7.4714
  seconds (0.025%). The 12-row quantified-LIA slice remains 4 SAT / 8 UNSAT,
  with no unknown, unsupported, error, or replay failure.
- The 5-row Bitwuzla-derived slice decides four expected UNSAT rows. Its SAT row
  is rejected by the broader current tree's quantified-model replay gate; this
  predates and is unreachable from the UNSAT-only scheduler, but prevents a
  clean whole-slice claim. The generic benchmark Z3 adapter still declines
  quantified formulas, so the direct quantified-BV differential is the oracle
  gate and passes two suites with zero disagreement.
- E-matching unit tests pass 29/29, the independent bounded-instance harness
  passes 900 deterministic seeds, the all-feature solver library passes 833/833,
  and focused quantified evidence, instantiation, MBQI, and model-finder suites
  pass. Two stale evidence tests were corrected to expect ADR-0100's accepted
  checked closed-universal certificate, which now intentionally precedes the
  older finite-expansion variant.
- The 2,000-case quantified-UFLIA model-finder differential remained CPU-active
  at 15 minutes and 1.3 GB RSS and was stopped; no pass is claimed. The smaller
  MBQI/model-finder suites completed, and the quantified-BV direct-Z3 fuzz
  completed with zero disagreement.
- Workspace all-target/all-feature Clippy, warning-denied rustdoc, links,
  formatting/diff, capability/support goldens (2/2 and 12/12), and the
  137-concept/174-pack foundational-resource gate pass. The known Sturm
  nontermination still precludes a whole-workspace aggregate claim.
