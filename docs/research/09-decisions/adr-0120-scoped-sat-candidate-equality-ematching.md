# ADR-0120: Scoped SAT-candidate equality e-matching

Status: accepted
Date: 2026-07-11

## Context

ADR-0119 retains the equality-abstraction CDCL(T) search across quantifier
rounds, but the separate matching e-graph sees only asserted/generated ground
equalities. A Boolean skeleton can force an equality nested under `or`, `ite`,
or another propositional context. The retained SAT candidate knows that
equality is true, yet matching cannot use it to discover a trigger enabled only
modulo that candidate. The loop can therefore stop at a matching fixpoint and
return `unknown` even though one candidate-guided source instance refutes the
query.

Z3's SAT quantifier plugin queues clauses from EUF merge notifications and
processes those queues at unit-propagation and final-check boundaries. It does
not rebuild every quantifier on every assignment. Axeyum already has exact
merge-path candidate queues (ADR-0113 through ADR-0116), so the missing boundary
is a rollback-safe candidate view rather than a high-frequency callback API.

## Decision

When ordinary source matching reaches a fixpoint while the retained CDCL(T)
session has a theory-consistent SAT candidate:

1. snapshot the currently true equality atoms in stable theory-atom order;
2. push one scope on the matching e-graph and merge those equality endpoints
   only inside that scope;
3. use the existing exact declaration/argument merge paths and semantic filters
   to match only affected top applications;
4. combine scoped matches with retained source matches and materialize concrete
   `TermId` binding tuples before popping the scope;
5. construct complete exact source instances from those tuples, pop every
   candidate merge, and never retain a candidate equality as an equality reason;
6. admit each instance only through `QuantifierInstanceCertificate`, then insert
   it through ADR-0119's checked retained-clause gate; and
7. resume the retained search. A new SAT candidate may trigger another bounded
   final-check round; no candidate SAT result becomes product SAT.

Candidate equality count and scoped candidate-application work have explicit
caps. Unsupported/missing endpoints, cap exhaustion, or no new instance decline
to the existing ordinary fixpoint/final-QF behavior. Candidate merges are search
hints only: they cannot justify detached literals, suppress source obligations
after pop, enter public evidence, or survive into another SAT branch.

The retained solver is solved lazily: if ordinary matching produces no first
batch, one initial candidate solve is permitted so candidate equalities can
unlock a trigger. Existing source-generated batches remain higher priority.

## Acceptance

- A nested-trigger target that is unmatchable from top-level source equalities
  becomes UNSAT only through a forced Boolean-skeleton equality and one exact
  candidate-guided source instance; disabling candidate matching preserves the
  prior `unknown`.
- Candidate merges are popped and cannot become false-sibling reasons or alter
  later ordinary matching; contradictory candidate snapshots remain isolated.
- Exact path candidates return the same tuples as scoped full matching while
  executing/scanning less work on a many-pattern target.
- Missing, unsupported, duplicate, over-equality-cap, over-work-cap, tampered
  certificate, online SAT, and replay-withheld paths fail closed.
- The target improves decide rate or measured matching/solve work without a
  public-corpus regression; otherwise reject the production path.
- Quantified BV/LIA/Bitwuzla decisions, direct-Z3 and bounded-instance
  soundness, evidence, MBQI, solver, benchmark, Clippy, rustdoc, links,
  foundational resources, generated matrices, formatting, and reference gates
  pass.

Accepted results:

- the nested-trigger target moves from `Unknown` with candidate matching
  disabled to replayed `Unsat` with one candidate check, one exact instance,
  two retained solves, and unchanged two-call QF replay; five optimized runs
  improve median time from 0.573 to 0.148 ms (74.2%, 3.87x);
- on 64 independent patterns, scoped exact paths execute/scan 1 pattern and 1
  top application versus a 64-pattern full scan, return the same sole tuple,
  and improve five-run optimized median time from 5.478 to 4.329 ms over 128
  repetitions (21.0%, 1.27x);
- optional-equality, forced-disequality, positive-universal, scope-pop,
  equality-cap, application-cap, exact-path/full-scan, and source-certificate
  gates pass. A 64-case direct-Z3 matrix recovers all 16 candidate-guided UNSAT
  cases and leaves all 48 satisfiable controls safely `Unknown`;
- the public cvc5 quantified-BV slice remains 29 SAT / 9 UNSAT / 5 unknown /
  11 unsupported with zero disagreement/error/replay failure and PAR-2 7.47178
  seconds. Quantified LIA remains 12/12 with three-run median 0.11852 seconds;
  Bitwuzla retains four expected UNSAT rows plus its known SAT replay alarm;
- all 1,064 direct-Z3 quantified-BV cases and 900 bounded-instance cases agree;
  solver 863/863, e-matching 57/57, evidence 69/69, MBQI 13/13, benchmark 7/7,
  and the static/documentation/resource/reference gates pass.

## Alternatives

- **Invoke matching after every SAT assignment.** Rejected: it adds a hot-path
  callback and repeated work before evidence shows that final-check deltas are
  insufficient.
- **Permanently merge every equality ever seen on a SAT trail.** Rejected:
  equalities from incompatible branches would accumulate, suppress useful
  instances, and could accidentally contaminate explanation ownership.
- **Use the SAT equality as a detached-literal reason.** Rejected: a candidate
  assignment is not an original or generated consequence. Only complete
  universal instances are emitted from this route.
- **Trust the candidate match without reconstructing the source instance.**
  Rejected: trigger matching remains untrusted search; exact substitution replay
  is the admission boundary.
- **Rebuild a separate matcher for each SAT candidate.** Rejected if exact scoped
  path matching is Pareto-positive: retained patterns, indexes, and source
  substitutions already contain the expensive stable state.

## Consequences

- Boolean-context equalities can unlock nested e-matches without becoming proof
  premises or persistent congruence facts.
- The implementation gains a final-check bridge between retained SAT theory
  state and the retained matcher, but no public solver/evidence type changes.
- High-frequency SAT-trail callbacks remain measurement-gated. Non-equality
  candidate antecedents and online proof serialization remain separate trust
  boundaries.
