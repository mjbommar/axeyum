# Proof and Evidence Obligations

Axeyum's design is “untrusted fast search, trusted small checking.” Search may
be heuristic or delegated; a definitive public answer is only as strong as the
smallest independently checked chain that connects it back to the original
query.

## Start from the answer type

| Result | Required evidence |
|---|---|
| `sat` | A source-level model or witness that replays against every original assertion |
| `unsat` | A checked refutation chain, or an explicit lower-assurance trust-ledger classification |
| `unknown` | A structured reason that cannot be confused with a definitive answer |
| error | A typed operational/input failure that fails closed |

An oracle agreement, a solver's own success code, or a proof of only the final
lowered problem does not by itself discharge the source-query obligation.

## The evidence chain

For a transformed query, ask at every arrow:

```text
original assertions
  -> rewritten/planned assertions
  -> theory elimination or bit lowering
  -> AIG/CNF or theory constraints
  -> search result
  -> model lift or proof reconstruction
  -> independent source-level check
```

The [foundational DAG](../research/08-planning/foundational-dag.md) defines these
contracts. The [trust ledger](../research/08-planning/trust-ledger.md) records
which arrows are currently checked, trusted, oracle-backed, partial, or absent.
Update the ledger when a route's assurance changes; do not rely on capability
prose alone.

## SAT obligations

A `sat` route must retain all information needed to interpret a backend answer
in the original arena:

- symbol-to-input maps after lowering;
- reconstruction trails after variable elimination or abstraction;
- values for arrays, functions, datatypes, strings, or quantified witnesses as
  required by the fragment; and
- enough model completion to evaluate every original assertion without
  inventing inconsistent values.

The canonical check evaluates the original assertions, not merely the final
transformed formula. Add both:

- a valid-model test that replays; and
- a tampered or incomplete model that the checker rejects.

For a bounded or quantified model certificate, test the certificate's claimed
scope and ensure the public result does not overstate it.

## UNSAT obligations

An `unsat` answer needs a contradiction plus checked bridges for every
semantics-changing layer. Existing proof surfaces are grouped under the
[`proofs` namespace](../../crates/axeyum-solver/src/lib.rs), with recipes in the
[Proof Certificate Cookbook](../proof-cookbook/README.md).

Common routes include:

- bit-blast/CNF plus independently checked DRAT;
- Alethe proof production and checking for supported theory steps;
- arithmetic certificates such as Farkas combinations;
- finite-domain enumeration or checked certificates; and
- reconstruction into the independent Rust Lean-core checker or emitted Lean.

Name the assurance boundary precisely. For example, a DRAT proof may check the
CNF contradiction while the source-to-CNF transformation is still supported by
tests and a trusted meta-argument. That is useful evidence, but not the same as
an end-to-end checked source proof.

If no independent route exists, return `Unsat` only where the accepted backend
contract permits it and record the lower assurance in the trust ledger. Never
describe “the same solver checked its own output” as independent checking.

## Unknown and errors are evidence too

An incomplete route must fail closed:

- timeouts and deterministic resource bounds become classified `unknown`;
- unsupported representation becomes a typed `Unsupported` error at the
  backend boundary;
- malformed text becomes a parse error;
- proof disagreement, failed replay, or impossible reconstruction becomes a
  soundness error; and
- no failure path may silently guess a verdict.

Test the exact classification. A generic “did not return sat” assertion can
hide a wrong `unsat`, a crash, or an unrelated parse failure.

## Evidence artifact requirements

An evidence artifact should be self-identifying and replayable. Record:

- exact source revision and dirty-state policy;
- input identity and content hash or committed corpus manifest;
- backend/route and feature profile;
- tool/checker versions;
- deterministic seeds, budgets, jobs, and wall-clock limits;
- raw verdict plus model replay/proof check status;
- transformation and evidence route identifiers;
- checker outcome and failure detail; and
- schema version.

Keep the raw evidence separate from a generated summary. A dashboard or success
count is not enough to replay one row.

## Negative controls

Every checker or evidence producer needs a control that should fail. Depending
on the format, mutate:

- the source assertion while retaining the evidence;
- a model value;
- a proof step, premise, clause, coefficient, or hash;
- the claimed tool/source revision; or
- a bound or scope field.

The control must reach the intended checker and fail for the intended reason.
Failing earlier on malformed JSON does not demonstrate that a proof checker
rejects an invalid proof.

Retain satisfiable/near-miss controls for refutation recognizers and unsatisfiable
controls for witness recognizers. This detects always-accept and always-decline
implementations.

## Determinism and bounds

Evidence generation must have stable ordering, explicit seeds, and explicit
resource limits. If a proof or reconstruction cannot be produced within its
bound, the route must return a safe decline or lower-assurance state—not omit
the checker status while preserving a definitive claim.

Timing alone is not reproducibility. Deterministic artifacts should be byte-
stable when practical; otherwise define and test the normalized fields that
must remain identical.

## Review checklist

Before accepting a new definitive path, a reviewer should be able to answer:

- [ ] What exact original query is being proved or witnessed?
- [ ] Which transformations occur, and what validates every arrow?
- [ ] Does SAT replay use original assertions and reject a tampered model?
- [ ] Does UNSAT have an independent checker, and what remains trusted?
- [ ] Do negative controls reach and fail the intended checker?
- [ ] Are unsupported, timeout, and resource cases classified without guessing?
- [ ] Are source, input, tools, features, seeds, budgets, and schema recorded?
- [ ] Do the capability matrix, support matrix, and trust ledger say the same thing?

If any answer is unknown, the route is not ready for a stronger assurance
claim. It may still land as an explicit experiment or ledgered lower-assurance
path.

