# Adding a Solver Route

A solver route may be a new `SolverBackend`, a new theory procedure behind the
full-profile dispatcher, or a bounded fast path inside an existing backend. In
all cases it must preserve one public result contract: replayable `sat`, sound
`unsat`, structured `unknown`, and typed operational errors.

## 1. Define the route boundary

Before implementation, specify:

- accepted logics, sorts, operators, and query shapes;
- completeness: decision procedure, refutation-only, model-finding-only, or
  bounded/incomplete;
- deterministic admission and search budgets;
- fallback order and whether a decline permits another route to try;
- satisfying-model construction and original-query replay;
- UNSAT evidence/checker composition;
- feature and native-dependency profile; and
- the telemetry needed to distinguish parse, transform, solve, lift, and check
  costs.

Check the [foundational DAG](../research/08-planning/foundational-dag.md),
[roadmap](../research/08-planning/roadmap.md), and
[research questions](../research/08-planning/research-questions.md). A new
backend, theory combination, proof format, linked solver role, or default
dispatch policy requires an ADR.

## 2. Preserve the public result taxonomy

The contract lives in
[`backend.rs`](../../crates/axeyum-solver/src/backend.rs):

- `CheckResult::Sat(Model)` means a source-level model exists;
- `CheckResult::Unsat` is a definitive refutation;
- `CheckResult::Unknown(UnknownReason)` means the route safely declined; and
- `SolverError` means invalid input, unsupported representation, parse failure,
  or an operational/internal failure.

Timeouts, node/CNF/search limits, memory limits, and incompleteness are
`Unknown`, not `Unsat` and normally not errors. Unsupported syntax discovered
before a procedure owns the query is `SolverError::Unsupported`. A failed model
lift, checker disagreement, or impossible internal state is a backend error and
must fail closed.

Do not collapse these states into a Boolean or treat `unknown` as “probably
sat/unsat.”

## 3. Implement or extend the backend boundary

An independent backend implements [`SolverBackend`](../../crates/axeyum-solver/src/backend.rs):

- `capabilities()` returns a stable name, model-production status, and whether
  the route is complete for its declared fragment;
- `check()` consumes only `TermArena`, `TermId`, and owned Axeyum values; and
- `last_stats()` may return layer-attributed `SolveStats`.

Backend FFI terms, contexts, lifetimes, and models must not leak into public
Axeyum APIs. One-shot backends can inherit `check_query`; an incremental backend
must preserve assertion, assumption, scope, and label semantics from
[`axeyum-query`](../../crates/axeyum-query/README.md).

If the route is internal to the full-profile dispatcher, keep admission
predicates narrow and inspectable. A route should either own and correctly
handle a query, return a classified safe decline, or leave it untouched for the
next route. Avoid catch-all matches that steal queries from a more complete
procedure.

## 4. Make budgets part of semantics at the boundary

Use [`SolverConfig`](../../crates/axeyum-solver/src/backend.rs) for common
wall-clock, deterministic-resource, memory, node, and CNF budgets. Procedure-
specific expansions also need explicit caps.

Budget behavior must be:

- checked before an unbounded allocation or expansion;
- deterministic where the budget is deterministic;
- surfaced as a classified `UnknownReason`;
- included in artifacts and route traces; and
- covered by a test that forces the bound.

Never catch an out-of-memory kill or hang after the fact and call that resource
control.

## 5. Lift and replay every SAT model

The route's internal assignment is not the public model. Retain all maps and
reconstruction trails needed to recover values for original symbols after
rewriting, elimination, abstraction, bit-blasting, or theory combination.

Before returning `Sat`:

1. construct an Axeyum-owned [`Model`](../../crates/axeyum-solver/src/model.rs);
2. complete only values permitted by the route's semantics;
3. reconstruct eliminated or abstracted values in dependency order; and
4. run the canonical source-query model check.

A replay failure is a soundness alarm. It must not be downgraded to a successful
`Sat`, and an artifact must not count it as an ordinary `unknown` without an
explicit replay-failure policy.

Retain a tampered-model negative control so the replay test proves that the
checker can reject.

## 6. Account for UNSAT independently

For every new `Unsat` path, identify the checked chain from source assertions to
the final contradiction. Depending on the route, that may include rewrite or
elimination certificates, bit-blast/AIG equivalence, CNF equisatisfiability,
DRAT/Alethe/Farkas/theory certificates, and Lean reconstruction.

If the complete chain is not independently checked, classify the result at its
actual assurance tier in the
[trust ledger](../research/08-planning/trust-ledger.md). Do not advertise a
downstream SAT proof as an end-to-end proof when an upstream transform remains
trusted by a meta-argument.

Follow [Proof and evidence obligations](proof-and-evidence-obligations.md) and
the [proof cookbook](../proof-cookbook/README.md) for existing routes.

## 7. Add route observability

Record enough stable data to answer:

- why this route admitted or declined the query;
- which route ultimately decided it;
- which deterministic/wall-clock budgets applied;
- how much time and shape belonged to each transformation/solve/lift/check
  layer; and
- what evidence and replay states were produced.

Telemetry is returned structured data, not parsing human logs. Keep ordering
stable and avoid high-cardinality nondeterministic strings in artifacts.

## 8. Test route selection and soundness

Retain at least:

- an admitted `sat` query with successful original-model replay;
- an admitted `unsat` query with its checker/evidence assertion;
- a query just outside the admission boundary;
- a forced budget exhaustion with the exact `UnknownKind`;
- malformed/unsupported input with the correct `SolverError`;
- a fallback query proving a decline does not block another route;
- deterministic repeated execution under the same seed/budget; and
- differential verdict comparison against an independent oracle.

Add near-miss cases around syntactic recognizers. A shape matcher that is too
broad is a common route-level soundness bug.

## 9. Update public truth and validate

Update the support matrix, capability matrix, trust ledger, route/architecture
docs, relevant ADR, limitations, benchmarks, and `PLAN.md` together.

Then run:

```sh
cargo test -p axeyum-solver --features full
cargo clippy -p axeyum-solver --features full --all-targets -- -D warnings
cargo test -p axeyum-solver --test progress_frontier \
  --features full -- --test-threads=1
just check-scope origin/main
```

Run the frontier alone, then the applicable corpus/differential gate. Finish
with one `just check` before integration.

## Completion checklist

- [ ] Admission, completeness, fallback, features, and budgets are explicit.
- [ ] `Sat`/`Unsat`/`Unknown`/error meanings are preserved.
- [ ] Axeyum-owned SAT models replay against original assertions.
- [ ] UNSAT proof composition or its trust gap is explicit and tested.
- [ ] Route and layer telemetry is deterministic and structured.
- [ ] Boundary, budget, fallback, negative-control, and oracle tests pass.
- [ ] Current matrices, ledger, ADR, limitations, benchmarks, and PLAN agree.

