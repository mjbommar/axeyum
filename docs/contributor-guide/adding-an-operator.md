# Adding an Operator

An operator is not complete when an `Op` variant compiles. It is complete when
its type rules, total semantics, text representation, lowering/solver route,
model replay, evidence story, tests, and support claims agree.

## 1. Establish scope before code

Read the [foundational DAG](../research/08-planning/foundational-dag.md), the
[current roadmap phase](../research/08-planning/roadmap.md), and the
[research-question index](../research/08-planning/research-questions.md).

Write down:

- the SMT-LIB operator and logic fragments it changes;
- argument/result sorts and every boundary case;
- whether the operation is total, and its exact division-by-zero, overflow,
  shift, NaN, or partial-looking semantics;
- which backend will decide it;
- how a `sat` model lifts and replays;
- how `unsat` becomes independently checkable, or which trust-ledger gap
  remains; and
- deterministic resource limits for any expansion or search.

If this creates public surface, changes semantics, adds a dependency, or
chooses a new evidence format, record the decision in an ADR before silently
settling it in code. The ADR template is in the
[decision index](../research/09-decisions/README.md).

## 2. Trace every exhaustive match site

The central operator enum is [`Op`](../../crates/axeyum-ir/src/term.rs). Before
editing it, inventory all sites that consume operators:

```sh
rg -n 'Op::|match .*op' crates/axeyum-ir crates/axeyum-rewrite \
  crates/axeyum-bv crates/axeyum-smtlib crates/axeyum-solver
```

The usual path is:

```text
Op variant
  -> checked TermArena builder
  -> ground evaluator
  -> stable formatter
  -> SMT-LIB parser and writer
  -> rewrite traversal/rebuild
  -> lowering or theory backend
  -> model/proof lift and original-query replay
```

Not every operator belongs in the bit-vector lowering. Unsupported downstream
routes must decline structurally; they must not silently approximate semantics.

## 3. Add typed construction

Add or extend a checked [`TermArena`](../../crates/axeyum-ir/src/arena.rs)
builder. The builder must reject:

- wrong arity;
- wrong sorts or mismatched widths;
- invalid indices, widths, or parameters; and
- arithmetic overflow while computing result widths or bounds.

Interning must remain deterministic. Term IDs are arena-owned, lifetime-free
`Copy` handles; do not introduce backend types or lifetimes into the IR API.

Include builder tests for the valid form and every rejection class. A parser
test is not a substitute for direct builder coverage.

## 4. Define executable semantics

Implement the ground semantics in [`eval.rs`](../../crates/axeyum-ir/src/eval.rs)
before using an oracle or lowering as the meaning of the operator. The evaluator
is the small reference used by model replay and equivalence tests.

For bit-vectors, follow SMT-LIB totality exactly; see
[BV semantics and partial-looking operations](../research/01-foundations/bv-semantics-and-partial-operations.md).
Test zero, one, minimum/maximum values, signed extrema, and width-one behavior
where applicable. Do not rely only on ordinary values.

When the evaluator has a bounded representation, overflow must become a typed
error or a downstream `unknown`, never a wrapped reference answer.

## 5. Complete text and traversal support

Update the surfaces that can observe or reconstruct the term:

- stable human formatting in [`fmt.rs`](../../crates/axeyum-ir/src/fmt.rs);
- SMT-LIB parsing in [`axeyum-smtlib`](../../crates/axeyum-smtlib/src/lib.rs);
- sharing-preserving writing in [`write.rs`](../../crates/axeyum-smtlib/src/write.rs);
- any term statistics or operator classification; and
- generic rewrite/rebuild visitors that use exhaustive matches.

Add parser rejection cases, parse/write round trips, and a sharing-sensitive
round trip when the operator can contain repeated subterms. If the parser and
writer do not support the new operator yet, do not claim SMT-LIB support for it.

## 6. Implement a decision route

For scalar QF_BV, add lowering in [`axeyum-bv`](../../crates/axeyum-bv/src/lib.rs)
and preserve the term-bit and symbol-input maps. Prove the Boolean wires agree
with the evaluator by exhaustive small-width tests.

For a theory operator, route it through the owning theory procedure and keep
unsupported cases explicit. New encodings must define:

- semantic or equisatisfiability relation to the source term;
- any reconstruction data required for `sat`;
- proof/evidence composition for `unsat`;
- node/CNF/search budgets; and
- layer-attributed telemetry where performance is material.

Do not discard lift maps after solving. A backend assignment is not yet an
Axeyum model.

## 7. Prove both answer directions

At minimum, retain:

- direct evaluator examples;
- exhaustive small-domain builder/evaluator coverage;
- evaluator-versus-lowering or evaluator-versus-procedure tests;
- deterministic differential tests against an independent oracle;
- a `sat` case whose lifted model passes original-query replay;
- an `unsat` case with the applicable proof/checker route or an explicit
  lower-assurance classification;
- an `unknown`/unsupported case at the route boundary; and
- malformed and resource-bound controls.

See [Proof and evidence obligations](proof-and-evidence-obligations.md) for the
required distinction between definitive answers, safe declines, and
operational errors.

## 8. Update public truth

Update all affected current-state surfaces in the same change:

- [support matrix](../research/08-planning/support-matrix.md);
- [capability matrix](../research/08-planning/capability-matrix.md);
- [trust ledger](../research/08-planning/trust-ledger.md);
- relevant user limitations or examples;
- roadmap/phase evidence; and
- `PLAN.md` status and next actions.

Capability, performance, and assurance are separate claims. A parser accepting
an operator does not prove the pure-Rust solver decides it; a solver decision
does not prove independent UNSAT checking.

## 9. Validate

Start with the owning crates, then widen:

```sh
cargo test -p axeyum-ir
cargo test -p axeyum-smtlib
cargo test -p axeyum-bv
cargo test -p axeyum-solver --features full
just check-scope origin/main
```

If the change affects solver dispatch, also run the serialized frontier from
[Testing and validation](testing-and-validation.md#solver-and-dispatch-changes).
Run `just check` once before integration.

## Completion checklist

- [ ] Sort, arity, parameter, and total semantics are documented.
- [ ] Builder and evaluator agree on all edge cases.
- [ ] Parser, writer, formatter, and visitors are complete or explicitly unsupported.
- [ ] Lowering/procedure agrees with the evaluator on a bounded exhaustive domain.
- [ ] Lifted `sat` models replay against the original query.
- [ ] `unsat` assurance is checked or accurately ledgered.
- [ ] Unsupported/resource cases decline deterministically.
- [ ] Current support, capability, trust, roadmap, and PLAN surfaces agree.
