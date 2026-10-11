# ADR-6300: typed OMT results retain original model replay

Status: accepted; audited OMT contract adopted, final integration gates remain open
Date: 2026-10-11

## Decision

Add a Rust model-bearing text optimization report and Python smt.optimize. Keep
mode explicit (lexicographic default, or box), objective direction/sort/value,
optimization outcome, and model availability separate. Exact Int values remain
signed; BV objectives use unsigned order and unsigned values. The existing i128 result
carrier supports BV objective widths1..127; wider objectives decline explicitly.
Integer representation/search ceilings remain Unknown, never unboundedness.
Each box objective has its own model. Lexicographic objectives carry the earlier
optimal-value pins; unresolved prefixes stop later optimization.

Retain the owning arena, original active assertions, objective and claimed value.
Initial scalar feasibility probes complete ordinary missing Bool/Int/Real/BV
bindings, then replay before evaluating the objective. Unconstrained objectives
must not crash merely because satisfiability returned a sparse model.
Recover a model by solving the same query with the objective pinned to its
optimum, under the remaining shared caller budget. Replay checks every active
assertion/prefix and independently evaluates the original objective against the
claimed value. Missing/undecided witness retrieval is explicit, never an empty
model presented as replayed. Return fresh Python model dictionaries; editing
one cannot modify internal evidence.

Select objectives at the same query snapshot as assertions. Pop removes scoped
objectives, reset-assertions clears them, and declarations after check-sat do not
change the queried objective list. Legacy text optimizers reuse this selection.
Reject conflicting explicit mode options and unsupported Pareto/Real/soft
objectives rather than silently applying another interpretation. Multiple queries
still require a future incremental optimization result contract.

A replayed feasible model is not no-better evidence. Gold eligibility remains
false until a source-bound certificate for objective > v (or < v) is checked,
with prior pins in lexicographic mode. Generic Evidence::check alone is not that
contract: several routes check self-contained certificates without binding their
premises to the supplied query. Do not credit those as source-bound gold answers.
Checked optimality, preemptible ingestion and incremental reporting remain open.

Reference for lex/box semantics: [official Z3 guide](https://microsoft.github.io/z3guide/docs/optimization/combiningobjectives/).
Scoped objective authority: [Z3 scoped state](https://github.com/Z3Prover/z3/blob/master/src/opt/opt_context.cpp).

## Validation

Fresh Int/BV maximize/minimize, box/lex conflicts, ties, infeasible/unbounded,
unsupported sorts, expired budgets, objective scopes/reset/query snapshots and
mutable-model-copy controls. Rust replay rejects separately altered values and
models. Remove each replay guard in a private snapshot and require exactly one
targeted test failure. Full solver/workspace/front-door/differential gates remain
required; focused API tests do not close existing integration gate failures.

## Adoption and later composition

The implemented bounded contract is adopted. Later ADR-6301/6302 bind finite
integer optimality evidence to the original query; ADR-7000/7100 carry shared
cooperative deadlines through intake and model replay. Earlier follow-up lists
above record the original increment and are superseded where these later
contracts supply the implementation. See the
[current validation receipts](../../plan/notes/28-wide-real-smtlib-writer.md)
and [completion audit](../../plan/user-feedback-completion-audit-2026-10-11.md).
Current fresh-native OMT suites and full-feature solver regressions cover
feasible/optimal/unknown/unsupported outcomes and changed evidence. A checked
affine recession witness, not search exhaustion, justifies unboundedness.
Gold remains false when strict-better evidence is absent; integer-cut, BV and
other unsupported certificate producers retain explicit declines. Shared
linearization/checking is not advertised as independent implementation or
kernel admission. Final workspace/all-target verification and main integration
remain open.
