# ADR-1925: An engine-internal `Unsupported` is a decline, and a relabel must carry what it replaces

Status: accepted
Index-summary: Two diagnosis rules, both forced by the 2026-09-12 QF_NRA census: an `Unsupported` raised INSIDE a theory engine is a decline (`unknown`), never an error out of the dispatcher — it was the largest single cause in that division (20 of 77) and its text named the wrong backend; and a budget relabel must APPEND the reason it replaces rather than overwrite it — that one sentence is the top named `Timeout` detail in three separate censuses (QF_NIA 41/110, all-divisions 30/260, QF_NRA 18/77). Both are gated by mutation-controlled tests that each kill exactly one test.
Index-status: accepted
Date: 2026-09-12

## Context

The 2026-09-12 census of **all 77** winnable QF_NRA files
([`bench-results/qf-nra-route-20260912/`](../../../bench-results/qf-nra-route-20260912/README.md))
was run to find out why axeyum decides 117 of 200 where z3 decides 187 in a mean
of 1.31 s. The expectation going in was a capability wall. Two of the three
largest classes turned out to be **diagnosis defects** instead, and each of them
is an instance of a general rule this repository had not written down.

| cause | files | share |
|---|---:|---:|
| `ERROR: unsupported by backend: QF_LRA: nonlinear real multiplication` | 20 | 26% |
| `preprocessed dispatch timeout after reduced solve` | 18 | 23% |
| genuine relaxation incompleteness (fixpoint / capacity / round bound) | 22 | 29% |
| clock (lazy-SMT wall clock, watchdog, Fourier–Motzkin budget, replay) | 16 | 21% |
| wide integer literal (ADR-1702, tracked elsewhere) | 1 | 1% |

### The first class: an error where an `unknown` belonged

`unknown` is a first-class solver result and never an error — that is a Hard
Rule in `CLAUDE.md`. The dispatcher upheld it only when the query carried an
uninterpreted function:

```rust
Err(SolverError::Unsupported(message)) if features.has_function => { …decline… }
Err(e) => return Err(e),
```

A **pure** nonlinear-real query therefore had no conversion at all. When
`check_with_nra`'s relaxation leaked a raw product into the linear engine (the
root cause, fixed separately in `solve_relaxation`), the resulting
`SolverError::Unsupported` travelled all the way out of `solve`, and the
competition front door printed:

    ; give-up kind=Error detail=unsupported by backend: QF_LRA: nonlinear real multiplication

Three things are wrong with that line, and only the first is obvious.

1. It is an **error**, so the whole dispatch is abandoned.
2. It names **`QF_LRA`** — the linear backend, which is downstream of and
   innocent of the refusal. A reader following that text goes to the wrong
   module. Measured: with the relaxation disabled by
   `AXEYUM_NRA_ADMISSION=0`, the same file reports the true boundary,
   `nonlinear abstraction: … past the consuming engine's capacity … (this needs
   a nlsat/CAD engine)`.
3. It costs the query **two full dispatches**. `check_auto` catches an errored
   preprocessed pass and re-runs everything on the original, so `nra-real-root`
   and `cas-ideal-refuter` each ran twice (156 ms + 150 ms on
   `MulliganEconomicsModel0051a.smt2`) before the second pass errored again.

### The second class: a relabel that overwrote its own evidence

`dispatch_reduced` ends an out-of-budget reduced solve like this:

```rust
if matches!(result, CheckResult::Unknown(_)) && past_deadline(deadline) {
    return Ok(CheckResult::Unknown(timeout_reason(
        "preprocessed dispatch timeout after reduced solve",
    )));
}
```

`result` is an `Unknown` that already carries **which route gave up and on what
bound**. The relabel discards it and keeps only the clock.

That is not a QF_NRA corner. The same sentence is the top named `Timeout` detail
in every census that has looked:

- 41 of 110 files —
  [`qf-nia-is-not-a-width-problem-2026-09-12.md`](../03-measurements/qf-nia-is-not-a-width-problem-2026-09-12.md)
- 30 of the 260 `unknown`s over eleven divisions —
  [`why-unknown-says-nothing-2026-09-11.md`](../03-measurements/why-unknown-says-nothing-2026-09-11.md)
- 18 of 77 here.

So roughly a third of two divisions' gap analysis rests on a string that carries
no cause. The WHY-UNKNOWN lane reported this sentence as the bucket's largest
detail without noticing that it is a *substitution*, which is exactly how a
placeholder survives being counted.

## Decision

**1. An `Unsupported` raised inside a theory engine is a decline, not an error.**
At the dispatcher's theory-branch boundary, `SolverError::Unsupported` is
recorded against the route and converted to `CheckResult::Unknown` carrying the
engine's own message — for every query, not only ones that happen to contain a
function. Errors are reserved for conditions the *caller* got wrong (an ingest
refusal, a malformed query), never for "this engine does not handle this shape",
which is the definition of an `unknown`.

**2. A relabel must append the reason it replaces, never overwrite it.**
Where a wrapper substitutes its own `UnknownReason` for an inner one — a budget
relabel, a degradation, a fall-through — the inner reason is appended. The
prefix stays byte-identical so existing consumers keep matching, and the
discarded half is carried instead of dropped.

The general form, which is what makes this an ADR rather than two bug fixes:
**a layer that rewrites a diagnosis owns the obligation to carry the diagnosis
it rewrites.** A census is only as good as the worst placeholder in it, and a
placeholder is invisible precisely because it counts.

## Consequences

- The front door no longer errors on a pure nonlinear-real query it cannot
  decide; it returns `unknown` with a reason. The verdict is unchanged in every
  case (an error and an `unknown` are both "not decided" to a scorer), so no
  parity row moves because of this rule alone.
- The `Timeout` class in every division becomes readable. Re-censusing the 18
  QF_NRA rows behind the old sentence is now a matter of re-running them, and
  the same applies to the QF_NIA 41 and the all-divisions 30.
- **The safety net in rule 1 currently has no exerciser**, and this is stated
  rather than papered over. The root-cause fix in `solve_relaxation` removed the
  only known producer of an engine-internal `Unsupported` on the real branch, so
  a mutation deleting the conversion survives. That is an honest "not covered",
  not a claim of coverage. The rule is kept because the next producer should not
  re-learn it the expensive way — which is what happened here.

## Alternatives considered

- **Convert the error at the front door instead.** Rejected: the CLI already has
  an `Err(_) => "unknown"` arm, and it is exactly what
  [`unknown_reason_coverage.rs`](../../../crates/axeyum-solver/tests/unknown_reason_coverage.rs)
  was written to stop — converting at the outermost layer is what threw the
  reason away in the QF_DT case. The conversion belongs where the message is.
- **Keep the retry after converting.** The old `Err` path re-ran the whole
  dispatch on the original query. Treating the decline like any other `unknown`
  ends the preprocessed pass, which is what every non-error decline already
  does; keeping a retry only for this one kind would make the budget depend on
  whether a route said "unsupported" or "incomplete". Measured on the 200-file
  division A/B before accepting.
- **Drop the relabel entirely and return the inner reason.** Rejected: the
  relabel's `kind` (`Timeout`) is genuine information — the budget *did* expire —
  and three existing censuses match on its prefix. Appending keeps both.

## How each rule can fail

Both are gated, and each mutation kills **exactly one** test
(`scripts/tests/mutation_controls.py`):

| suite | mutation | result |
|---|---|---|
| `nra-point-lemma-abstraction` | delete the abstraction rewrite on the point lemma | `killed 1` |
| `preprocessed-timeout-reason` | drop the carrier phrase from the relabel | `killed 1` |

The first test asserts at `check_with_nra`, **below** the rule-1 safety net, on
purpose: a front-door version of the same fixture passed with the guard deleted
because the net caught the error one layer up, and the mutation control reported
`SURVIVED`. That rejection — and an earlier fixture the exact real-root decider
simply decided, so the relaxation never ran — are both recorded in the test's
module docs.
