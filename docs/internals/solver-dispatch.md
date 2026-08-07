# Solver dispatch and route contracts

`axeyum-solver` is the orchestration hub. Its job is not to pretend every term
belongs to one algorithm; it classifies a query, admits only routes whose
contracts apply, and returns a definitive verdict only when that route's replay
or evidence obligations are met.

## Front doors

The unified `solve` front door accepts an arena, assertions, and a `SolveConfig`.
It normalizes the query, considers quantified and ground paths, dispatches the
quantifier-free subset, and safely falls back to incomplete quantified routes.
The quantifier-free `check_auto` dispatcher selects among theory-specific and
combination engines.

The precise route order evolves, so the stable mental model is:

```mermaid
flowchart TD
    q["Typed query + limits"] --> classify["Classify fragment and features"]
    classify --> admit{"Route contract admitted?"}
    admit -->|no| next["Try the next applicable route"]
    admit -->|yes| decide["Run within caller deadline"]
    decide -->|SAT| replay["Lift + check source model"]
    decide -->|UNSAT| evidence["Assess evidence / assurance route"]
    decide -->|UNKNOWN| next
    replay --> verdict["Definitive result"]
    evidence --> verdict
    next --> exhausted{"Applicable routes left?"}
    exhausted -->|yes| classify
    exhausted -->|no| unknown["unknown"]
```

Fallback happens after `unknown`, not after a contradictory definitive result,
and all routes share the caller's remaining deadline. The explained dispatcher
adds a deterministic route trace without changing the verdict.

Current fragment coverage belongs in the generated
[support matrix](../reference/support-matrix.md), not in a hard-coded route list
on this page.

## Backends and solver state

`SolverBackend` defines a one-shot semantic boundary: a backend reports `sat`
with a model, `unsat` at its documented assurance level, or `unknown` with a
reason. Infrastructure faults remain errors rather than logical results.

The high-level `Solver<B>` adds assertions, assumptions, and push/pop scopes.
Those are interface-level incremental semantics; they do not promise that every
backend keeps a warm native solver between calls. Dedicated incremental BV/SAT
paths exist where reuse is implemented and measured.

## Stage accounting

Typed layer statistics separate normalization, bit-blasting, CNF encoding,
inprocessing, SAT solving, model lifting, and evidence work. Shapes and digests
make artifacts comparable without relying on unstable debug output. This split
is essential for deciding whether performance work belongs in encodings,
theory propagation, or the SAT core.

## Result discipline

- `sat` requires a source-level model accepted by the appropriate checker.
- `unsat` records any certificate/checker path and the resulting assurance
  boundary; a proofless backend result remains explicitly lower assurance.
- `unknown` is normal for unsupported fragments, incomplete algorithms, or
  exhausted explicit limits.
- an error means the request or infrastructure failed; it is never converted
  into `unsat`.

See [Solver configuration](../reference/solver-config.md) for public controls,
[Adding a solver route](../contributor-guide/adding-a-solver-route.md) for the
implementation checklist, and [Proof and evidence routes](proof-stack.md) for
how definitive results are audited.
