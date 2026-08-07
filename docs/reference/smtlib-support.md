# SMT-LIB Support

Axeyum has a substantial SMT-LIB parser and Rust-facing helpers, but it is not
yet a drop-in interactive SMT-LIB process. Keep syntax acceptance, command
execution, Rust return values, textual response ordering, and theory support
separate.

## Authoritative protocol matrix

Use the generated
[SMT-LIB and Rust API conformance matrix](../plan/generated/smtlib-api-conformance.md).
It records, per command/API:

- parse state (`semantic`, command-point, global, no-op, rejected, absent);
- execution state;
- returned representation;
- assurance/evidence;
- exact tests; and
- the remaining protocol gap.

Validate it with:

```sh
python3 scripts/gen-smtlib-api-conformance.py --check
```

The planned ordered session semantics are separately modeled by the generated
[SMT-LIB session contract](../plan/generated/smtlib-session-contract.md). That
prototype is executable planning evidence, not the current production runner.

## Current Rust-facing front doors

With `axeyum-solver/full`:

| API | Contract |
|---|---|
| `solve_smtlib` | One effective satisfiability query; returns `SmtLibOutcome` |
| `solve_smtlib_incremental` | One typed result per recorded check point with assertion-stack behavior |
| `solve_smtlib_get_model` / `solve_smtlib_model` | Typed declared constants/functions for one SAT query |
| `solve_smtlib_get_value` | Typed evaluated requested terms |
| `solve_smtlib_get_assignment` | Typed values for supported named assertions |
| `solve_smtlib_get_assertions` | Rendered active-assertion snapshots |
| `solve_smtlib_get_info` / `get_option` | Rust values from recorded metadata/options |
| `solve_smtlib_unsat_core` | Deletion-minimized active assertion subset |
| `solve_smtlib_get_proof` | Checkable proof text for selected UNSAT shapes |

These helpers parse a complete input string and return Rust data. They do not
emit an ordered SMT-LIB stdout transcript.

## Important current boundaries

- `set-logic` is recorded metadata; dispatch follows term shape.
- Multiple check points require `solve_smtlib_incremental`; the single-query
  facade rejects multiple effective queries.
- Assertion push/pop is represented, but full standard declaration scoping and
  reset/session epochs are not yet production behavior.
- Several output commands are accepted syntactically without command-point
  execution; consult the generated row before relying on one.
- Models and values are typed Rust values, not canonical SMT-LIB text.
- Proof output exists only for selected shapes and checker routes.
- Parser resource/deadline exhaustion must map to structured `unknown`, not a
  verdict or generic syntax error.

## Theory support is a different axis

The protocol matrix does not claim that every term in a named logic is decided.
Use [Supported logics](supported-logics.md) and the generated
[support matrix](support-matrix.md) for parser/IR/solver/evidence coverage.

For a runnable one-query example, see
[Your first SMT-LIB query](../user-guide/first-smtlib-query.md).

