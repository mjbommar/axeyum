# Incremental (scoped) corpus — roadmap item 2.9

Small, hand-written SMT-LIB scripts that use `push`/`pop`/`reset-assertions`/
`check-sat-assuming`, each with **one expected verdict per `check-sat`**, used by
[`crates/axeyum-solver/tests/corpus_regression.rs`](../../crates/axeyum-solver/tests/corpus_regression.rs)'s
`incremental_corpus_is_sound` test.

## Why this exists, separately from `corpus/regression/`

`corpus/regression/` is flat: one `(set-info :status sat|unsat)` per file,
compared against the parser's flat (scope-free) assertion view. That gate
*deliberately skips* any file containing `push`, `pop`, `reset-assertions`, or
`(reset` (`corpus_regression.rs`'s `evaluate_file`) — a single `:status` cannot
express the ground truth of a scoped script, whose `check-sat`s can legitimately
disagree with each other (see `04-leak-catcher.smt2`).

Before this directory, **0 of the 1,101 committed `.smt2` files used `push`
at all**, so no committed gate ever exercised scoping — including the exact
failure mode (an assertion surviving a `pop`) that would make routing the
`Solver` façade through the warm incremental engine (roadmap item 1.1b) unsafe
to gate.

## The verdict format: `check-sat-order`

`:status` is singular and cannot carry more than one ground truth, so each file
here instead carries a header comment:

```
; check-sat-order: sat unsat sat
```

whitespace-separated `sat`/`unsat` tokens, one per `check-sat` (and
`check-sat-assuming`) command **in script order**. The harness reads this line
directly from the file text (not through the SMT-LIB parser) and zips it
against the `Vec<CheckResult>` `solve_smtlib_incremental` returns — one result
per query, in order. A length mismatch (the script's query count and the
header's verdict count disagree) is itself a failure: a route that silently
drops or duplicates a query is exactly as unsound as one that answers it wrong.

## What each file pins

| File | Covers |
|---|---|
| `01-push-pop-basic.smt2` | assert outside a push, contradict inside it, pop, recheck |
| `02-nested-push-pop.smt2` | `push`/`push`/`pop`/`pop` nesting |
| `03-push-then-two-checks-same-scope.smt2` | two `check-sat`s in one still-open scope |
| `04-leak-catcher.smt2` | **the file the exit criterion names**: unconstrained → contradictory under one push → popped back to unconstrained. A `pop` that fails to drop its scope's assertions turns the third verdict `unsat` instead of `sat`. |
| `05-reset-assertions.smt2` | `reset-assertions` at top level |
| `06-reset-inside-push.smt2` | `reset-assertions` while a scope is open (no matching `pop` follows) |
| `07-check-sat-assuming-non-retention.smt2` | `check-sat-assuming` binds for one query only; verdicts pinned against z3 4.13.3 (matches `crates/axeyum-solver/tests/smtlib.rs::incremental_scripts_answer_one_verdict_per_check_sat`) |
| `08-push-zero-pop-zero.smt2` | `(push 0)` / `(pop 0)` are no-ops |
| `09-push-two-pop-two.smt2` | `(push 2)` / `(pop 2)` batch two scopes in one command |
| `10-repeated-cycle-stress.smt2` | three independent push/assert/check/pop cycles — a leak that only accumulates over several cycles |
| `11-checksat-immediately-after-empty-push.smt2` | `check-sat` right after a push with nothing asserted yet |
| `12-declare-inside-push-survives-pop.smt2` | a `declare-fun` inside a push stays declared after the matching `pop` (declarations are global, per `solve_smtlib_incremental`'s documented contract) — only the *assertions* from that scope are dropped |

## The negative control

`incremental_corpus_is_sound` calls the production entry point
(`axeyum_solver::solve_smtlib_incremental`) — not a test-local reimplementation
— because the whole point of this corpus is to gate the *real* incremental
route. To prove the corpus and comparison actually discriminate correct from
leaking scoping, a **separate, temporary** hand-rolled walker was added to
`corpus_regression.rs` during development that reimplements the same
push/assert/check-sat walk from public API (`ScriptCommand`, `check_auto`) but
deliberately skips truncating the assertion stack on `pop`. Run once against
this corpus, it disagreed with `04-leak-catcher.smt2`'s expected `sat` (the
leaky walker reports the final check-sat `unsat`, since the popped
`(< x 0)`/`(> x 0)` pair is still present) — see the lane's final report for
the exact command output. That walker was then deleted; it exists nowhere in
the shipped test.

## Adding more

Keep files small and fast (same wall-clock cap as `corpus/regression/`). Every
file needs the `; check-sat-order: ...` header with exactly one token per
`check-sat`/`check-sat-assuming` in the script, in order.
