# Regression corpus — status-annotated, oracle-free soundness gate

Small, status-annotated SMT-LIB benchmarks used by
[`crates/axeyum-solver/tests/corpus_regression.rs`](../../crates/axeyum-solver/tests/corpus_regression.rs)
as a **soundness regression gate**: each file carries `(set-info :status sat|unsat)`,
the harness parses it, runs `check_auto`, and **fails only if the verdict
contradicts the declared status** (`sat` vs `unsat`). A parse failure (front-end
gap) or an `unknown` result is *skipped* — those are coverage gaps, not bugs. No
external oracle (Z3) is needed, so this runs in the default `cargo test`.

Files are flat (no `push`/`pop`/`reset`), single `(check-sat)`, so the parser's
flat assertion view is faithful.

## Layout

| Dir | Logic | Source |
|---|---|---|
| `qf_lra/` | QF_LRA | hand-authored (canonical linear-real sat/unsat) |
| `qf_lia/` | QF_LIA | hand-authored (integer gap / parity / solve) |
| `qf_uf/`  | QF_UF  | hand-authored (congruence, transitivity, distinct) |
| `qf_uflia/` | QF_UFLIA | hand-authored (uninterpreted `f` over `Int`) |
| `cvc5/qf_lia/`, `cvc5/qf_lra/` | QF_LIA / QF_LRA | **reused from cvc5** `test/regress` (see below) |

## Provenance of the `cvc5/` slice

The files under `cvc5/` are copied verbatim from the
[cvc5](https://github.com/cvc5/cvc5) project's `test/regress/` suite (BSD-3-Clause;
© the cvc5 authors), filtered to flat, status-annotated, parser-friendly QF_LIA /
QF_LRA instances. The original relative path is encoded in each filename
(`cvc5__<path-with-__-separators>.smt2`). They are included as third-party test
data; cvc5's licence applies to those files.

## Adding more

Drop any flat, `:status`-annotated `.smt2` into a subdirectory — the harness
discovers it recursively. Prefer fast-deciding instances (the harness caps each
solve at a few seconds and counts a timeout as `unknown`). Files that exercise a
not-yet-supported front-end construct (e.g. `declare-sort` uninterpreted sorts)
will simply be skipped until the construct lands.
