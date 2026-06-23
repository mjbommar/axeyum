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

- **Hand-authored seeds** (statuses certain by construction), one subdir per logic:
  `qf_lra/`, `qf_lia/`, `qf_uf/`, `qf_uflia/`, `qf_bv/`, `qf_abv/` (read-over-write),
  `qf_nia/` (square sat/unsat), `qf_nra/` (√2 sat, `x²=-1` unsat), `qf_dt/` (enum
  constructors).
- **Reused from cvc5** under `cvc5/<logic>/`: flat, status-annotated, parser-friendly
  instances for QF_LIA, QF_LRA, QF_ABV, QF_FP, QF_UF, QF_BV, QF_S (strings). See
  provenance below.

> Note on coverage: pure **QF_UF with `declare-sort` (uninterpreted sorts)** is
> currently *parse-skipped* — the front end does not yet model first-class
> uninterpreted sorts (a known gap). EUF congruence is still exercised through
> QF_UFLIA (uninterpreted functions over `Int`). Most **QF_S (strings)** files
> parse-skip too — axeyum's string support is experimental/bounded. These skips
> are coverage gaps the gate surfaces honestly, not soundness failures.

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
