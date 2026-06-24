# BV (quantified bit-vectors) curated slice (cvc5 + bitwuzla regress)

First **BV** (quantified bit-vectors — files carry `forall`/`exists`)
head-to-head of the high-level `axeyum_solver::check_auto` dispatcher
(`--backend solver`) against Z3 4.13.3. Part of the **quantified** category
(`quantified/UF`, `quantified/BV`, `quantified/LIA`).

## Why this slice is all-`unsupported` (an honest skip)

The quantifiers `forall`/`exists` are parsed faithfully into the typed IR, but
the pure-Rust BV backend declines them: every file reports *"term #N uses
unsupported pure-Rust BV operator `Forall(...)`"* (or `Exists(...)`). No
quantifier-instantiation / e-matching / MBQI search is wired through the backend
yet, so the (otherwise fully-supported QF_BV) body is never decided once a
quantifier wraps it — and therefore no wrong verdict is possible. The division
is **opened and measured** (DISAGREE 0 vacuously); the instantiation path is the
tracked follow-up.

This is the most interesting of the three quantified slices because the
quantifier *body* is in axeyum's strongest fragment (QF_BV): a quantifier
instantiation layer here would immediately produce decided verdicts.

## Provenance

Files are reused from the cvc5 regression suite
(`references/cvc5/test/regress`) **and** the bitwuzla regression suite
(`references/bitwuzla/test/regress`), both shallow sparse clones —
`references/` is gitignored. Each vendored file's name flattens its original
`test/regress/...` path (`/` → `__`).

Two sub-slices:

- `cvc5-regress-clean` — **54** clean files (all 54 contain `forall`/`exists`;
  `:status` 36 sat, 18 unsat).
- `bitwuzla-regress-clean` — **5** clean files (all 5 contain `forall`/`exists`;
  `:status` 1 sat, 4 unsat).

## Selection criteria

Same clean, parser-faithful, status-annotated filter as the other slices
(`scripts/curate-public-slice.py BV <out>` for cvc5;
`… BV <out> --root references/bitwuzla/test/regress` for bitwuzla): exact
`(set-logic BV)`, a `(set-info :status …)` ground truth, plain `(assert …)` +
`(check-sat)` only, not `.smtv1`-derived, no incremental/exotic commands, at
least one `assert`.

## Measured head-to-head

`--logic BV --backend solver --compare-z3 --timeout-ms 10000 --jobs 4`.

`bench-results/baselines/bv-cvc5-regress-clean-quantified-solver-vs-z3-10s.json`:

- **files 54** — decided **0** (sat 0, unsat 0), unknown 0, unsupported **54**,
  errors 0. Oracle: **compared 0, agree 0, DISAGREE 0**.
- Detail: 45 `Forall`, 9 `Exists` (all unsupported BV operators).

`bench-results/baselines/bv-bitwuzla-regress-clean-quantified-solver-vs-z3-10s.json`:

- **files 5** — decided **0**, unknown 0, unsupported **5**, errors 0. Oracle:
  **compared 0, agree 0, DISAGREE 0**.
- Detail: 3 `Forall`, 2 `Exists`.

PAR-2 means reflect the harness's unsupported-as-2×timeout convention (1080 s
for 54 files, 100 s for 5); actual max axeyum solve is ~ 2 ms (the quantifier is
rejected at lowering, before any search).

## Dominant blocker (all `unsupported`)

**The quantifier operator itself** — `Forall`/`Exists` is an unsupported
pure-Rust BV operator. Because the quantifier *body* is QF_BV (fully supported),
this slice is the prime candidate for the first quantifier-instantiation
increment. Wiring it is a solver-source change, out of scope for corpus
curation. All 59 files decline cleanly as `Unsupported`.
