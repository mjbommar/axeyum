# QF_SLIA curated slice (committed, reproducible, **capped**)

Curated, **committed** SMT-LIB `QF_SLIA` (quantifier-free strings + linear integer
arithmetic) slice for the measured head-to-head of `axeyum_solver::check_auto`
(`--backend solver`) against the **Z3 4.13.3 binary** (z3 supports the strings
theory, so this is a *real* oracle, unlike the finite-field slices). `QF_SLIA` is
the largest practical string division — it is where real-world string solving lives,
and the seam of interest is the **str ↔ Int bridge**: `str.len`, `str.indexof`,
`str.to_int` / `str.from_int` connecting the string theory to the Int constraints.

## This slice is capped (50 of 105 clean files)

The cvc5 regression suite has **105** files clean under the standing filter (plain
`assert`+`check-sat`, `:status` ground truth, no `push`/`pop`/`get-value`/…). That
is too large to vendor in-tree, so this slice is **capped at 50 files** spanning
easy → hard. The selection is deterministic and reproducible:

- **all 14** files from `regress2` / `regress3` / `regress4` (the hard tier), plus
- a deterministic even stride of **36** files across the 91 `regress0` / `regress1`
  files (indices `round(i·(n−1)/35)` over the sorted list, deduplicated).

The cap is a vendoring limit, not a soundness or measurement exclusion. The full
105-file set is re-derivable with `scripts/curate-public-slice.py QF_SLIA -`.

```sh
target/release/axeyum-bench \
  corpus/public-curated/non-incremental/QF_SLIA/cvc5-regress-clean \
  --logic QF_SLIA --backend solver --compare-z3 --timeout-ms 10000 --jobs 4 \
  --out bench-results/baselines/qf-slia-cvc5-regress-clean-solver-vs-z3-10s.json
```

## Measured baseline (`--backend solver --compare-z3 --timeout-ms 10000`)

| metric | value |
|---|---|
| files | 50 |
| decided | **15** (sat 10, unsat 5) |
| unknown | 6 (all `Incomplete`) |
| unsupported | **29** |
| errors | 0 |
| Z3-binary oracle compared | 14 |
| Z3-binary oracle **agree** | **14** |
| Z3-binary oracle **DISAGREE** | **0** |
| `:status` agree (incl. oracle-skipped files) | 15 |
| model-replay failures | 0 |
| PAR-2 mean (s) | ~5.7 |

**DISAGREE = 0** on the binding `--compare-z3` head-to-head, and **every decided
verdict also matches its `:status` ground truth**. An independent direct re-run of
the z3 binary on all 15 decided files (outside the harness) confirms zero
disagreements. One decided file (`update-ex4-seq.smt2`, axeyum `sat`, matches
`:status`) is oracle-skipped because z3 4.13.3 rejects `seq.update` — that is an
oracle gap, not a disagreement; the harness correctly counts it as skipped, which is
why the oracle compared 14 while `:status` agree is 15.

A low decide-rate is the **expected, honest** result for the largest practical
string division — the win is opening QF_SLIA with a real z3 head-to-head and
**DISAGREE = 0**, declining what it cannot soundly bound rather than guessing.

### The str ↔ Int bridge holds (the seam of interest)

The bridge files in this slice — `bug613`, `unsound-0908` (sat), `at001`,
`issue4701_substr_splice`, `loop008`, `cmi-split-cm-fail` (sat) — exercise
`str.len` / `str.indexof` / `str.substr` / `str.at` against Int constraints, and
**all of them decide correctly** (every one agrees with z3 and `:status`). No
soundness bug surfaced on the str ↔ Int seam; the length/index ↔ Int reduction is
sound on this slice.

### Dominant blocker: the bounded-length string model (ADR-0029)

axeyum models strings as **fixed-bounded length** bit-vectors, so the 29
`unsupported` files are dominated by hitting that bound (a clean decline → never a
wrong verdict). The breakdown:

| count | blocker |
|---|---|
| 8 | `str.++` result exceeds the bounded length cap (ADR-0029) |
| 5 | string literal longer than the bounded length (ADR-0029) |
| 5 | `str.replace_re` / `str.replace_re_all` over a non-constant string (moving-cursor regex outside the wired sound subset) |
| 3 | `str.update` / `seq.update` outside the wired bounded subset |
| 3 | `str.indexof_re` (a cvc5 extension, not in the SMT-LIB UnicodeStrings theory) |
| 2 | sequence packing unsupported (a `Seq` of a non-packable element sort) |
| 2 | regex constant `re.allchar` / non-literal `str.to_re` (ADR-0029) |
| 1 | string operator applied to a non-string sort |

The single largest theme (13 of 29: the two bounded-length rows) is the
**bounded-length cap itself** — symbolic / long strings the fixed-width model
cannot represent. Raising the cap or wiring an unbounded string theory is a
solver-source change (out of scope for corpus curation); the str ↔ Int bridge ops
that *do* fit the bound decide soundly. The 6 `unknown`s are genuine
search-`Incomplete` results on the in-bound fragment — the measured frontier this
baseline exists to track.

## Provenance & selection

Files reuse the cvc5 regression suite (`references/cvc5/test/regress`, a gitignored
sparse-blobless clone of the `test/regress` tree); each vendored name flattens its
original path (`/` → `__`). The standing clean filter
(`scripts/curate-public-slice.py QF_SLIA -`) applies: exact `(set-logic QF_SLIA)`,
`(set-info :status …)` ground truth, plain `assert`+`check-sat` only, no `.smtv1`,
no `check-sat-assuming` / `get-value` / `push` / `pop` / `set-option :incremental`.
The 50-file cap on top of that filter is described above.
