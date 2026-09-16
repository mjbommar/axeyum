# Lane `nra-cell-exact` — exact delineability and the clause loop (ADR-2126)

<!-- plan-section: lane-status -->

Status: the exact delineability check, its scope guard, the `CadDecline::Projection`
split, the clause loop and both fuzz seed classes are landed. **No sample is
load-bearing in `nra_cell_cert` any more.** Ship decisions are in ADR-2126.

## What this lane was

[ADR-2121](../../research/09-decisions/adr-2121-single-cell-cad-for-nra.md)
shipped the single-cell CAD route's `sat` half and withheld its `unsat` for one
reason it stated plainly: the certificate checker's delineability test was
**sampling**, and sampling can falsify delineability but never establish it.
This lane replaces that test.

## The exact check, in three parts

| check | what | status |
|---|---|---|
| 6a | leading coefficients, discriminants and pairwise resultants required to be **root-free on the cell**, by Sturm counting against its ALGEBRAIC endpoints | **exact** — no sample anywhere |
| 6b | the old three-point probe | demoted to an independent **cross-check**; a failure after 6a accepts is a disagreement between two implementations of one property |
| 6c | `NestedOpenGeneralization` — a generalisation over an open cell may not rest on **another** generalisation, because that needs delineability over a 2-D region and 6a is 1-D | **new**; ADR-2121's check had the same gap and named none of it |

Resultants are Sylvester determinants over ℚ[t] through `axeyum_ir::poly`'s exact
evaluation–interpolation. `None` from any step is a rejection: a check that
cannot run must not be reported as one that ran.

## The sizing correction

ADR-2121 flagged its own `CadDecline::Projection` count of 2 as an upper bound.
Split into four causes and re-run on the same 24 files:

| files | cause | what would fix it |
|---:|---|---|
| 12 | `non-conjunctive` | the clause loop |
| 6 | `algebraic-witness` | an algebraic sample |
| 2 | *decided* | nothing |
| 1 | `certificate-rejected` | the checker accepting what the producer built |
| 1 | `projection-arithmetic` | wider coefficient arithmetic |
| **1** | **`projection-sylvester-dim`** | **a fraction-free (Bareiss) determinant** |
| 1 | `root-ordering` | exact ordering of two critical values |

**The determinant lever is worth 1 file, not 2.** And the other six rows are a
control: this scan ran under the exact checker and `certificate-rejected` is
still 1, *decided* still 2 — the strengthening cost zero files.

## The clause loop

`nra_clause_loop.rs`: CDCL(T) over sign atoms with single-cell CAD as the
theory, through `axeyum_cnf::IncrementalSat` rather than a new SAT loop. Removes
the `non-conjunctive` refusal that costs 12 of the 24.

`sat` rests on **nothing** in the Boolean layer — the sample is replayed against
the original assertions. `unsat` is **withheld**
(`ClauseLoopUnsatUncertified`), and the evidence that would close it is named: a
`CellRefutation` per blocking clause plus a DRAT refutation of the clause set.
A blocking clause can only make the loop *miss* a model, never invent one, so on
the sat-only arm an unsound one costs completeness and cannot cost soundness.

`AXEYUM_NRA_CAD=clause-loop` ships **OFF**, unmeasured.

## The numbers

Interleaved A/B, one binary and two env values, four shards on s5 cores
1, 9, 3, 11, 24 s / 8 GiB. Arm A is the shipped default (`single-cell-sat`);
arm B is `single-cell`. They differ in exactly `emit_unsat`.

| division | rows | A | B | net | gain / loss / flip | vs `:status` |
|---|---:|---:|---:|---:|:---:|---|
| QF_NRA (pinned) | 200 | 121 | **122** | +1 | 2 / 1 / 0 | 0 over 241 |
| QF_NRA (held-out) | 200 | 109 | 109 | +0 | **0 / 0 / 0** | 0 over 216 |
| QF_NIA | 200 | 79 | 79 | +0 | **0 / 0 / 0** | 0 over 158 |
| QF_LRA (control) | 200 | 107 | 107 | +0 | **0 / 0 / 0** | 0 over 194 |

Both baseline arms reproduce ADR-2121's own numbers (QF_NRA 121, QF_LRA 107).
The `sat` column is identical on both arms, which is what "they differ in exactly
`emit_unsat`" predicts, measured rather than assumed.

Three-pass recheck of every mover: **2 STABLE-GAIN, 0 STABLE-LOSS, 1
BOTH-DECIDE, 0 UNSTABLE**, exit status 0 on all 18 runs. The sweep's one loss is
arm B deciding it `unsat` 3 of 3 on a quiet core — and `--trace` had already
shown both arms declining that file at `nra-real-root` in microseconds, with its
`unsat` coming from a later rung at 18.8 s of a 24 s budget.

**Across all four sweeps: 0 `sat`↔`unsat` flips and 0 disagreements against
declared `:status` over 809 comparable verdicts.**

Mutation: `nra-cell-exact-delineability` and `nra-cell-exact-clause-loop`, each
killing **exactly one** named fixture; `--check-anchors` `suites=151 anchors=1100
stale=0`.

Differential fuzz, `nra_differential_fuzz` 7 tests green with **DISAGREEMENTS: 0**:

| class | instances | decided | agreements |
|---|---:|---:|---:|
| general | 2000 | — | **0 disagreements** |
| single-cell | 1500 | 239 (237 sat / 2 unsat) | 239 |
| **clause-loop (new)** | 1500 | **368** | **368** |

1,485 of the 1,500 clause-loop instances carry a real disjunction (asserted).
`open_deeper_cells=2` and `exact_delineability_tests=4` — asserted nonzero, so
whether the fuzz reaches check 6a is a number and not a hope.

## The ship decision

**`CAD_DEFAULT` moves to `CadPolicy::SINGLE_CELL`: the route's `unsat` half
ships ON.** Every gate met — 0 stable losses on both draws, 0 flips, the control
unmoved, 0 `:status` disagreements.

**And the honest limit on that.** The gain is two files in four hundred, the
held-out draw found none, and **neither of the two rests on the exact check** —
both are atom-cell refutations that never reach it. The decision is not "the
exact check bought +2"; it is that the reason ADR-2121 withheld this half no
longer exists, the half costs nothing on two independent draws and a control,
and it is worth two files where its shape appears.

`AXEYUM_NRA_CAD=clause-loop` ships **OFF**, unmeasured on any corpus.

## What this lane did not do

- **Lazard evaluation.** ADR-2126 §2 prices it: minimal-polynomial extraction, a
  tower of algebraic extensions, univariate factorization *over each level of
  that tower*, exact multivariate division, and a Gröbner basis under an
  elimination order. cvc5 gets all of it from GPL CoCoALib and still defaults
  `nlCovProjection` to `MCCALLUM`. A lane of its own.
- **The 2-D generalisation** (check 6c's boundary).
- **The clause loop's `unsat`**, and the algebraic sample (6 of 24), and the
  fraction-free determinant (1 of 24, measured).
- **A gap found and left**: `config_registry`'s `GOVERNED_FILES` contains
  `nra.rs` and none of `nra_real_root.rs`, `nra_single_cell.rs`,
  `nra_cell_cert.rs` or `nra_clause_loop.rs`, so every bounded-cost constant on
  this route is watched by nothing. Adding the files demands registry entries
  for all their constants at once — a cross-lane change, recorded rather than
  made.

## Landed changes

| commit | what |
|---|---|
| `2d72b5e6d` | `CadDecline::Projection` split into four causes with four different fixes |
| `8bb5cb970` | exact delineability (6a), the sampling probe demoted to a cross-check (6b), the scope guard (6c) |
| `6e4c70754` | the 24-file re-bucketing and its controls |
| `a699cf4bc` | the clause loop, its arm, and seven tests |
| `0c9c5da61` | mutation restructure: one mutation, one dead test |
| `51c3baf4b` | the clause-loop fuzz class, the 6a-reached tally, the pairwise-resultant fixture |
| `21fb3897e` | the three-division A/B data and the held-out draw |
