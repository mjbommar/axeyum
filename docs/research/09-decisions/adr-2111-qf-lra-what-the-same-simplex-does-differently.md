# ADR-2111: `QF_LRA` — the same simplex, and the four things ours does differently

Status: accepted
Index-summary: Every reference decides the `QF_LRA` files we lose with the same Dutertre–de Moura simplex we ship, so the gap is not the algorithm's name. Census of **all 93** undecided rows over four cause channels (the give-up string is one of them and loses the largest bucket alone, [ADR-2045]): **40 `rc=134` allocation aborts, 36 `budget/other`, 7 `incomplete`, 5 `bound-no-decline`, 5 `not-applicable`**, 0 without a capture — and the typed decline name **types nothing here**, all 36 budget rows carrying `Budget::Other`, which is [ADR-2102]'s empty `decline_names` seen from the producer side. Shape census against the **107 decided as a control**: atoms separate the halves **1,351×** (median 9,462 vs 7) while **coefficient size does not** — max numeral 5 digits median and 10 max on BOTH halves, 0 of 200 rows over 18 against `i128`'s 38 — so every arithmetic decline here is pivot GROWTH, never the file's own numbers, which kills the "big coefficients" reading before a trace is read. **Reference trace, same 24 s / 8 GiB envelope, same pinned cores: z3 `smt.arith.solver=6` decides 57 of 93, `=2` (`theory_mi_arith`, predating every `lp/` refinement) decides 56, they agree on 53, and `lar_solver` accounts for FOUR files** — so "their newer simplex is better" is not the explanation; **and 33 of 93 are decided by NOBODY at 24 s, so the addressable prize is 60, not 93**. **The largest bucket by COUNT is not the largest by ADDRESSABILITY**, which this lane learned after aiming at the first: the 40 aborts are 50 % reachable (20) while the 32 rows dying inside `lra.rs` before the simplex gets a system are **28 reachable at 86–91 %** — and their trail says why, **652 rounds buying one 4.8-literal blocking clause against 1,839 atoms, with `cube_simplex_calls=651` COLD solves, one per SAT model**, where all four references keep the basis across backtracking and undo only bound stacks (z3 `lar_core_solver.h:122-129`, cvc5 `partial_model.h:220-229`, `OpenSMT` `LRAModel.cc:60-74`, `SMTInterpol` `LinArSolve.java:535-583`). Four design differences with `file:line` on both sides. **(1) The tableau**: ours was a dense `m × (nvars+m)` `Vec<Vec<Rational>>` and **none of z3, cvc5, `OpenSMT` or `SMTInterpol` stores a dense one** (`static_matrix.h:88-89`, `matrix.h:56-196`, `Tableau.h:62,118-119`, `TableauxRow.java:22-34`), all four threading the COLUMNS too. FIXED: `row_val` sparse aligned with the `row_nz` index that already existed plus a `col_rows` transpose — without which two `0..m` column scans become `O(m log nnz)`, a regression dressed as a fix. Measured on the median abort row: **1,624,162,512 cells holding 147,440 nonzeros**, 48.4 GiB against an 8 GiB ceiling, and the arm turns a core-dumped `rc=134` into a clean `unknown` at **203 MB** — mechanism, NOT a verdict claim. **(2) Theory propagation is not weak but absent**: over the 23 of 93 rows reaching the online engine, a median **19** propagations against **836,531** decisions — 24,509 decisions and 3,352,038 atom visits each — because `lra_online.rs:842` rescans every propagatable atom on every call, while z3 analyses only `touched_rows` (`lar_solver.h:284-302`), skips rows over 300 (`lp_settings.h:238`), and **pre-axiomatises the bound ORDERING as SAT clauses** (`theory_lra.cpp:2841,2963`); we generate no bound axioms at all. NOT FIXED, sized. **(3) The per-cube RE-SOLVE**, §3.2. **(4) The equality hypothesis is REFUTED on the reference side**: 66 of 93 rows are ≥50 % equalities and we do no Gaussian elimination — but z3 has no `solve_eqs` either and cvc5's is capped at `ppAssertMaxSubSize = 2`. Degeneracy handling and explanation minimisation were measured and do NOT order the field (z3 does not minimise at all and decides most). The failing allocation is **median 1.33 MB**, the STRAW at the ceiling and not the load. The shipped lever is the CONSEQUENCE, not the storage: `for_budget` reserves **128 MiB, 20 % of the 640 MiB online budget**, for a structure now costing ~1.4 MB, and that reserve decides which queries the engine ADMITS instead of dropping to the weak offline loop; `TableauReserve` ships **`Dense`** because ADR-2045's budget raise bought **0 verdicts and five NEW aborts** and ADR-2055's cap turned **18 clean exits into `rc=134`**.
Index-status: accepted
Date: 2026-09-15

## Context

`QF_LRA` on the pinned board (`bench-results/board-ab-20260915/QF_LRA.tsv`,
column `main_054104068`) reads ours **107 of 200** against z3 4.13.3's **166**
and cvc5's **145** — **59 behind**. Linear real arithmetic is fully decidable,
we ship a Dutertre–de Moura simplex, and so does every reference. The question
this lane was given is therefore not "what algorithm is missing" but **"what
does ours do differently, with a trace on both sides"**.

Branch base: `git merge-base main HEAD` is `f0904bfe2`, which **is** local
`main`'s HEAD at the time this lane opened.

Compute: **s5, physical core pairs `5,13` and `6,14`**, and nothing else.

What was already known and was read first: [ADR-2045] (74 of 93 on one route,
40 aborts + 34 Fourier–Motzkin), [ADR-2055] (the sparse ROW entry landed and
`QF_LRA` stayed at 107; the tableau is the memory), `GAP-LOG-2026-09-12.md`
("not the clock: 0 of 40 decide at 5× budget"), [ADR-2060] (the give-up
variants), [ADR-2102] (59 of 93 one-route on today's tree, and `decline_names`
empty on all 220 rows — named there as *the trace lane's* surface).

## 1. The census — all 93, four channels, and what the typed name is worth

Population re-derived from the committed board: **200 files, 107 decided, 93
undecided**, reproducing the board's 107 exactly. Every row re-run under
`--trace` at the board envelope (24 s / 8 GiB) with both existing print-only
probes armed (`AXEYUM_LRADENSEPROBE`, `AXEYUM_LRAMODELPROBE`). **93 of 93
classified, 0 without a capture.**

[ADR-2045] measured that a census built on the `; give-up` line alone loses its
own largest bucket, so the channel that answered is a **column**, never an
inference. `scripts/ledger-run-one.sh` is the right per-file runner and sends
stderr to `/dev/null` **by design** — its parser reads a verdict and a trail
from stdout — so `trace-census.sh` takes stderr itself, which is the only
channel 40 of these rows use.

| channel | bucket | n/93 |
|---|---|---:|
| `abort` | `alloc-failure` | **40** |
| `trail` | `budget/other` | **36** |
| `trail` | `incomplete/incomplete` | 7 |
| `trail` | `bound-no-decline` | 5 |
| `trail` | `not-applicable/unnamed` | 5 |

### 1.1 The typed decline name types nothing here

All **36** `budget` rows carry the ADR-2104 typed name `other` —
`Budget::Other(String)`, the catch-all `DeclineReason::from_unknown` produces
(`route_trace.rs:325`). Bucketing on the typed channel alone gives one bucket of
36. Their **prose** splits them:

| n | the producer's own sentence |
|---:|---|
| 21 | `lra:` the deadline passed building the Fourier–Motzkin unit-multiplier matrix; the elimination itself never started |
| 11 | `lra:` the deadline had already passed when the conjunctive decider was entered |
| 2 | `lra:` the deadline passed while linearizing the assertions |
| 1 | budget exhausted in the online difference-logic driver |
| 1 | timeout in the online CDCL(T) LRA driver |

Prose is exactly what [ADR-2020] and [ADR-2045] measured as untrustworthy, and
this is [ADR-2102]'s named remaining work seen from the producer side: the
consumer reads a `name` member that the renderer *does* emit, and the producer
puts `other` in it for this whole division. **Reported, not fixed** — typing the
six `lra.rs` give-up sites is a producer change with its own surface and it is
named as remaining work in §6.

### 1.2 Two structural readings the buckets give for free

**34 of 93 are bound inside `lra.rs` BEFORE the simplex gets a system** (21 + 11
+ 2 above). The 11 spent all 24 s before any arithmetic engine ran at all.

**Only 23 of 93 rows ever reach the online CDCL(T) engine** — a
`; theory-layer` line is present. The other 70 contribute **nothing** to its
counters, not a zero, and every table below states that denominator.

### 1.3 The failing allocation is small, and that is the finding

Over the 40 abort rows: **median 1,331,008 B, min 521,184, max 10,313,376.**

Read against the 8 GiB `ulimit -v` the harness enforces, a request that small
failing means the process was **already at the ceiling and this was the straw**,
not the load. The cumulative holder is [ADR-2055]'s tableau (median 10.53 GiB on
these rows). Recording it stops the next lane sizing a fix from the number in
the panic message. 39 of the 40 are `LassoRanker`.

## 2. The shape census, and the hypothesis it kills before any trace

A second authority, deliberately separate from the solver's own trail: the trail
says what our engine DID, the shape says what the file IS, and a disagreement
between them is a finding that is unreachable when one is derived from the
other. The **107 decided rows are carried as a control in the same table**,
because a median over the undecided alone answers "how big are the files we
lose", which nobody disputes, and cannot answer "does size separate the halves".

| column | A undecided median | B decided median | A/B |
|---|---:|---:|---:|
| atoms | 9,462 | 7 | **1,351×** |
| vars | 1,706 | 3 | 569× |
| asserts | 160 | 1 | 160× |
| equalities | 4,027 | 0 | n/a |
| **max numeral digits** | **5** | **4** | **1.25×** |
| **max denominator digits** | **2** | **2** | **1.00×** |

**Size separates the halves completely; coefficient size does not.** Max numeral
digits is 5 at the median and **10 at the maximum in both halves**; **0 of 200
rows exceed 18 digits on either measure**. `i128` holds 38 decimal digits, so
the input literals are nowhere near the boundary, and any arithmetic decline on
this population is **growth during pivoting**, never the file's own numbers.
That is a negative with its denominator, and it kills the "we abort on big
coefficients" reading before a single trace is read.

It also refines the record in our favour: `Rational` has **not** been a bare
`i128` pair since ADR-1702. `simplex.rs` opts in to promotion (`wide_add` and
friends), so intermediate growth does not decline at all; what remains is the
**witness** boundary in `narrow` (`simplex.rs:502`), which discards a model with
a promoted coordinate — and [ADR-2055] measured that at **0 of 23 rows**. So the
rational representation is a real difference from every reference (Yices2,
`OpenSMT` and `SMTInterpol` all grow the number; we give up at the boundary) and
it is **not what this division is losing on**.

## 3. The reference trace

Both z3 arithmetic solvers were run on the same 93 files under the same
envelope, because `smt.arith.solver` selects which arithmetic theory is built
(`src/params/theory_arith_params.h:25-32`): `2 = AS_OLD_ARITH` is
`theory_mi_arith`, the classic simplex; `6 = AS_NEW_ARITH` is `theory_lra` over
`lp::lar_solver` and is **the default for `QF_LRA`**
(`src/params/smt_params_helper.pyg:65`; `smt_params::setup_QF_LRA` does not
touch `m_arith_mode`). cvc5 1.3.4 ran beside them, all three at **the same 24 s
/ 8 GiB envelope on the same pinned core pairs as our own census**, one full
`-st` / `--stats` capture per file kept whole rather than grepped for one token.

```text
population: 93 rows we do NOT decide          (malformed: 0)

  z3 solver=6 (theory_lra, the QF_LRA default) decides   57/93
  z3 solver=2 (theory_mi_arith, classic simplex) decides  56/93
  cvc5 1.3.4                                    decides  36/93

  decided by BOTH z3 arms                  53
  decided ONLY by solver=6 (lar_solver)     4
  decided ONLY by solver=2 (classic)        3
  decided by SOME reference                60
  decided by NO reference at 24 s          33
```

**Two results, and both change what a lane should do next.**

**`lar_solver` accounts for 4 files of 93.** z3's two arithmetic theories agree
on 53 of the 57 solver-6 decides, and the classic `theory_mi_arith` — which
predates every data-structure refinement in `lp/` — decides 56 on its own. So
"their newer simplex is better than ours" does not explain this division: *both*
of z3's simplexes beat ours by about the same margin, which is what you would
expect if the difference is structural rather than a refinement.

**33 of 93 are decided by NO reference at 24 s.** The addressable prize on this
population is **60, not 93**, and a gap number that does not say so promises
work that is not there. A row nobody decides is not proof that it is unwinnable
— only that it is not reachable by these three at this budget, which is the
honest ceiling on what a gap can mean.

### 3.1 The bucket that is largest is not the bucket that is reachable

Crossing our own sub-buckets with "does any reference decide it":

| sub-bucket | n | addressable | share |
|---|---:|---:|---:|
| `alloc-failure` | **40** | 20 | 50 % |
| `lra:` deadline building the Fourier–Motzkin unit-multiplier matrix | 21 | **18** | **86 %** |
| `lra:` deadline already gone when the conjunctive decider was entered | 11 | **10** | **91 %** |
| `incomplete` — online model did not replay | 7 | 4 | 57 % |
| `not-applicable` | 5 | 3 | 60 % |
| `bound-no-decline` / `nra` | 3 | 3 | 100 % |
| `lra:` deadline while linearizing | 2 | 1 | 50 % |
| `budget` — online difference-logic driver | 1 | 1 | 100 % |
| `bound-no-decline` / `fd:parse` | 2 | 0 | 0 % |
| `timeout` — online CDCL(T) LRA driver | 1 | 0 | 0 % |

**This lane fixed the largest bucket by COUNT, and the reference trace says that
was not the largest by ADDRESSABILITY.** The 40 aborts are 50 % reachable (20);
the 32 rows that die inside `lra.rs` before the simplex ever gets a system are
**28 reachable, at 86–91 %**. Said plainly so the next lane does not repeat it:
sizing work from a census alone picks the wrong bucket, because a census counts
rows and cannot say which of them anyone can win.

### 3.2 What those 32 rows are doing — and it is the re-solve

The trail of `_standard_init5_ground.i_3_2_2.bpl_7.smt2`, the representative of
the 11-row "deadline already gone" group under the written picking rule:

```text
; route decided_by=none bound_by=nra bound_ms=23978 total_ms=24018 attempts=15
; lazy-smt  atoms=1839  lra_rounds=652
            skeleton_ms=6317  theory_ms=16703
            cube_collect_ms=3552  cube_simplex_ms=13102  cube_simplex_calls=651
            cube_matrices=0  cube_fm_ms=0
            blocking_clauses=651  blocking_literals=3137
```

Twenty-four seconds buys **652 rounds**, each of which solves the Boolean
skeleton to a TOTAL assignment, hands every atom to a **cold** conjunctive
decision, and returns **one blocking clause of 4.8 literals against 1,839
atoms**. `cube_simplex_calls=651` with `cube_matrices=0`: six hundred and fifty
one simplex solves **from scratch**, one per SAT model.

That is the repository's own named pattern — *"re-solves from scratch what it
should update"* — and it is the sharpest contrast with every reference read for
this lane. **All four keep the basis across SAT backtracking; only bound stacks
are undone.** z3's `lar_solver::push` snapshots *only* `m_column_types` and the
strategy (`lar_core_solver.h:122-129`) — the matrix, the basis, the basis
heading and `m_r_x` are not saved, and `stacked_vector m_r_pushed_basis` is
declared and referenced nowhere — while `find_feasible_solution` resumes from
the existing basis after patching only the columns whose bounds changed
(`update_x_and_inf_costs_for_columns_with_changed_bounds_tableau`,
`lar_solver.cpp:1280-1283`). cvc5's tableau and assignment are plain members and
not context-dependent, so a pop restores bounds and nothing else
(`partial_model.h:220-229`); `OpenSMT` pops only `bound_trace`
(`LRAModel.cc:60-74`) and demotes a retracted basic variable to *quasi-basic*
rather than pivoting it out (`Simplex.h:112-116`); `SMTInterpol`'s
`backtrackComplete` marks everything dirty and calls `fixOobs()` without
rebuilding anything (`LinArSolve.java:535-583`).

**Why these files are on that route at all** is the admission screen: 1,839
atoms is past what the online CDCL(T) engine's byte budget admits, so they fall
through to the offline lazy-SMT loop, whose own module doc already calls it
"much weaker" and measures it at "a round costs 48–2,000 ms and buys a clause of
2.0–19.0 literals against 265–1,736 atoms" (`lra_route.rs`). The online engine
**does** keep its basis warm — `simplex_cold_restarts=0` on every traced row —
so this is a routing outcome and not a missing capability. That is exactly the
screen `TableauReserve::Sparse` moves, and it is why the lever is where it is
rather than on the storage.

## 4. The design differences, with `file:line` on both sides

Three here; the fourth — the offline route's per-cube RE-SOLVE, which every
reference replaces with a warm basis — is §3.2, because the reference trace is
what showed it to be the reachable one rather than the largest.

### Claim 1 — the tableau is dense here and sparse in every reference

**Ours, before this lane.** `Tableau::row: Vec<Vec<Rational>>`
(`crates/axeyum-solver/src/simplex.rs`), rebuilt by `reset_structure` as
`vec![Rational::zero(); self.n]` per row: a fully dense `m × (nvars+m)` matrix
of 32-byte cells. `row_nz` existed beside it and its own doc said what it was —
*"a sparse index over dense storage, not a sparse representation"*.

**[ADR-2055]'s price**, over the 74 rows on that route: a median **19,198,877
cells holding 34,555 nonzeros — 0.0288 % dense**, "a structure ~3,500× larger
than its data", 5.07 GiB median peak RSS against an 8 GiB ceiling.

**Every reference.**

| solver | storage | `file:line` |
|---|---|---|
| z3 | `static_matrix<mpq, numeric_pair<mpq>>`, doubly-linked row **and** column strips; `set` returns early on a zero so zeros are never stored; the dense `matrix<T,X>` base is inherited only under `Z3DEBUG` | `src/math/lp/static_matrix.h:88-89,70-74`; `static_matrix_def.h:256-257` |
| cvc5 | one `std::vector<MatrixEntry<T>>` arena with a free list, rows and columns intrusive lists over it | `src/theory/arith/linear/matrix.h:56-136,139-196,199-366` |
| `OpenSMT` | `rows_t = vector<unique_ptr<Polynomial>>` (sorted `vector<Term>`) plus `cols` of per-column row lists | `src/tsolvers/lasolver/Tableau.h:62,118-119,25-56` |
| `SMTInterpol` | flat `int[] mEntries` of `x0 c0 x1 c1 …` with a `BigInteger[]` escape hatch, plus a per-column `BitSet` of rows | `TableauxRow.java:22-34`; `LinArSolve.java:102-113` |

z3 goes further: a row is created per distinct **compound term**, deduplicated
through `m_normalized_terms_to_columns`, and a single-variable atom (`x ≤ 3`)
creates **no row at all** — `is_unit_var` short-circuits and the atom becomes a
column bound (`theory_lra.cpp:807-809,856-857`). Ours makes one row and one
slack column per *constraint*. That is a second-order difference on the same
axis and it is **not** addressed here.

**Fixed.** `row_val` is now a sparse vector positionally aligned with `row_nz`,
and `col_rows` is the transpose. The column index is not optional: two loops
(`update_nonbasic`, and the pivot's capture of the entering column before the
elimination zeroes it) read a whole column by walking `0..m`, which sparse rows
alone turn from `O(m)` into `O(m log nnz)` — a regression dressed as a fix. Cost
is now `nnz × 40` bytes against `m × (nvars+m) × 32`, a factor of **439 at
ADR-2055's median** and 3,472 at its density extreme; z3's own per-nonzero cost
is about 52 B, so the two representations are now in the same units.

### Claim 2 — theory propagation is not weak, it is absent

Over the **23 of 93** rows that reach the online engine (the other 70
contribute nothing, not a zero):

| counter | median |
|---|---:|
| `decisions` | 836,531 |
| `theory_conflicts` | 3,774 |
| **`theory_propagations`** | **19** |
| `bound_scan_calls` | 939,591 |
| `bound_scan_atoms` | 12,197,876 |
| `simplex_pivots` | 15,079 |
| `simplex_rows` × `simplex_columns` | 907 × 1,086 |
| `final_check_core_literals` | 66,088 |

| ratio | median |
|---|---:|
| **SAT decisions per theory propagation** | **24,509** |
| **atom visits per theory propagation** | **3,352,038** |
| literals per conflict core | 17.5 |
| pivots per conflict | 4.3 |
| tableau nonzeros (mean per check) | 8,086 → **0.82 % dense** |

**Ours.** `LraTheory::propagate_bounds` (`crates/axeyum-solver/src/lra_online.rs:835`)
opens `for index in 0..self.propagatable.len()` on **every call**, with no
"which bounds changed since last time" filter, and the driver calls it once per
decision. The emission cap (`MAX_BOUND_PROPAGATIONS_PER_CALL = 256`) bounds the
OUTPUT; nothing bounds the input, and at a median 939,591 calls the total is
12.2 million atom visits for 19 literals.

**z3.** `propagate_bounds_with_lp_solver` (`src/smt/theory_lra.cpp:2400-2419`)
analyses only `propagate_bounds_for_touched_rows` (`src/math/lp/lar_solver.h:284-302`),
a set reset after each pass; a row over
`settings().max_row_length_for_bound_propagation = 300` (`lp_settings.h:238`) or
carrying a big coefficient is skipped entirely (`lar_solver.cpp:379-384`); and
`bound_analyzer_on_row::analyze_row` yields **at most two** implied bounds per
row (`bound_analyzer_on_row.h:54-80`). There is no numeric per-call cap because
the work is bounded by what changed.

**And z3 does not need the theory for the unate half at all.** The bound
ORDERING on each variable is pre-axiomatised as SAT clauses by
`mk_bound_axioms` / `flush_bound_axioms` (`theory_lra.cpp:2841,2963`), so
`x ≤ 3 → x ≤ 5` is a unit propagation in the SAT core. `OpenSMT` does the same
eagerly at theory level (`LASolver::getSimpleDeductions`, `LASolver.cc:545-569`,
walking every weaker bound); `SMTInterpol` queues every `BoundConstraint` in the
interval between the old and new bound inside `setBound`
(`LinArSolve.java:957-964,996-1002`). **We have no bound-axiom generation
anywhere** — `grep -niE 'bound.axiom|unate'` over `lra_online.rs`,
`lra_theory.rs` and `cdclt.rs` returns nothing.

**NOT FIXED.** It is sized, it is named, and it is the largest single lever this
lane found that it did not pull; see §6.

### Claim 3 — the equality hypothesis is refuted on the reference side

66 of 93 undecided rows are ≥50 % equalities (median 4,027 of 9,462 atoms)
against 19 of 107 decided, and we do no Gaussian elimination: `Rel::Eq` becomes
one slack row with `lower = upper = b` (`simplex.rs`, `set_row_bound`). That
looks like the whole story and it is not.

**z3 has no Gaussian elimination either.** `asserted_formulas::reduce`
(`src/solver/assertions/asserted_formulas.cpp:267-311`) has `propagate_values`,
`nnf_cnf`, `elim_term_ite` and macros — and **no `solve_eqs`** — and the
`QF_LRA` tactic adds nothing (`src/tactic/smtlogics/qflra_tactic.cpp:84`). What
it does have is term substitution (`lar_solver::subst_known_terms`,
`lar_solver.cpp:2044-2059`) and fixed-variable pivoting-out
(`remove_fixed_vars_from_base`, `lar_solver.cpp:1151-1178`, called
probabilistically 1-in-10). cvc5's `ppAssert` solves a top-level equality for a
single variable but is capped at `options().arith.ppAssertMaxSubSize`,
**default 2** (`arith_options.toml:336-341`). `SMTInterpol`'s `pivotEqualities`
is **entirely commented out** (`LinArSolve.java:1122-1140`).

So "we lack equality elimination" is **not** a design difference against the
references. It is recorded here as a **refuted** hypothesis with its citations,
because it is the one a reader arrives at from the shape table alone and it
would have cost a lane.

### Two differences measured and found NOT to be the gap

- **Degeneracy handling.** Ours: `PivotPolicy::bland_threshold`, scaled, on
  repeat leavings. z3: Bland after `m_bland_mode_threshold = 1000` repeated
  *leavings*, hardcoded (`lp_primal_core_solver.h:645`). cvc5: per-basic-variable
  `arithPivotThreshold`, **default 2**, and for `QF_LRA` the heuristic phase is
  disabled outright (`set_defaults.cpp:812-850`). `OpenSMT`: Bland after
  `repeats > getNumOfCols()` (`Simplex.cc:47`). Four different answers; ours is
  inside the spread, and `bland_fallbacks` reads 0 on the traced files.
- **Explanation minimisation.** Ours: 17.5 literals per conflict core. z3 does
  **not** minimise — `shrink_explanation_to_minimum` is a commented-out call and
  exists nowhere else in the tree (`theory_lra.cpp:3708`) — and still decides
  166. cvc5 (`minimallyWeakConflict`, `linear_equality.cpp:773-838`) and
  `SMTInterpol` (`SOIPivoter.computeConflict`, `:333-385`) do minimise, and cvc5
  decides fewer than z3. The axis does not order the field, so a core-size
  change is not where this division's 59 files are.

## 5. What shipped, and what it is gated on

**The storage ships as the only path**, for [ADR-2055]'s stated reason: a lever
defaulting `Off` leaves the new path exercised by no gate, and here the gates
that matter are the five z3 differential fuzzes and the full solver sweep. The
A/B is therefore two binaries, whose SHAs differ and are printed.

**The lever is the consequence, not the storage.**
`NormalizationLimits::for_budget` spends `MAX_TABLEAU_CELLS × 32 B` = **128 MiB
— 20 % of the 640 MiB online LRA budget** — on the tableau before coefficients
get any, and `estimated_bytes` adds it into every projection. That is not
accounting: it decides which queries the online CDCL(T) engine **admits**, and
only 23 of 93 rows reach it. `TableauReserve` (`lra_online.rs`) makes it
`Dense` (128 MiB, today's behaviour byte for byte) or `Sparse` (400,000
nonzeros × 40 B = 16 MiB), read once from `AXEYUM_LRA_TABLEAU_RESERVE`.

**It ships `Dense`.** The direction of the routing consequence does not follow
from the direction of the memory correction, and this repository has measured
that surprise twice: [ADR-2045] raised the same budget to 8 GiB and got 21 rows
reaching the engine, **0 newly decided, and five NEW aborts**; [ADR-2055] capped
the tableau and turned **18 clean exits into `rc=134`**, because "the unpriced
allocation was accidentally load-bearing".

400,000 is `MAX_TABLEAU_CELLS / 10`, **named as the round number it is**. What
it is measured against is real: 49× the median 8,086 nonzeros over the 23 rows
that reach this engine and 11.6× the median 34,555 [ADR-2055] measured on the
offline route. Nobody has taken the tail.

### The lever is INERT on the population it was aimed at, and a mechanism probe said so before the A/B did

This is the finding this lane is least pleased with and the one most worth
keeping. §3.2 argued that the 32 `lra.rs` rows are on the weak offline route
because the online engine's byte budget refuses them, and that
`TableauReserve::Sparse` — freeing 112 MiB of a 640 MiB budget — is the screen
that moves them. **It is not.** Both arms were run on the group's representative
and produced the *same route, the same give-up, and the same
`online_probe=admission-screen`.**

The screen that actually refuses them is `lra_theory.rs:305`, and it is an atom
COUNT wearing byte clothing:

```rust
let admitted_atoms = budget_bytes / crate::lra_online::BYTES_PER_ADMITTED_ATOM;
if atom_terms.len() > admitted_atoms { … refuse … }
```

with `BYTES_PER_ADMITTED_ATOM = DEFAULT_ONLINE_LRA_BUDGET_BYTES / 1_024`, so at
the default budget `admitted_atoms` is **exactly 1,024** — its own doc says it
is "byte-identical to the `MAX_ONLINE_LRA_ATOMS = 1_024` count it replaces". The
representative has **1,839 atoms** and is refused there. `TableauReserve` is
read by `NormalizationLimits::for_budget` and `estimated_bytes`, both of which
run **after** this screen has already decided. The two arms differ by 122 MiB
against 15 MiB and **neither number appears in the expression that refuses the
file**.

That is ADR-2045's own finding one level down — *"one knob drives two screens
wanting opposite settings"* — and it means **the lever's A/B was not run,
deliberately.** It would have printed `net +0` on this population by
construction, and `net +0` from an inert arm is indistinguishable from `net +0`
from a working one that does not help. Asking what the command would print if
the lever were doing nothing, and finding that it is what the command would
print, is the whole reason to take the mechanism probe first.

The lever still ships, still `Dense`, and is still correct about bytes: the
reserve it fixes is real and is spent on every projection that gets past the
outer screen. What it is **not** is the thing that moves the 32 rows. The screen
that would is `lra_theory.rs:305`, and that experiment has already been run:
[ADR-2045] raised `memory_limit_mb` to 8 GiB, which does move it (13,107 atoms
admitted), and got **21 rows reaching the engine, 0 newly decided, 19 dying at
"model did not replay"**. So the route is not what is holding this population —
the online engine's own capability is, which is claim 2.

### The mechanism, on one file, before any A/B

`AXEYUM_LRADENSEPROBE=1` on `LassoRanker/CooperatingT2/sas2.t2.c_Iteration6_Lasso_6-phaseTemplate.smt2`
— the row at the **median** failing allocation of the 40, chosen from the
committed table and not by eye:

```text
; LRADENSEPROBE site=simplex-fallback-entry rss_kb=205588 nvars=2546 constraints=39048
; LRADENSEPROBE site=dense-rows-built     rss_kb=207672 nvars=2546 m=39048 nnz=147440
; LRADENSEPROBE site=feasible_within-entry rss_kb=207676 nvars=2546 m=39048
                                          tableau_cells=1624162512
```

**1,624,162,512 cells holding 147,440 nonzeros.** At 32 B a cell that tableau is
**48.4 GiB** against an 8 GiB ceiling, which is why the base binary dies; at
40 B a nonzero the same system is **5.9 MB**. Measured side by side on one
pinned core:

| | base (`815489e3…`) | arm (`af93b938…`) |
|---|---|---|
| exit status | **`134`, core dumped** | **`0`** |
| verdict | none | `unknown` |
| peak RSS at `feasible_within-entry` | never reached | **203 MB** |

This is the mechanism and **it is not a verdict claim**: the arm answers
`unknown`, which is what [ADR-2045] predicted when it converted 20 such rows and
found "not one is decided". What changed is that a `rc=134` core dump became a
first-class `unknown` and the ladder below it now runs. Whether that buys any
verdict across the population is what the A/B answers, and one file cannot.

### The soundness-negative fixture

The one way a sparse tableau can be wrong that a dense one cannot is by **losing
a cell**: a cell that should be nonzero and is not stored makes the row weaker
than the constraint it represents, and a weaker row is satisfiable where the
real one is not — a **wrong `sat`**.

`a_fill_in_cell_the_sparse_rows_must_not_lose_decides_a_soundness_pair` is a
three-cycle `x0 − x1 ≤ 0, x1 − x2 ≤ 0, x2 − x0 ≤ c`, INFEASIBLE at `c = −1` and
FEASIBLE at `c = +1`, differing in one constant. **No input row mentions all
three variables**, so the coefficient that closes the refutation exists only as
FILL-IN written by `pivot_and_update` into a column the row did not have. It is
a PAIR with the satisfiable arm **first**, so the `unsat` is read as a
distinction the engine draws and not as a blanket refusal, and the certificate
is re-verified against the original rows by `check_farkas`.

### Two existing tests changed, neither weakened

- `col_nnz_matches_a_recount_after_every_pivot`. The dense `recount_columns`
  re-derived the index by **scanning the row values**, so it was idempotent on a
  pivoted tableau. A sparse row has no value outside its index, so that function
  split in two (`rebuild_from_input`, `recount_columns`), and comparing `row_nz`
  against the second would have been a value compared with itself — **a control
  that cannot fail**, the exact shape this repository has been caught by. It now
  checks `col_rows` against the recount plus the three properties the engine
  relies on directly: the two vectors agree in length, the index is strictly
  ascending (Bland's rule is "smallest usable index"), and no stored value is
  zero.
- `a_poisoned_engine_recovers_a_consistent_tableau`. Its tear is now **worse**
  than the dense one: dense storage could only be given wrong VALUES, the sparse
  pair can be given a wrong SHAPE, so it empties `row_nz` while leaving
  `row_val` populated. The verdict comparison alone would not have caught a bad
  recovery — `cell` binary-searches an empty index and answers zero for every
  column, a perfectly consistent and completely wrong row.

### The mutation run, and the prediction it falsified

`scripts/tests/mutation_controls.py simplex-sparse-tableau`, baseline green at
**36 tests**, filtered to `simplex::tests` rather than to one test so a kill
count is a claim about a population. All three mutations are `killed N` — the
harness's only outcome that supports a coverage claim — and the run exits 0.
`--check-anchors`: 141 suites, 1,068 anchors, **stale=0**.

| guard removed | kind of damage | killed |
|---|---|---:|
| the fill-in write that enters a newly-nonzero cell | soundness | **16** |
| the transpose entry removed when a cell goes to zero | consistency | **10** |
| the sorted position the transpose keeps its rows in | determinism | **8** |

**None killed exactly one, and that is reported rather than engineered away.**
The rule this repository keeps — *delete one guard and require that exactly one
test dies* — exists because six of seven guards in one suite were removable with
everything still green, since they all rejected through **one shared check**.
The property it protects is that distinct guards have distinct consumers, and
these do: the three kill sets are different sets, not nested ones. Only the
first takes `a_fill_in_cell_…`, `single_var_infeasible_carries_farkas`,
`equality_system_infeasible`, `two_var_infeasible` and
`the_cost_counters_are_populated_and_bounded_by_the_work`, and the second and
third differ from each other by two. A literal one-kill mutation would have had
to be constructed for the number, which is the opposite of what the rule is for.

**The third mutation falsified this lane's own prediction, and that is the most
useful line in the table.** Appending to `col_rows` instead of inserting in
order was registered as a DETERMINISM defect on the expectation that it would be
visible *only* to the recount, because it changes no verdict — every
exact-rational sum is the same sum in a different order. It killed **eight**,
including `the_tie_break_is_seeded_and_reproducible` and
`the_bland_fallback_is_reachable_and_verdict_preserving`. So the transpose's
ORDER is load-bearing for reproducibility and not merely for the index check:
the order of the adds is where an arithmetic decline lands, and the pivot
sequence follows from it. The comment in `col_rows` claiming the order matters
was a guess when it was written; it is now measured.

One consequence worth stating against this lane's own work: the
soundness-negative fixture is covered by fifteen other tests, so it is a
**named and readable** guard rather than a uniquely necessary one. That is still
worth having — the fifteen fail with no hint that a fill-in cell was lost — but
it is not the sole thing standing between the engine and a wrong `sat`.

## 6. What this lane did not do, sized

- **Bound-axiom clauses / touched-driven propagation** (claim 2). The largest
  unpulled lever: 19 propagations per 836,531 decisions, 12.2 M atom visits
  each. The touched-driven form is *provably* output-equivalent at fixpoint — an
  atom over a form whose bound did not change was not entailed last call and
  cannot have become entailed — so it is a performance change with an exact
  control available, and `the_scan_filter_offers_exactly_what_a_full_scan_would`
  (`lra_online.rs`) is the pattern to copy. The bound axioms are a separate,
  larger change.
- **Typing the six `lra.rs` give-up sites** so `decline_names` stops reading
  `other` for this whole division ([ADR-2102]'s named work, §1.1).
- **One row per distinct compound term, unit atoms as pure column bounds**
  (z3 `theory_lra.cpp:807-809`), which attacks `m` rather than the cost per
  cell.
- **The `narrow` witness boundary** (roadmap 2.3) stays closed; measured at 0 of
  23 rows and therefore not this division's problem.

[ADR-2020]: adr-2020-the-give-up-detail-contains-the-separator.md
[ADR-2045]: adr-2045-the-bound-is-not-the-wall-qf-lra-is-one-offline-dense-engine.md
[ADR-2055]: adr-2055-the-tableau-is-the-memory-and-capping-it-costs-eighteen-clean-exits.md
[ADR-2060]: adr-2060-the-give-up-variant-could-not-tell-six-gates-apart-and-nothing-asked-it-to.md
[ADR-2102]: adr-2102-the-outcome-ledger.md
