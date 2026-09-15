# ADR-2111: `QF_LRA` — the same simplex, and the three things ours does differently

Status: accepted
Index-summary: Every reference solves the 93 `QF_LRA` files we lose with the same Dutertre–de Moura simplex we ship, so the gap is not the algorithm's name. Census of **all 93** over four cause channels (the give-up string is one of them and loses the largest bucket alone, [ADR-2045]): **40 `rc=134` allocation aborts, 36 `budget/other`, 7 `incomplete`, 5 `bound-no-decline`, 5 `not-applicable`** — and the typed decline name **types nothing here**, all 36 budget rows carrying `Budget::Other`, which is [ADR-2102]'s empty `decline_names` seen from the producer side. Shape census over the 93 against the **107 decided as a control**: atoms separate the halves **1,351×** (median 9,462 vs 7) while **coefficient size does not** — max numeral 5 digits median, 10 max, **0 of 200 rows over 18 digits on either half** — so `i128` is nowhere near its 38 digits and every arithmetic decline on this population is pivot GROWTH, never the file's own numbers; that kills the "big coefficients" reading before a trace is read. Three design-difference claims with `file:line` on both sides. **(1) The tableau.** Ours was `Vec<Vec<Rational>>`, a dense `m × (nvars+m)`; **none of z3, cvc5, `OpenSMT` or `SMTInterpol` stores a dense tableau** (`static_matrix.h:88-89`, `matrix.h:56-196`, `Tableau.h:62,118-119`, `TableauxRow.java:22-34`) and all four thread the COLUMNS too. FIXED: `row_val` sparse aligned with the `row_nz` index that already existed, plus a `col_rows` transpose — without which two `0..m` column scans become `O(m log nnz)`, a regression dressed as a fix. **(2) Theory propagation is not weak, it is absent**: over the 23 of 93 rows that reach the online engine, a median **19** propagations against **836,531** decisions — **24,509 decisions and 3,352,038 atom visits per propagation** — because `lra_online.rs:836` rescans every propagatable atom on every call, while z3 analyses only `touched_rows` (`lar_solver.h:284-302`), skips rows over `max_row_length_for_bound_propagation = 300` (`lp_settings.h:238`), and **pre-axiomatises the bound ORDERING as SAT clauses** (`theory_lra.cpp:2841,2963`) so the unate half never calls the theory. We have no bound-axiom generation at all. NOT FIXED, sized and named. **(3) The equality hypothesis is REFUTED on the reference side**: 66 of 93 rows are ≥50 % equalities and we do no Gaussian elimination — but neither does z3 (no `solve_eqs` in `asserted_formulas::reduce`), and cvc5's is capped at `ppAssertMaxSubSize = 2`. The failing allocation is **median 1.33 MB** (max 10.3), i.e. the STRAW at an 8 GiB ceiling and not the load, which stops the next lane sizing a fix from the panic message. The shipped lever is the CONSEQUENCE, not the storage: `for_budget` reserves `MAX_TABLEAU_CELLS × 32 B` = **128 MiB, 20 % of the 640 MiB online budget**, for a structure now costing ~1.4 MB, and that reserve decides which queries the engine ADMITS; `TableauReserve` ships **`Dense`** because ADR-2045's budget raise got **0 newly decided and five NEW aborts** and ADR-2055's cap turned **18 clean exits into `rc=134`**.
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
touch `m_arith_mode`). cvc5 1.3.4 ran beside them. Results:
`bench-results/lra-trace-20260915/ref-*.tsv`, one full `-st` / `--stats`
capture per file kept whole rather than grepped for one token.

## 4. The three design differences, with `file:line` on both sides

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

**Ours.** `LraTheory::propagate_bounds` (`crates/axeyum-solver/src/lra_online.rs:836`)
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
