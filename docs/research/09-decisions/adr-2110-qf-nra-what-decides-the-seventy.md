# ADR-2110: QF_NRA — 45 of the 70 are a CAD problem, and 22 are not

Status: proposed
Index-summary: The 83 QF_NRA files the board leaves undecided, censused by typed
route trail and traced against z3's CAD and linearization engines separately.
z3's linearization arm — the one shaped like `nra.rs` — decides 29 of 83; its
CAD arm decides 45 more, 44 of them in under a second. The exact decider now
records WHICH guard stopped it instead of one `not-applicable` for all 78. Lane NIA-TRACE measured nlsat conflicting on 67 of the 76 QF_NIA files z3 decides and we do not, so the nlsat/CAD route both lanes point at covers both nonlinear divisions -- 45 of 83 here, 67 of 76 there, disjoint populations and two different measurements that must not be added.
Index-status: proposed
Date: 2026-09-15

**Lane:** `nra-trace`

**What `proposed` refers to.** Decision 1 below -- the `CadDecline` attribution
-- is LANDED and unconditional: it is the default behaviour of every traced run
from this branch, with its own tests, mutation suite and gates. Decision 2's
lever ships **OFF** (`AXEYUM_NRA_CAD=default`, byte-identical to the previous
engine), and this ADR carries `proposed` for that reason: no default was moved.
The measurements -- the census, the reference trace and the two design claims --
are measurements, not proposals, and stand on the artifacts named at the end.

## Context

`QF_NRA` is the second-largest single division gap. The 2026-09-15 board
(`bench-results/board-ab-20260915/QF_NRA.tsv`) records **117 of 200**; z3 4.13.3
decides **187** of the same 200
(`bench-results/session-20260911-smtlib/head-to-head/QF_NRA.tsv`). 70 behind.

### What already existed, and why the brief was wrong about it

This lane's brief said "no census has ever been run on this division". One had:
[`docs/research/12-performance/qf-nra-loss-attribution-2026-09-09.md`](../12-performance/qf-nra-loss-attribution-2026-09-09.md)
swept 75 QF_NRA **parity-loss** files six days earlier, produced a step-1 split,
a per-atom shape table and two A/Bs, and two routes in the tree today
(`nra_fbbt`'s derived bounds, `SkeletonSolvePolicy`) came out of it. Checking
that before starting is the standing rule and it changed what this lane did: the
2026-09-09 note's lazy-SMT internal split is not re-measured here, and its
findings are quoted rather than rediscovered.

This census is a different population on a different instrument:

| | 2026-09-09 | this ADR |
|---|---|---|
| population | 75 parity losses (2026-09-08 cut) | 83 undecided on the 2026-09-15 board |
| route trail | blind on 21 of 75 | `bound_by` populated on 82 of 83 |
| schema | 1 | 3 |

## The census

83 files, `smtcomp_cli --trace`, 24 s wall / 8 GiB `ulimit -v`, two shards on s5
cores `1,9` and `3,11`, every run through `scripts/ledger-run-one.sh`. 83 of 83
produced an outcome-ledger row: `bench-results/ledger/nra-trace-census-20260915.tsv`.

Buckets are keyed on the decline of the route that **held the budget**, with
restating wrappers unwrapped.

| files | bucket | median vars | median degree |
|------:|--------|------------:|--------------:|
| **26** | `nra/incomplete` — abstraction: refinement reached a fixpoint | 3 | 8 |
| **22** | `nra/budget` — N cross-products project to M atoms, past the 1,024 capacity | 450 | 2 |
| **11** | `nra/budget` — lra: Fourier–Motzkin stopped on the deadline | 3 | 4 |
| **5** | `nra/budget` — lra: Fourier–Motzkin hit `MAX_FM_CONSTRAINTS` | 4 | 4 |
| 14 | ten smaller buckets | | |

`bound_by` is `nra` on **71 of 83**. The largest bucket is **not** the one the
2026-09-09 sweep named: that sweep's biggest class was the atom-capacity refusal
(14 of 75), which is bucket 2 here. Bucket 1 is 23 `meti-tarski` files plus
three others — **3 variables, degree 3–20, one assertion** — and it is the
canonical CAD shape.

`nra-real-root/not-applicable` appears somewhere in the trail of **78 of 83**.

### Two instruments lied before they were right, and both are recorded

**The bucket key.** The first version read the LAST non-front-door decline. On a
quantifier-free query the ladder keeps walking past the real branch, and the
quantifier rungs quote the `nra` reason verbatim, so the two largest QF_NRA
buckets came out as `q:skolem-qf` (18) and `q:nat-induction` (17) — routes that
have nothing to do with this division. This is the 2026-09-09 sweep's own
hazard 3 in a new place, one rung down.

**The division column.** `shape-features.py` is a parser, not a grep, and still
got real division wrong twice:

1. `(/ 9062500 7)` is a `meti-tarski` coefficient literal → "40 of 83 have
   division".
2. SMT-LIB has no negative numeral, so `-471/100` is `(/ (- 471) 100)` — a LIST
   numerator. Testing `isinstance(a, str) and is_numeral(a)` on the operands →
   "31 of 83 have symbolic division".
3. Asking whether the **denominator** is a ground constant — the question
   `nra::eliminate_real_div` actually turns on — gives **0 of 83, and 0 of all
   200**.

A whole "division elimination is the bucket" lane would have come out of
reading 1 or 2. `bench-results/nra-trace-20260915/controls/` keeps a satisfiable
file that does divide by a variable, so a column that is zero across the
population is still falsifiable.

## The reference trace — the decision this ADR exists to record

Each of the 83 through z3 **three ways**, same envelope, same pinned cores, plus
cvc5 1.3.4:

| arm | what it is | sat | unsat | unknown | none | **decided** |
|---|---|---:|---:|---:|---:|---:|
| `z3-default` | the logic's own tactic | 39 | 31 | 0 | 13 | **70** |
| `z3-nlsat` | `(check-sat-using qfnra-nlsat)` — forced CAD | 37 | 29 | 0 | 17 | **66** |
| `z3-lin` | `(check-sat-using smt)`, `smt.arith.solver=6`, `smt.arith.nl.nra=false` | 14 | 15 | 38 | 16 | **29** |
| `cvc5` | default | 37 | 33 | 0 | 13 | **70** |

`z3-default` decides 70, and **117 + 70 = 187** is exactly the head-to-head's z3
column. The run reproduces the number it is being compared against, which is the
control on the whole table.

`smt.arith.nl.nra=false` is the load-bearing flag: z3's own option help says
`arith.nl.nra` "call nra_solver when incremental linearization does not produce
a lemma", so leaving it on lets the linearization arm fall back into the CAD
engine the arm exists to exclude.

**`z3-lin` is the arm shaped like ours** — abstract each monomial to a fresh
variable, drive an LP over the abstraction, refute with tangent / order /
monotonicity / Gröbner lemmas. It decides **29 of 83**.

| | files |
|---|---:|
| decided by the CAD engine and **not** by linearization | **45** |
| decided by linearization too | 29 |
| decided by neither z3 arm | 9 |

On the 45 only the CAD engine decides, it is not working hard: **median 108 ms,
44 of 45 under one second**, max 12.3 s.

Per bucket:

| bucket | n | z3 | nlsat | lin | cvc5 |
|---|---:|---:|---:|---:|---:|
| refinement fixpoint (3 vars, degree 8) | 26 | 26 | **26** | **5** | 25 |
| atom capacity (LassoRanker, ~450 vars, degree 2) | 22 | 14 | 10 | **14** | 14 |
| Fourier–Motzkin deadline | 11 | 11 | 11 | 3 | 11 |
| Fourier–Motzkin `MAX_FM_CONSTRAINTS` | 5 | 5 | 5 | 1 | 5 |

**The two largest buckets are opposite problems.** Bucket 1 is 26/26 for the CAD
engine and 5/26 for linearization. Bucket 2 is the other way round — 14 for
linearization, 10 for the CAD engine. Treating "QF_NRA" as one gap and picking
one fix for it is how a lane spends a week on the wrong half.

### The same route covers QF_NIA, and that is a second lane's number

Lane `NIA-TRACE` ran the equivalent trace on the other nonlinear division and
measured **nlsat conflicting on 67 of the 76 QF_NIA files z3 decides and we do
not**. Put beside this ADR's **45 of 83** on QF_NRA, the two say the same thing
about the same missing engine:

| division | files z3 decides and we do not | attributable to the CAD/nlsat engine |
|---|---:|---:|
| QF_NRA (this ADR) | 70 | **45** decided by the CAD arm and not by linearization |
| QF_NIA (`NIA-TRACE`) | 76 | **67** on which nlsat conflicted |

The two numbers are not the same measurement and must not be added as if they
were: this ADR's 45 is "the CAD arm decides it and the linearization arm does
not", while `NIA-TRACE`'s 67 is "nlsat recorded conflicts on it", which counts
files nlsat worked on rather than files only nlsat decides. Read them as two
independent lanes arriving at the same engine from opposite divisions, not as
one 112-file total.

The consequence for planning is the one that matters: a model-constructing
nlsat/CAD route is **not** a QF_NRA-only investment. It is the single largest
named capability gap across both nonlinear divisions, and the two lanes'
populations are disjoint.

## Decision

1. **The `nra-real-root` rung reports which guard stopped it.**
   `nra_real_root::CadDecline` is a 12-cause taxonomy with an exhaustive
   `name()`, recorded through `note`, which is the identity on `Some` and
   records on `None` — so it cannot change a verdict. The rung keeps the
   payload-free `not-applicable` when the decider never ran.

   It answered immediately on bucket 1's example: `atan-vega-3-chunk-0242`
   as shipped declines `non-conjunctive` (one `or` ends the exact decider before
   any projection), and its first conjunct alone declines `projection`. Neither
   was visible before; both printed `not-applicable`.

2. **`AXEYUM_NRA_CAD` is a dated lever on the decomposition's cell cap**,
   registered as `CAD_DEFAULT` in `config_registry`. It ships `default`, which
   is byte-identical to the pre-change engine (`CadPolicy::DEFAULT.cell_cap` IS
   `MAX_CAD_CELLS`), so the A/B is one binary and one env var.

3. **We do not claim the cell cap is the constraint.** The attribution says it
   is not: the causes recorded on the largest bucket are `non-conjunctive` and
   `projection`. The lever exists so that claim is measured rather than argued,
   and the A/B below is what it measured.

## The design difference, twice, with `file:line` on both sides

**Claim 1 — enumerative CAD versus model-based single-cell projection.**

Ours enumerates the arrangement. `nra_real_root.rs:3754` `visit_open_cells` (and
`visit_rational_cells` / `visit_all_cells` beside it) recurses over the
projection, visiting **every open cell's rational interior sample**, charging a
global budget initialised at `nra_real_root.rs:2968` `MAX_CAD_CELLS = 256`; the
`Unsat` at `decide_nonstrict_cad_nvar`'s tail is earned only by "every cell's
sample failed", so a verdict costs the whole arrangement.

z3 never enumerates one. `nlsat_solver.cpp:1848` `search()` assigns arithmetic
variables one at a time (`new_stage()` at `:1803`, `select_witness()` at
`:1816`), and only on a conflict does `nlsat_explain.cpp:988` `project(ps,
max_x)` run — which builds **one cell around the current sample**
(`nlsat_explain.cpp:944` `levelwise_single_cell`, reading `sample()`; the
sample-cell projection of Li & Xia, named in that function's own comment) and
emits a clause. cvc5 does the same thing with coverings:
`coverings_solver.cpp:117` `d_CAC.getUnsatCover()`, built by
`coverings/cdcac.cpp:555` `getUnsatCoverImpl` around the current partial
assignment.

So our cost is exponential in the variable count **before we can say anything**,
and theirs is per conflict. That is why 26 files with three variables and one
assertion are `unknown` for us and 108 ms for them.

**Claim 2 — `i128` coefficients versus arbitrary precision.**

Ours clears polynomials to `i128` integer coefficients and declines above
`nra_real_root.rs:137` `MAX_ABS_COEFF = 1 << 40`; `to_single_var_integer_poly`
returning `None` is now attributed as `CadDecline::CoefficientRange`, and
`project_strict` failing as `CadDecline::Projection` — which is the cause
recorded on bucket 1's reduced example. Projection squares coefficient
magnitudes at every elimination level, so a benchmark whose *source* literals
already reach 10^24 (13 of the 83 exceed `1 << 40` before any projection) cannot
survive one level.

z3's polynomial manager is arbitrary-precision by construction:
`src/math/polynomial/polynomial.h:118-119` types `numeral_manager` as
`unsynch_mpz_manager` and `numeral` as its `numeral` — GMP integers. There is no
coefficient cap to decline at.

These are the two capability statements. Neither is a tuning distance, and
neither is addressed by the lever this ADR ships.

## The A/B

Interleaved per file, one binary, two env values, both arms back to back on the
same pinned core, order alternating with the file index.

**QF_NRA, 200 files, s5 cores `1,9` + `3,11`, 24 s / 8 GiB:**

| | |
|---|---:|
| rows | 200 |
| A (`default`) | **117** |
| B (`wide`) | **119** |
| net | **+2** |
| gains / losses / `sat`↔`unsat` flips | **2 / 0 / 0** |
| rows where an arm produced no verdict token | 1 (both arms) |
| vs declared `:status` | **0 disagreements over 234 comparable verdicts** |
| wall clock | A 1,240 s, B 1,213 s |

Arm A scores **117**, which is the board's own number for this commit — the
control on the A/B is that its baseline arm reproduces the board.

Both gains are in the census population and both are declared `sat`:
`meti-tarski/exp/problem/10/2/exp-problem-10-2-chunk-0017` (24.2 s → 0.2 s) and
`meti-tarski/exp/problem/10/3/exp-problem-10-3-chunk-0139`.

**QF_NIA, 200 files** — the nonlinear code is shared, so the division that did
not motivate the lever is where a regression would show:

| | |
|---|---:|
| rows | 200 |
| A (`default`) | **83** |
| B (`wide`) | **83** |
| net | **+0** |
| gains / losses / flips | 1 / 1 / **0** |
| vs declared `:status` | **0 disagreements over 166 comparable verdicts** |

Arm A's 83 sits against the board's own 85 for this division, two rows apart at
the budget boundary.

**Every mover re-run 3x per arm**, one pinned core, arms alternating within the
three passes (`bench-results/route-ownership-20260915/recheck-movers.sh`, with
the two arms as wrapper scripts over ONE binary so its same-binary guard still
means something):

| file | A | B | class |
|---|---|---|---|
| `exp-problem-10-2-chunk-0017` | `unknown` x3 | `sat` x3 | **STABLE-GAIN** |
| `exp-problem-10-3-chunk-0139` | `unknown` x3 | `sat` x3 | **STABLE-GAIN** |
| `From_T2__apchild-live...terminationG_0` | `sat` x3 | `sat` x3 | BOTH-DECIDE |
| `Stroeder_15__NonTermination2...edge_closing_0` | `sat`/`sat`/`unknown` | `sat`/`sat`/`unknown` | **UNSTABLE** |

So **2 stable gains, 0 stable losses, 0 flips across both divisions**. The
QF_NIA pair are both ambient: one decides in both arms and the other has an
IDENTICAL three-pass pattern in both arms, which is a budget-boundary file and
not an effect. Reporting the raw `1 gain / 1 loss` as the result would have
been wrong in both directions.

**The default stays `default`.** +2 on one division is not a basis for changing
a bound every real query passes through, and the attribution says the cap is not
what stops the largest bucket. The lever is now one env var away for the next
lane.

## What this does not say

- It does not say the 45 CAD-shaped files become wins. It says an engine of a
  different **kind** decides them in 108 ms median, and names the two structural
  differences with line numbers on both sides.
- It does not size the work to build a model-constructing CAD. That is the next
  question, not a claim here.
- The 22-file atom-capacity bucket is **not** a CAD problem — z3's linearization
  arm decides 14 of the 14 z3 decides at all, and its CAD arm decides fewer.
  Whatever is done for bucket 1 should not be sold as a fix for bucket 2.
- It does not re-measure the 2026-09-09 note's lazy-SMT internal split; that
  note is still the source for it.

## Consequences

- One `not-applicable` for 78 of 83 files becomes 12 distinguishable causes.
- The next NRA lane starts from "45 files, CAD-shaped, 108 ms median for an
  engine that builds one cell per conflict", not from "we are 70 behind".
- `config_registry` gains a dated entry (103 dated of 491).

## Evidence

- `bench-results/nra-trace-20260915/` — census, shapes, reference trace, A/B,
  and the runners for each.
- `bench-results/ledger/nra-trace-census-20260915.tsv` — 83 ledger rows.
- `scripts/tests/mutation_controls.py` suite `nra-cad-attribution`: baseline
  green at 42 tests; each of three guard deletions killed **exactly one** named
  test, a different one each time.
