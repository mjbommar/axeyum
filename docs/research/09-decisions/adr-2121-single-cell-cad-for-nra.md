# ADR-2121: Single-cell CAD for QF_NRA — the route exists, it is checked, and it ships OFF

Status: proposed
Index-summary: ADR-2110 measured 45 of 83 undecided QF_NRA files as decided by
z3's CAD arm and not by its linearization arm, and named the design difference:
we enumerate the arrangement, z3 and cvc5 build one cell per conflict. This
builds the second shape as a bounded slice. The lever `AXEYUM_NRA_CAD=single-cell`
is measured at +6 on QF_NRA (6 STABLE-GAIN, 0 STABLE-LOSS, 0 flips on a 3x
recheck, of which +4 is the route deciding and 2 are files it declines), +0 on
QF_NIA and 0 movement on the QF_LRA control, with its baseline arm reproducing
the board's own 117; an `unsat` is emitted only after an independent cell-covering
checker accepts it, and the honest label on that checker is CHECKED, not proved,
because its delineability test is sampling. The sizing correction matters more
than the +6: this lane's own first ceiling of 24 was wrong, and the corrected
conjunctive ceiling is 12 of 45.
Index-status: proposed
Date: 2026-09-15

**Lane:** `nra-single-cell`

**What `proposed` refers to.** The route, its certificate checker, its fuzz seed
class and the attribution work are LANDED. The lever ships **OFF**
(`AXEYUM_NRA_CAD=default`), and this ADR carries `proposed` for that reason: no
default was moved. The measurements are measurements.

## Context

[ADR-2110](adr-2110-qf-nra-what-decides-the-seventy.md) split the QF_NRA gap in
two and named the design difference with `file:line` on both sides:

- ours enumerates the arrangement (`nra_real_root.rs:3754` `visit_open_cells`,
  global cap `MAX_CAD_CELLS = 256` at `:2968`, an `Unsat` earned only by visiting
  every cell);
- z3 builds one cell per conflict, reading the current sample;
- **45 of the 83 undecided files are decided by the CAD arm and not by
  linearization**, 44 of them under a second, median 108 ms.

Its closing sentence was "the model-constructing nlsat/CAD route is the
recommendation, not this lane's build". This is that build, as a bounded slice.

## The sizing, and the correction this lane had to make to its own

Exit criterion 1 was committed before any code
(`bench-results/nra-single-cell-20260915/sizing.py`, commit `4447b5a14`). It
joins ADR-2110's engine split against its shape table and refuses to report
unless it reconstructs exactly 45 CAD-only files, so the ceiling is a statement
about the same population.

| | of the 45 |
|---|---:|
| inside the BOUND ceiling — ≤ 4 variables, total degree ≤ 8, coefficients ≤ `1<<40` | **24** |
| excluded by the `1<<40` coefficient clearing alone | 9 |
| excluded for degree | 16 (8 degree-only, 8 degree + coefficient) |
| excluded for variable count | 4 |

**That 24 was wrong as a shape ceiling, and the way it was wrong is worth more
than the number.** The sizing read `has_top_or` from ADR-2110's shape table,
which tests the **outermost node of each assertion**. `meti-tarski` files are a
single assertion built from one enormous `let`-bound `and` tree, so an `or` six
levels inside does not move that column. ADR-2110's own decision 1 says exactly
this about `atan-vega-3-chunk-0242` — "one `or` ends the exact decider before any
projection" — and this lane read past it.

`conjunctivity.py` asks the right question: expand every `let`, walk the whole
term, and look for any non-conjunctive connective. **12 of the 24 are
conjunctive.** The corrected shape ceiling is **12 of 45**, and the difference is
entirely disjunction inside a single assertion.

The general rule: a column computed at the top of a term is not a statement about
the term. The first ceiling was not a guess that came out slightly high — it was
the wrong question answered exactly.

## The design difference, with `file:line` on three sides

ADR-2110 gave the search-loop citations. This adds the **projection operator**,
which is the part that had to be built.

**Ours.** `crates/axeyum-solver/src/nra_single_cell.rs` `project_level`. For each
polynomial of positive degree in the eliminated variable it adds **every**
coefficient in that variable, the discriminant `Res(p, ∂p/∂e)`, and every
pairwise resultant; and it checks **non-nullification at the sample** first,
declining (`CadDecline::NullifiedResidual`) when a polynomial vanishes identically
there.

**z3.** The live single-cell projection is `references/z3/src/nlsat/levelwise.cpp`
— a separate file from `nlsat_explain.cpp`, which only wraps it:

| `file:line` | what |
|---|---|
| `levelwise.cpp:1526` | `levelwise::single_cell` — the entry |
| `levelwise.cpp:437` | `add_projection_for_poly` — leading coefficient, discriminant, non-null witness coefficient |
| `levelwise.cpp:1282` / `:1259` | `add_sector_projections` / `add_section_projections` |
| `levelwise.cpp:1162` / `:1185` | `add_relation_resultants` / `add_adjacent_root_resultants` |
| **`levelwise.cpp:268`** | **`handle_nullified_poly`** — adds all coefficients, then walks partial derivatives until a non-vanishing one is found |
| `levelwise.cpp:1381` | `collect_non_null_witnesses` |
| `nlsat_explain.cpp:623` / `:717` / `:738` | `add_lcs` / `psc_discriminant` / `psc_resultant` — the fallback operator |
| `nlsat_explain.cpp:50` | `m_add_all_coeffs` — the restart flag that projects EVERY coefficient |
| `nlsat_explain.cpp:340` | `elim_vanishing` |

**cvc5.** The characterization is inlined in the coverings solver:

| `file:line` | what |
|---|---|
| `coverings/cdcac.cpp:358` | `CDCAC::constructCharacterization` — discriminant, pairwise resultants, required coefficients, boundary resultants |
| `coverings/cdcac.cpp:444` | `CDCAC::intervalFromCharacterization` |
| `coverings/cdcac.cpp:319` / `:226` / `:253` | `requiredCoefficients` and its McCallum / Lazard variants |
| `coverings/lazard_evaluation.cpp:590` / `:700` | `LazardEvaluation::add` / `reducePolynomial` — the modified lifting that makes the projection sound when a polynomial IS nullified |
| `coverings/projections.cpp:77` | `projectionMcCallum` — **dead code**: its only caller is a unit test. Do not cite it as the live operator. |

**The one structural fact to take from this table.** All three implementations
have a distinguished answer to the *same* problem — what to do when a polynomial
is nullified at the sample, where McCallum's theorem stops applying. z3 adds all
the coefficients and then walks derivatives; cvc5 offers Lazard evaluation; this
route adds all the coefficients and otherwise **declines**. Declining is the
weakest of the three and the only one this lane could ship with a checker behind
it. The next capability step on this route is named, not vague: it is cvc5's
`lazard_evaluation.cpp`.

## What was built

`crates/axeyum-solver/src/nra_single_cell.rs` — CDCAC. At each level the
boundary set starts as that level's own atoms and grows **only** with the
projection of polynomials a real conflict one level down actually used. A full
scan that adds nothing is the fixpoint, and that fixpoint is exactly the
condition a `Deeper` cell reason needs to generalise from its witness to its whole
cell. Variable order is ascending `SymbolId`, fixed, and every sample comes from
`nra_real_root::cell_samples` — determinism is a public promise and this route
makes no random choice.

`crates/axeyum-solver/src/nra_cell_cert.rs` — the certificate and its checker,
landed **before** the route (commit `c03bf39f7`) so the format was fixed by what
can be checked. It shares no code with the producer: Sturm bisection over
`axeyum_ir::poly` rather than `nra_real_root`'s grid isolator, and every
polynomial re-substituted from the **multivariate** form the certificate carries,
so the producer cannot lie about a substitution it performed.

### What the checker establishes, and what it only samples

Exactly: the sample shape; that every atom of a level is in that level's boundary
set; that the cell list IS the arrangement of that set (`m` recomputed here); that
an atom-closed cell's polynomial has **no root strictly inside** and the wrong
sign at the cell's representative — a theorem about the whole cell; and that a
`Deeper` witness belongs to its cell and the sub-sample extends the parent's.

By **sampling**: delineability. At three further interior points of a `Deeper`
cell, each boundary polynomial of the sub-covering must keep the same
distinct-real-root count.

**So an `unsat` from this route is CHECKED, not PROVED, and the module doc says so
in the place a reader would quote it.** This matters for how the result may be
described: it is not a machine-checkable proof of unsatisfiability in the sense
the Lean-parity metric uses. What the sampling does catch is the failure mode that
actually occurs — a projection that omits a polynomial or is skipped makes the
cell too wide, and a too-wide cell crosses a root-count change.

One asymmetry worth stating: on a **point** cell the delineability probe is
skipped, because a single point needs no generalisation. The checker decides
which case applies from the arrangement it recomputed, not from the certificate,
so a producer cannot choose the cheaper branch. `CellCheckStats` counts point
cells apart so a test can tell "the probe did not need to run" from "the probe did
not run".

## Two bugs this lane found in its own work, both on the checker side

Recorded because both surfaced as `certificate-rejected` — a dropped verdict —
rather than as a wrong answer, which is the gate working:

1. `merge_roots` discarded the refinement `compare_iso` performed (it refined
   clones), so the merged root list kept whatever bracket each root was first
   isolated in. For a linear polynomial that is the whole Cauchy interval, and
   every later step needing a point between two roots had nowhere to put one.
2. The route hand-rolled an open-cell sampler instead of reusing
   `nra_real_root::cell_samples`, whose own doc comment records a wrong-`Unsat`
   bug from exactly that.

And one on the route side, found by the capability probe rather than by a test:
the route refused every **rational point cell** that satisfied its level's atoms,
recording `indeterminate-sign`. That was its measured cause of death on every
conjunctive `meti-tarski` file in the in-bounds set. A rational point cell is
perfectly descendable; the certificate now distinguishes the two cases.

## The measurements

### Capability, on the population ADR-2110 named

The 24 in-bounds files through the route with `--trace`
(`cause-inbounds-24.tsv`). The route **decides 2** of them outright, and the
attribution names why the rest stop:

| cause | files |
|---|---:|
| `non-conjunctive` | 12 |
| `algebraic-witness` | 6 |
| `projection` | 2 |
| `root-ordering` | 1 |
| `certificate-rejected` | 1 |
| **decided** | **2** |

`algebraic-witness` is a cause this lane added and split out of
`algebraic-coarsening`, because the two say different things about what would fix
them: a bracket that could not be narrowed, versus a **representable model at an
irrational point that this slice declines to represent**. It is the route's
dominant blocker inside its own declared shape, and it is the cause a
`Value::RealAlgebraic` sample would remove.

### The A/B

Interleaved per file, one binary (`sha256` in `ab-binary-sha256.txt`), two env
values, both arms back to back on the same pinned core, order alternating with
the file index. Four shards on s5 cores 1, 9, 3, 11; 24 s wall, 8 GiB `ulimit -v`.

**QF_NRA, 200 files** — the target division:

| | |
|---|---:|
| rows | 200 |
| A (`default`) | **117** |
| B (`single-cell`) | **123** |
| net | **+6** |
| gains / losses / `sat`↔`unsat` flips | **6 / 0 / 0** |
| rows where an arm produced no verdict token | 0 |
| vs declared `:status` | **0 disagreements over 238 comparable verdicts** |
| wall clock | A 1,259 s, B **1,172 s** |

Arm A scores **117**, which is the 2026-09-15 board's own number for this
division — the control on the A/B is that its baseline arm reproduces the board.
Arm B is also the *faster* arm by 87 s, so the route is not buying decisions with
time.

### Four of the six gains are the route. Two are not, and saying so is the point.

Every mover was re-run with `--trace` and attributed to the rung that answered
(`cause-movers-8.tsv`), and joined against the four nested populations
(`mover-population.py`, which refuses to report unless they are 83 / 45 / 24 / 12
and nested):

| file | A → B | in 83 / 45 / 24 / 12 | who decided it |
|---|---|:---:|---|
| `sqrt/1mcosq/8/…-chunk-0562` | `unknown` → `sat` | 1 / 0 / 0 / 0 | **the route** |
| `sin/cos/sin-cos-346-b-chunk-0147` | `unknown` → `unsat` | 1 / 1 / 1 / 1 | **the route** |
| `sin/problem/7/sin-problem-7-chunk-0124` | `unknown` → `sat` | 1 / 1 / 1 / 1 | **the route** |
| `exp/problem/10/3/weak/…-chunk-0081` | `unknown` → `unsat` | 1 / 0 / 0 / 0 | **the route** |
| `sin/problem/7/weak/…-chunk-0131` | `unknown` → `sat` | 1 / 1 / 1 / 0 | a later rung — the route declined `non-conjunctive` |
| `atan/vega/3/weak/…-chunk-0243` | `unknown` → `sat` | 1 / 1 / 1 / 0 | a later rung — the route declined `non-conjunctive` |

**So the route's own attributable effect on QF_NRA is +4, not +6.** The other two
are budget-boundary files that moved because the arm-B binary spends a little
time declining before the ladder continues; the three-pass recheck below is what
decides whether they are effects at all. Reporting the raw +6 as the route's
result would have overstated it by two.

Two things this table settles that no static count could:

- **Two of the four route-decided files are outside ADR-2110's 45** — z3's
  linearization arm decides them too, so they were never part of the CAD-shaped
  population. The route reaches past the population that motivated it, and the
  ceiling is not a forecast in either direction.
- **`conjunctivity.py` agrees with the solver, 2 for 2.** The exact two movers it
  marked non-conjunctive are the exact two the route declined as
  `non-conjunctive`. That is the control on this lane's own sizing correction:
  the corrected 12 is a measurement of the same thing the route sees, not another
  proxy for it.

**QF_NIA, 200 files** — the nonlinear code is shared, so the division that did
not motivate the route is where a regression would show:

| | |
|---|---:|
| rows | 200 |
| A (`default`) | **81** |
| B (`single-cell`) | **81** |
| net | **+0** |
| gains / losses / flips | 1 / 1 / **0** |
| vs declared `:status` | **0 disagreements over 162 comparable verdicts** |

**Neither QF_NIA mover reached this route at all**: `--trace` shows no
`nra-real-root` attempt in either file's trail (`cause-movers-8.tsv`), so both
are budget-boundary effects and neither is attributable to the lever. The gain is
also the same file ADR-2110 classified `UNSTABLE` on its own A/B. That is the
reason the raw `1 gain / 1 loss` column must not be reported as the result.

**QF_LRA, 200 files — the CONTROL.** Nothing linear goes near this route, so a
mover here would be a finding about the harness and not about the lever:

| | |
|---|---:|
| rows | 200 |
| A (`default`) | **107** |
| B (`single-cell`) | **107** |
| gains / losses / flips | **0 / 0 / 0** |
| vs declared `:status` | **0 disagreements over 194 comparable verdicts** |

`ab-report.py` exits non-zero if the control moves, so this is a check and not a
printout. Across all three divisions: **0 `sat`↔`unsat` flips, 0 disagreements
against declared `:status` over 594 comparable verdicts, and 0 rows where either
arm failed to produce a verdict token.**

### Every mover re-run three times per arm

`bench-results/route-ownership-20260915/recheck-movers.sh`, one pinned core,
arms alternating within the three passes, the SAME binary both sides through two
wrapper scripts so the script's same-binary guard still means something. Exit
status is recorded per pass as its own column, because a `losses=0` by verdict
can sit on top of new aborts.

| file | A × 3 | B × 3 | class |
|---|---|---|---|
| `sin-problem-7-weak-chunk-0131` | `unknown` ×3 | `sat` ×3 | **STABLE-GAIN** |
| `sqrt-1mcosq-8-chunk-0562` | `unknown` ×3 | `sat` ×3 | **STABLE-GAIN** |
| `sin-cos-346-b-chunk-0147` | `unknown` ×3 | `unsat` ×3 | **STABLE-GAIN** |
| `atan-vega-3-weak-chunk-0243` | `unknown` ×3 | `sat` ×3 | **STABLE-GAIN** |
| `sin-problem-7-chunk-0124` | `unknown` ×3 | `sat` ×3 | **STABLE-GAIN** |
| `exp-problem-10-3-weak-chunk-0081` | `unknown` ×3 | `unsat` ×3 | **STABLE-GAIN** |
| `Stroeder_15__NonTermination2…edge_closing_0` | `sat`/`sat`/`unknown` | `unknown`/`sat`/`unknown` | UNSTABLE |
| `From_T2__n-21.t2__p3959_terminationG_0` | `unsat` ×3 | `unknown`/`unsat`/`unsat` | UNSTABLE |

**6 STABLE-GAIN, 0 STABLE-LOSS, 2 UNSTABLE, 0 flips, and exit status 0 on all 48
runs.** The QF_NIA "loss" the raw column showed is UNSTABLE — arm B decides it
in two of three passes — so it is not a loss, and the QF_NIA gain is the same
file ADR-2110 classified UNSTABLE on its own A/B. Both QF_NIA movers are ambient
in the recheck exactly as they are unattributable in the trace.

**The decomposition that matters, and it is not the same as the gain count.** Of
the six stable QF_NRA gains:

- **four are the route deciding** (`--trace` shows `nra-real-root` `decided`);
- **two are stable but NOT the route's verdict** —
  `sin-problem-7-weak-chunk-0131` and `atan-vega-3-weak-chunk-0243` are files the
  route DECLINES `non-conjunctive`, and their gain is a later rung reaching a
  different point in its budget because arm B spent a little time declining
  first. It reproduces 3 of 3, so it is not noise; it is also not this route's
  capability, and counting it as such would be the mistake.

So: the board number moves +6 and the route's own capability accounts for +4.

The **QF_LRA control** exists because nothing linear goes near this route: a
mover there would be a finding about the harness and not about the lever, and
`ab-report.py` exits non-zero if the control moves.

### The differential fuzz

`crates/axeyum-solver/tests/nra_differential_fuzz.rs` gains
`generate_single_cell_shape` — 2..=4 variables, total degree up to 8, all six
comparators, no division, and ~1 in 6 atoms forced to share the previous atom's
monomial support so two polynomials genuinely collide in the eliminated variable.
The general generator structurally cannot reach this: it caps a monomial at two
variable factors and divides by a variable in a quarter of its atoms.

The route is called through `single_cell_decide_for_testing` rather than by
setting `AXEYUM_NRA_CAD`, because the lever is read once per process — a fuzz that
set it would be a gate on one shell, and setting it from a test is racy and
`unsafe`, which is denied workspace-wide.

```
total=1500 decided=239 (sat=237 unsat=2) agreements=239 declined=1261
          z3_unknown_skipped=0
decline causes: nullified-residual 671, non-conjunctive 311, projection 188,
                slice-bounds 36, algebraic-witness 24, indeterminate-sign 14,
                certificate-rejected 9, root-isolation 6, root-ordering 2
```

Four assertions keep it from passing vacuously: `decided > 0`; **both**
directions exercised (a sweep that only refutes never touches the sat replay; one
that only satisfies never touches the certificate checker);
`agreements == decided - z3_unknown`; and **every `unsat` must carry a non-vacuous
record of what the CHECKER examined**, because counting `unsat` verdicts alone
cannot tell an accepted certificate from a checker that stopped looking
(`checked_cells=11` over the two refutations). Every `sat` model is replayed
against the original assertions in the fuzz as well as inside the route.

The histogram found **195 unattributed declines** (`not-attempted`) on its first
run — four `?` sites returning `None` without recording a cause, which is exactly
what ADR-2110 existed to remove. Now zero.

Also landed: `single_cell_never_refutes_a_division_by_constant_zero`, the
degenerate-argument class CLAUDE.md's hard rule requires. This route never
divides — but "never touches a partial operator" is a claim, and it is now shown
on `(/ x 0)` and on a symbolic divisor that can be zero, both satisfiable, with a
z3 control confirming the fixture tests a real property.

### Mutation

| suite | baseline | mutation | killed |
|---|---:|---|---|
| `nra-single-cell-delineability` | green, **16 tests** | `if is_nullified_at(p, elim, sample)` → `if false` | **exactly 1**: `a_nullified_projection_polynomial_declines_with_its_own_cause` |
| `nra-single-cell-certificate` | green, **15 tests** | `if at_probe != at_witness` → `if false` | **exactly 1**: `delineability_sampling_rejects_a_cell_whose_root_count_changes` |
| `nra-single-cell-certificate` | green, **15 tests** | `CellReason::Undecided => Err(..)` → `=> {}` | **exactly 1**: `an_undecided_cell_is_rejected` |
| `nra-cad-attribution` | green, **44 tests** | `single_cell: true` → `false` on the arm | **exactly 1**: `the_single_cell_arm_differs_in_exactly_the_route` |
| `nra-cad-attribution` | green, **44 tests** | drop `"single-cell"` from the arm parser | **exactly 1**: `every_arm_name_is_a_value_the_parser_accepts` |

`--check-anchors`: `suites=147 anchors=1087 stale=0`.

The last two extend ADR-2110's own suite, and they close a hole it left one level
along. That ADR guards `wide` against carrying the same cap as `default` —
"an A/B whose two arms carry the same value measures nothing and reports 0
movement, which is indistinguishable from a real null". The `single-cell` arm has
**two** ways to become vacuous and neither raises an error: the arm carrying
`single_cell: false` so the treatment IS the control, and `cad_policy` not
recognising the string the runner exports, so `AXEYUM_NRA_CAD=single-cell` falls
through to `default` and the treatment arm never runs. Both would print a clean
`+0`. The arm parser is split out of `cad_policy` for exactly this: the policy is
read once per process through a `OnceLock`, so a test that set the variable would
measure whichever test ran first.

The delineability fixture asserts the recorded **cause**, not the verdict, and
the suite comment says why: the fixture's system is unsatisfiable either way and
the route still reaches `unsat` through a refined arrangement, so a verdict
assertion would pass on the mutant. `x·y² − x` is the zero polynomial in `y` at
`x = 0`, and because both its atoms are level 1 the level-0 cell's sample IS
`x = 0` — the route reaches the nullified point by construction, not by luck.

## Decision

1. **The single-cell CAD route lands, behind `AXEYUM_NRA_CAD=single-cell`, OFF.**
   `CadPolicy::SINGLE_CELL` carries the SAME `cell_cap` as `DEFAULT`, so an A/B
   between the two arms isolates the route and not the budget, and the two levers
   in this entry do not interact. On the shipped arms the call site is one bool
   test.

2. **An `unsat` from this route is emitted only if `check_cell_refutation`
   accepts the covering.** A rejection drops the verdict and records
   `CadDecline::CertificateRejected`. A `sat` is a rational model replayed through
   the ground evaluator against the original assertions.

3. **`CadDecline` gains three causes** — `SliceBounds`, `CertificateRejected`,
   `AlgebraicWitness` — and stays exhaustive, so a new cause does not compile
   until it is named.

4. **The default stays `default`.** See below.

## Why the default does not move

The A/B result is positive (6 stable gains, 0 stable losses, 0 flips, 0
`:status` disagreements over 594 comparable verdicts, a clean control, and arm B
the faster arm on the target division). By the numbers alone it would ship ON.
It stays off anyway, for one reason that is not about the numbers: **the `unsat` side of this
route is gated by a checker whose delineability test is sampling.** Every other
`unsat` producer in this tree is gated by something exact. Making this route the
default would make a sampling check load-bearing on the default path, and that is
a decision to take deliberately with the Lazard route in hand, not as a side
effect of a +6.

The measured facts a later lane needs in order to take it:

- the lever is one env var and the arms differ in exactly one bool;
- the checker rejects rather than accepts when it cannot run a check — an
  arithmetic-exhausted probe is a rejection, and that is asserted;
- `algebraic-witness` is the dominant blocker inside the declared shape, and
  `non-conjunctive` is the dominant blocker across the in-bounds set.

## What this does not say

- It does **not** say 45 files become wins. The bound ceiling is 24, the
  conjunctive ceiling is 12, and what the route decides is what the A/B measured.
- It does **not** close ADR-2110 claim 2. Coefficients are still cleared to
  `i128` and the route declines above `1 << 40`, which excludes 9 of the 45
  before any projection.
- It does **not** produce a machine-checkable proof of unsatisfiability. See the
  checker's own docs and the paragraph above.
- It does **not** address ADR-2110's 22-file atom-capacity bucket, which that ADR
  measured as the opposite problem.
- The **held-out 200-file QF_NRA draw** (ADR-2106's pattern) was **not run**. It
  is the gate for shipping ON, and the decision here is OFF, so spending a blind
  population on a lever that is not moving would spend it for nothing.

## The next step, named

Not "improve the CAD". Three things, in order of measured blocking power:

1. **A clause loop over sign atoms**, so a disjunction inside one assertion does
   not end the route. `non-conjunctive` is 12 of the 24 in-bounds files and 311 of
   1500 fuzz instances.
2. **An algebraic sample**, so `algebraic-witness` (6 of 24) stops being a
   refusal. `Value::RealAlgebraic` already exists and `axeyum_ir::eval` already
   does algebraic field arithmetic for everything but `RealDiv`.
3. **A fraction-free multivariate determinant** (Bareiss over the `MultiPoly`
   ring, which supports the exact division it needs), so the projection is not
   capped at Sylvester dimension 6 by an exact Leibniz expansion.

   Note the attribution limit here, because it is the kind that gets quoted too
   hard: `CadDecline::Projection` covers **several** failures — the dimension cap,
   an identically-zero resultant, and a derivative overflow — and it fires on 2
   of the 24 and 188 of 1500. **Those counts are an upper bound on what the
   determinant would fix, not a measurement of it.** Splitting `Projection` the
   way `AlgebraicWitness` was split out of `AlgebraicCoarsening` is the cheap
   first step, and it should come before the determinant work, not after.

## Evidence

- `bench-results/nra-single-cell-20260915/` — sizing, the conjunctivity
  correction, the cause scan, the A/B and its report, and the runner for each.
- `scripts/tests/mutation_controls.py` suites `nra-single-cell-delineability`
  and `nra-single-cell-certificate`.
