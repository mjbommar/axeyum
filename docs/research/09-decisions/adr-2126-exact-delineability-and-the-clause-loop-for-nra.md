# ADR-2126: Exact delineability, and the clause loop — QF_NRA

Status: proposed
Index-summary: ADR-2121 withheld the single-cell CAD route's `unsat` half for one
reason: the certificate checker's delineability test was SAMPLING, which can
falsify delineability but never establish it. This replaces it. Check 6a proves
delineability over the whole cell exactly — leading coefficients, discriminants
and pairwise resultants required to be root-free on the cell by Sturm counting
against its ALGEBRAIC endpoints; the old probe survives as an independent
cross-check; and check 6c names the argument's scope boundary and REJECTS a
generalisation resting on another generalisation, which the sampling check
silently assumed and did not name. No sample is load-bearing in the checker any
more. **But the measurement corrects the premise.** Both `unsat` verdicts the
A/B gains are single-level refutations closed entirely by atom cells — `deeper=0`
— so the delineability check never runs on either, sampled or exact. ADR-2121's
blocker was over-broad: it withheld a whole half because PART of that half could
rest on a sample, and the part that appears on this corpus never did. So the +2
is real and exactly justified, it is NOT attributable to this lane's exact
check, and on 200 QF_NRA files check 6a is reached zero times — the fuzz reaches
it twice, now asserted nonzero so the exercise is a number rather than a hope.
It also splits `CadDecline::Projection`, which ADR-2121 flagged as a bundle: the
fraction-free-determinant lever is worth **1 file of 24, not 2**. And it builds
the clause loop — CDCL(T) over sign atoms with single-cell CAD as the theory —
which removes the `non-conjunctive` refusal costing 12 of those 24; its `sat` is
a replayed model, 368 decided against z3 with 0 disagreements, and its `unsat` is
withheld with the evidence that would close it named.
Index-status: proposed
Date: 2026-09-16

**Lane:** `nra-cell-exact`

## Context

[ADR-2121](adr-2121-single-cell-cad-for-nra.md) built the one-cell-per-conflict
CAD route and shipped **half** of it. Its own decision section says why, and the
reason is not about the numbers:

> The A/B on the **full** arm is positive: 6 stable gains, 0 stable losses, 0
> flips, 0 `:status` disagreements over 594 comparable verdicts, a clean control,
> and arm B the faster arm. By the numbers alone it would ship. It does not, for
> one reason that is not about the numbers: **its `unsat` is gated by a checker
> whose delineability test is sampling**, and every other `unsat` producer in
> this tree is gated by something exact.

That is the blocker this ADR removes, and it names three more with counts:
`non-conjunctive` at 12 of 24 in-bounds files, `algebraic-witness` at 6, and a
`Projection` bucket it explicitly labelled an upper bound rather than a
measurement.

## 1. Sizing, and the ceiling it halves

The instrument landed before the measurement (`2d72b5e6d`), and the measurement
before any capability code that would be sized from it (`6e4c70754`).

`CadDecline::Projection` held four failures with four different fixes: the
Sylvester dimension cap, an identically-zero resultant, a derivative overflow and
a coefficient overflow. `multi_resultant` now has a classified sibling,
`multi_resultant_classified`, returning `Result<ResultantOutcome,
ResultantDecline>`; the `Option` wrapper keeps its old contract so no existing
caller moved. `CadDecline` gains four causes, recorded **only** by
`nra_single_cell::project_level`, and `Projection` now means exactly one thing:
the enumerative decider's `project_strict`.

Re-running ADR-2121's own 24 in-bounds files under the split taxonomy:

| files | cause | what would fix it |
|---:|---|---|
| 12 | `non-conjunctive` | the clause loop |
| 6 | `algebraic-witness` | an algebraic sample |
| 2 | *decided* | nothing — the route decides these |
| 1 | `certificate-rejected` | the checker accepting what the producer built |
| 1 | `projection-arithmetic` | wider coefficient arithmetic |
| **1** | **`projection-sylvester-dim`** | **a fraction-free (Bareiss) determinant** |
| 1 | `root-ordering` | exact ordering of two critical values |
| **24** | | |

**The Bareiss-determinant lever is worth 1 file in this slice, not 2.** The other
half of ADR-2121's pair is a coefficient overflow, which a wider determinant does
not touch. Halving a ceiling is the cheapest finding in this lane and it is the
one that decides what *not* to build next.

**The other six rows are a control, not context.** This scan ran under the exact
checker, and `certificate-rejected` is still 1 and *decided* is still 2 — exactly
ADR-2121's numbers. Strengthening the checker cost zero files on the population
where it could have cost them.

`recause-report.py` refuses to report unless the row set equals the file list it
was handed, the count is 24, every row carries a recognised cause and every cause
has a recorded fix. Truncating the TSV to 19 rows gives exit 1 and two named
control failures — checked, not asserted.

## 2. The design claims, with `file:line` on three sides

ADR-2121 cited the projection *operators*. This lane's question was narrower and
different: **how does each implementation establish sign-invariance without
sampling?** The answer reframes the choice the brief posed, so it is stated
first:

> **Neither z3 nor cvc5 has a well-orientedness TEST.** Both discharge
> McCallum's side condition *constructively* — they add whatever makes it true
> and never ask whether it is. Grepping z3's `levelwise.cpp` and cvc5's whole
> `coverings/` directory for `well.orient|nullif|delineab` finds comment text and
> one cvc5 comment, and **no failure branch anywhere in either**.

That matters because it says the brief's option (b) — "McCallum with an exact
well-orientedness check" — is not a thing either reference solver does. It is a
thing a *checker* does, and neither of them has an independent checker at all.
The producer constructs; the checker tests. This lane is building the second.

**z3, `references/z3/src/nlsat/levelwise.cpp` (1560 lines).** The manoeuvre is a
repair, never a test:

| `file:line` | what |
|---|---|
| `levelwise.cpp:391` | `choose_nonzero_coeff` — scans **all** coefficients for one with nonzero sign at the sample |
| `levelwise.cpp:413` | `if (sign(coeff) == 0) continue;` — exact sign at the sample, not a probe |
| `levelwise.cpp:468` | the witness coefficient is emitted into the projection, certifying non-nullification |
| `levelwise.cpp:445-453` | the leading coefficient added separately and unconditionally; the degree is **never reduced here** |
| `levelwise.cpp:455-466` | the discriminant, via `psc_discriminant` (`:329`) |
| `levelwise.cpp:1162` / `:1185` | `add_relation_resultants` / `add_adjacent_root_resultants` |
| **`levelwise.cpp:268-317`** | **`handle_nullified_poly`** — all coefficients first (`:270-276`), then partial derivatives BFS, **stopping at the first with nonzero sign** (`:302-305`) |
| `levelwise.cpp:472-492` | the theory comment: **projective delineability** (Nalbach et al., SC² 2025, Thm 3.1) — order-invariance of the discriminant alone suffices, the leading coefficient need **not** be sign-invariant |
| `levelwise.cpp:1452-1457` | that theorem applied: the lc is dropped when the polynomial has no roots at the sample |

**z3, `nlsat_explain.cpp` (1816 lines)** takes the *opposite* approach on the
leading coefficient — it **reduces the degree**:

| `file:line` | what |
|---|---|
| `nlsat_explain.cpp:340-384` | `elim_vanishing` — peels vanishing leading coefficients |
| `:363-366` | `if (!is_zero(lc) && sign(lc)) return;` — exact sign at the sample |
| `:380-382` | otherwise `add_zero_assumption(lc)` and replace `p` by its reduct: **the vanishing is recorded as a lemma literal** |
| `:376-378` | full nullification → `m_add_all_coeffs = true; throw add_all_coeffs_restart();` — the live escape hatch |
| `:714-715` / `:735-736` | `psc_discriminant` / `psc_resultant` carry the identical remark: *"the leading coefficients do not vanish in the current model, since all polynomials in ps were pre-processed using elim_vanishing"* — the side condition is **true by construction** |
| `:685-686` | an identically-zero PSC → *"can cause unsound lemmas"* → the same restart |
| `:1004-1011` | a levelwise-failure fallback that is **dead code**: `levelwise_single_cell` unconditionally `return true;` at `:971` |

**cvc5, `coverings/cdcac.cpp` (817 lines)** and `lazard_evaluation.cpp` (907):

| `file:line` | what |
|---|---|
| `cdcac.cpp:358-442` | `constructCharacterization` — discriminants, pairwise resultants, required coefficients, boundary resultants |
| `cdcac.cpp:226-243` | `requiredCoefficientsOriginal` (the **McCallum** variant; there is no `requiredCoefficientsMcCallum`) — coefficients top-down until one is constant (`:235`) or **certified non-vanishing** (`:237`) |
| `cdcac.cpp:253-265` | `requiredCoefficientsLazard` — **leading and trailing only**, and often just the leading (`:260`) |
| `cdcac.cpp:296-311` | `LAZARDMOD` — tries to prove non-nullification through the extended rewriter, and falls back to adding the trailing coefficient when it cannot |
| `cdcac.cpp:407` / `:416` | boundary resultants gated by **exact** root-position tests, not sampling |
| `lazard_evaluation.cpp:24` | `#ifdef CVC5_USE_COCOA`, with a stub at `:850-904` |
| `lazard_evaluation.cpp:888-892` | with CoCoA absent: *"nl-cov::LazardEvaluation is disabled … Falling back to regular real root isolation"* — the Lazard *projection* option stays selectable while the *lifting* it depends on silently becomes regular lifting |
| `lazard_evaluation.cpp:645` | `CoCoA::factor(mipo)` — factorization of a ℚ-minimal polynomial **over the algebraic extension tower** |
| `lazard_evaluation.cpp:502-519` | the Lazard manoeuvre itself: `while (IsZero(hom(q))) q = q/(var - a);`, and exact divisibility by the minimal polynomial for a true algebraic value |
| `lazard_evaluation.cpp:525-528` | `CoCoA::ReducedGBasis` — a Gröbner basis under an elimination order, per polynomial per lift |
| `lazard_evaluation.cpp:743-751` | spurious-root filtering, unavoidable because the GB over-approximates |
| `arith_options.toml:571`, `:589` | the defaults: `nlCovProjection = MCCALLUM`, `nlCovLifting = REGULAR`. **Lazard is opt-in in cvc5.** |

**So Lazard was not chosen, and the reason is a shopping list.** Lazard
evaluation over our own algebraic-number arithmetic would need: minimal-polynomial
extraction from a real algebraic number; a tower of simple algebraic extensions
with arithmetic in it; **univariate factorization over each level of that tower**;
exact multivariate divisibility and division; a Gröbner basis under an
elimination order (or iterated resultants); and a spurious-root filter. cvc5 gets
all of that from GPL CoCoALib and still ships it off by default. That is a lane
of its own, and this lane's job was to remove a *sampling* check, not to acquire
an extension-field library.

**Ours**, `crates/axeyum-solver/src/nra_cell_cert.rs`
`check_delineability_exact`: McCallum's condition as an exact **test**, over the
cell rather than at the sample — which is the checker's job and not the
producer's, and is why it is a different thing from all three of the above.

## 3. What was built

### 3a. Check 6a — exact delineability

Write `t` for the cell's own variable and `v` for the sub-covering's. Each
boundary polynomial is re-substituted at the sample of the variables **before**
`t`, and `t` is deliberately left free — that is the entire difference between
this and a probe at a point. Over the open interval the cell denotes, three
conditions, each by exact root counting against the cell's own **algebraic**
endpoints (Sturm bisection, through the existing `has_root_strictly_inside`):

1. the **leading coefficient** in `v` has no root strictly inside the cell. One
   condition, two jobs: `deg_v` cannot drop (no root escapes to infinity) and no
   polynomial can be nullified;
2. the **discriminant** `Res_v(p, ∂p/∂v)` has no root strictly inside, for every
   boundary polynomial of degree ≥ 2 in `v`: no two roots of one polynomial merge;
3. every **pairwise resultant** `Res_v(p, q)` has no root strictly inside: no root
   of one boundary polynomial crosses a root of another.

Given 1 and 2, each polynomial's `deg_v` complex roots are distinct and vary
continuously over the connected cell; a real root can leave the reals only by
colliding (excluded by 2) and leave the picture only by escaping to infinity
(excluded by 1), so the distinct-real-root count is **constant**. Given 3, the
merged ordering is constant too. Hence the whole 1-D arrangement one level up is
combinatorially the same above every point of the cell, and every boundary
polynomial is sign-invariant on each 2-dimensional piece over it.

The resultants are Sylvester determinants over ℚ[t], taken by `axeyum_ir::poly`'s
exact evaluation–interpolation (`sylvester_matrix` + `sylvester_determinant`) —
the machinery already existed and had no user in this module. `None` from any
step is a **rejection**: a check that cannot run must not be reported as one that
ran.

**Our condition 1 is stronger than the minimum.** z3's `levelwise.cpp:472-492`
records exactly this: under *projective* delineability the leading coefficient
need not be sign-invariant, because roots may go to infinity where it vanishes
without appearing or disappearing inside the cell. Our check refuses that cell.
That is the conservative direction, and it is now a named, citable amount of
conservatism rather than an unexamined one.

### 3b. Check 6b — the sampling probe, demoted to a cross-check

It stays, and it is no longer load-bearing. It shares no code with 6a — root
counts by Sturm isolation at points, against 6a's leading coefficients,
discriminants and resultants — so once 6a has **accepted**, a failure there is a
disagreement between two independent implementations of one property. That is a
bug in one of them and a rejection either way, and a checker that could not
surface it would be the weaker artifact.

### 3c. Check 6c — the scope boundary, named instead of assumed

**This is the part ADR-2121 did not have, and its absence was not visible.**

6a carries an **atom** cell of the sub-covering across the whole parent cell,
because the atom is in the boundary set (check 2 enforces it) and is therefore
sign-invariant on the 2-dimensional piece. It does **not** carry a `Deeper` cell
across: that would need the level below to be delineable over a 2-dimensional
region, and 6a is 1-dimensional. A **point** cell of the sub-covering is no
better — over an open parent cell a point cell is a **curve**, not a point.

So `CellCheckFailure::NestedOpenGeneralization` rejects a generalisation resting
on another generalisation. The accepted set is now a set the argument actually
covers.

**ADR-2121's sampling check had the same gap and named none of it.** Probing
three interior points says nothing about a level two down either. The gap was
not introduced by making the check exact; it was made visible by it, and that is
the more useful half of this change. The fix, when a later lane wants it, is
stated in the module docs: the projections of the level below must be shown to
be nonvanishing on the 2-dimensional cell, which reduces to the same 1-D
machinery applied to the *extended* boundary set.

### 3d. The clause loop

`crates/axeyum-solver/src/nra_clause_loop.rs`. Tseitin-encode the assertions'
Boolean structure over one propositional variable per distinct polynomial
comparison; ask `axeyum_cnf::IncrementalSat` — this repository's own CDCL, not a
new SAT loop — for a Boolean model; turn it into a conjunction and hand it to
`decide_atoms`. A sign atom's negation is another sign atom over the same
polynomial, so the theory never sees Boolean structure at all.

The two halves are not equally justified and the lever keeps them apart:

- **`sat` rests on nothing in the Boolean layer.** The sample is replayed against
  the **original** assertions through the ground evaluator. If the encoding were
  wrong, if a blocking clause were too strong, if the SAT core answered the wrong
  formula — a replayed model is still a model, and a wrong one fails the replay
  and declines.
- **`unsat` is WITHHELD** (`CadDecline::ClauseLoopUnsatUncertified`). It would
  rest on the encoding being equisatisfiable, every blocking clause being
  implied, and the SAT core's refutation — three claims no checker in this tree
  can read. The evidence that would close it is named: a `CellRefutation` per
  blocking clause, plus a DRAT refutation of the clause set through
  `solve_with_drat_proof` and `check_drat`.

The consequence that makes the `sat` half safe without certifying the blocking
clauses: **a blocking clause can only make the loop miss a satisfying assignment,
never invent one.** On the sat-only arm an unsound one costs completeness and
cannot cost soundness. On an arm that emitted `unsat` it would cost soundness —
which is exactly why that arm does not exist.

Blocking clauses are over the atoms a covering **cited**, not the whole
assignment: a covering proves "at every point one of the cited atoms is
violated", which is a statement about those atoms alone.

`AXEYUM_NRA_CAD=clause-loop` differs from the shipped `single-cell-sat` in
**exactly** `clause_loop` — same cell cap, same `single_cell`, same `emit_unsat`
— and the arm-table test asserts all four, because the two ways this A/B goes
vacuous (the treatment carrying `clause_loop: false`, or the arms differing in a
second thing) both print a clean number. The loop is offered the query only where
the conjunctive route just recorded `non-conjunctive`, so it is strictly additive
and cannot flip a verdict.

## 4. The measurements

See `bench-results/nra-cell-exact-20260916/README.md` for every runner and list.

### The A/B — pricing the `unsat` half alone

Interleaved per file, one binary, two env values, both arms back to back on the
same pinned core with the order alternating by file index. Four shards on s5
cores 1, 9, 3, 11; 24 s wall, 8 GiB `ulimit -v`.

- **A** = `AXEYUM_NRA_CAD` set and EMPTY — `parse_cad_arm("")` is `CAD_DEFAULT`,
  which ADR-2121 moved to `SINGLE_CELL_SAT`, so arm A is **the shipped default**.
- **B** = `single-cell`, the full arm, whose `unsat` is now gated on the exact
  check.

The two differ in exactly `emit_unsat`, so this prices the withheld half on its
own.

**The reference frame, because a timing number without one is not comparable.**
`s5` was not idle: lane `lra-warm-basis-20260916` ran its own A/B throughout, on
cores 5,13 and 6,14 — **different physical core pairs**, checked in `ps` rather
than assumed, so there was no collision on 1, 9, 3 or 11. Load averaged ~6 on a
16-core box. That ambient load is why the protocol interleaves: both arms run
back to back on the same core, so it lands on both and cancels in the difference.
The wall-clock columns below are therefore comparable **between the arms** and
should not be compared against ADR-2121's, which were taken under a different
frame.

#### QF_NRA, 200 files — the target division

| | |
|---|---:|
| rows | 200 |
| A (`single-cell-sat`, the shipped default) | **121** |
| B (`single-cell`, exact-gated `unsat`) | **122** |
| net | **+1** |
| gains / losses / `sat`↔`unsat` flips | **2 / 1 / 0** |
| rows where an arm produced no verdict token | 0 |
| vs declared `:status` | **0 disagreements over 241 comparable verdicts** |
| wall clock | A 1,272 s, B **1,227 s** |

**Arm A scores 121, which is exactly the number ADR-2121 shipped this default
on.** The baseline arm reproducing the board is the control on the whole
measurement, and it holds.

**Exactly three rows of 200 differ, and the `sat` column does not move at all** —
54 on both arms. That is what "the two arms differ in exactly `emit_unsat`"
predicts, and it is measured here rather than asserted from the code:

| file | A → B |
|---|---|
| `meti-tarski/sin/cos/sin-cos-346-b-chunk-0147` | `unknown` → `unsat` |
| `meti-tarski/exp/problem/10/3/weak/…-chunk-0081` | `unknown` → `unsat` |
| `hycomp/etcs_braking_2.01.redlog_global_15` | `unsat` → `unknown` |

**The loss is not the lever, and the trace says so rather than the recheck.**
Re-run with `--trace`, **both arms decline that file at `nra-real-root` with
`non-conjunctive`** — in 46 µs and 26 µs. The route is never involved. Its
`unsat` comes from a later rung (`route: nra`) at **18.77 s against a 24 s
budget**. An 18.8-second decision inside a 24-second budget, on a file whose
execution path is identical under both arms, is a budget-boundary row.

#### QF_NIA and the QF_LRA control

QF_NIA shares the nonlinear code, so a regression there is the one a QF_NRA-only
sweep would miss. QF_LRA is the **control**: nothing linear goes anywhere near
this route, so a mover there would be a finding about the harness and not about
the lever.

| | QF_NIA | QF_LRA (control) |
|---|---:|---:|
| rows | 200 | 200 |
| A (`single-cell-sat`) | 79 | **107** |
| B (`single-cell`) | 79 | **107** |
| net | **+0** | **+0** |
| gains / losses / flips | **0 / 0 / 0** | **0 / 0 / 0** |
| rows with no verdict token | 0 | 0 |
| vs declared `:status` | 0 over 158 | 0 over 194 |

**Neither division moved a single row.** Not "netted to zero" — zero gains and
zero losses, so there is nothing to attribute or explain away. `ab-report.py`
exits non-zero if the control moves, so its silence is a check and not a
printout, and it printed `CONTROL: the linear division moved 0 rows` explicitly.

Arm A scores 107 on QF_LRA, which is again ADR-2121's own number for that
control. Two independent baseline reproductions.

**Across all three divisions: 3 movers out of 600 rows, 0 `sat`↔`unsat` flips, 0
disagreements against declared `:status` over 593 comparable verdicts, and 0 rows
where either arm failed to produce a verdict token.**



### The finding that changes what the +2 means

**Both gained `unsat` verdicts are refutations the delineability check never
touches.** Read back through `single_cell_last_check` (the
`nra_cell_check_stats` example, committed):

```
unsat  coverings=1  cells=3  atom_cells=3  deeper=0  open_deeper=0
       point_deeper=0  exact_tests=0  probes=0  max_level=0   sin-cos-346-b-chunk-0147
unsat  coverings=1  cells=3  atom_cells=3  deeper=0  open_deeper=0
       point_deeper=0  exact_tests=0  probes=0  max_level=0   exp-problem-10-3-weak-chunk-0081
```

One covering, three cells, **every one closed by an atom**, and not a single
`Deeper` cell. Delineability is the property that carries a `Deeper` cell from
its witness to its whole cell; with no `Deeper` cell there is nothing to carry,
and checks 6a, 6b and 6c all correctly do nothing. Their justification is check
4 — the atom's polynomial has no root strictly inside the cell and the wrong
sign at the representative, a theorem about the whole cell — which was exact in
ADR-2121 too.

**So ADR-2121's blocker was over-broad.** It withheld the route's entire `unsat`
half because *part* of that half could rest on a sample, and the part that
actually appears on this corpus never did. The two verdicts were available all
along; what withheld them was a decision taken at the level of the arm, which by
ADR-2121's own deliberate design happens **before** the checker runs.

Three things follow, and the third is the uncomfortable one:

1. the **+2 is real and exactly justified** — no sample is anywhere in it;
2. the **+2 is not attributable to this lane's exact check**. Reporting it as
   the payoff for exact delineability would be the same overstatement ADR-2121
   caught itself making when it separated its +6 into +4 plus two
   budget-boundary rows;
3. **the exact check has no measured exercise on this corpus at this envelope.**
   It is exercised by its unit fixtures and by the mutation that kills exactly
   one of them; on 200 QF_NRA files it is reached zero times. The fuzz now
   counts `open_deeper_cells` and `delineability_exact_tests` and **asserts both
   are nonzero**, so whether the generated population reaches 6a is a number and
   not a hope.

The risk that follows from 3 is bounded and worth stating precisely: unreached
code that **rejects** conservatively cannot produce a wrong answer. If 6a is
wrong it refuses, `check_cell_refutation` returns an error, the route records
`CertificateRejected` and declines. The exposure is capability, not soundness.

### Three-pass recheck of every mover

`recheck-movers.sh`, one pinned core, arms alternating **within** the three
passes, the same binary behind two wrapper scripts so the script's same-binary
guard still means something. Exit status recorded per pass as its own column,
because a `losses=0` by verdict can sit on top of new aborts.

| file | A × 3 | B × 3 | class |
|---|---|---|---|
| `sin-cos-346-b-chunk-0147` | `unknown` ×3 | `unsat` ×3 | **STABLE-GAIN** |
| `exp-problem-10-3-weak-chunk-0081` | `unknown` ×3 | `unsat` ×3 | **STABLE-GAIN** |
| `hycomp/etcs_braking_2.01.redlog_global_15` | `unsat` ×3 | `unsat` ×3 | **BOTH-DECIDE** |

**2 STABLE-GAIN, 0 STABLE-LOSS, 0 UNSTABLE, and exit status 0 on all 18 runs.**

**The sweep's one loss is not a loss**: arm B decides it `unsat` three times out
of three on a quiet core. The trace said so before the recheck did — same
diagnosis, two independent instruments — and that is why the trace was run first.
Shipping on the raw `2 / 1` would have understated the lever; refusing to ship on
it would have been wrong too, and only one of those two checks was needed to
separate them.

### The held-out draw

ADR-2106's pattern, adapted: `draw-heldout-qfnra.py` could not reuse
`draw-heldout.py` because **there is no `QF_NRA.txt` in the route-ownership
pinned lists** — that harness pins `QF_LIA`, `QF_LRA`, `QF_NIA` and the `AUF*`
divisions only, and pointing the original script at `QF_NRA` aborts. So the
training set is passed explicitly. Excluded: the 200-file A/B list and every
`corpus_path` any committed `bench-results/ledger/` row carries for `QF_NRA`.
Seed a source constant. Pool 11,954 of 12,154; drew 200. The exclusion is
checked by the script **and** independently here: `comm -12` over the two sorted
lists gives 0.

| | |
|---|---:|
| rows | 200 |
| A (`single-cell-sat`) | **109** |
| B (`single-cell`) | **109** |
| net | **+0** |
| gains / losses / flips | **0 / 0 / 0** |
| movers of any kind | **0** |
| rows with no verdict token | 0 |
| vs declared `:status` | 0 disagreements over 216 comparable verdicts |
| wall clock | A 1,505 s, B 1,507 s |

**Zero movers.** Not a net of zero — the arms produced the same verdict on all
200 files, so there is no row to classify.

**This is the gate passing and it is also the gain not reproducing, and both
halves have to be said.** The gate was "0 stable losses on the held-out draw",
and 0 movers clears it with nothing left to recheck. But the draw also found no
gain, and the honest reading is not that the +2 was noise: it is that the gain is
**file-specific and rare**. Two files in 200 is a 1% rate, and a fresh draw of
200 finding none of them is what a 1% rate predicts more often than not. What the
held-out draw establishes is the thing it was run to establish — that the lever
does not *cost* anything on files nobody selected it against — and it says
nothing either way about a rate this small. A draw that could have separated
them would need to be an order of magnitude larger, and that is a statement about
what this evidence supports, not an excuse for it.

### Mutation

| suite | baseline | mutation | killed |
|---|---:|---|---|
| `nra-cell-exact-delineability` | green, **19 tests** | `if degree_drops` → `if false` | **exactly 1**: `a_sampled_check_passes_a_non_delineable_cell_and_the_exact_check_refuses` |
| `nra-cell-exact-clause-loop` | green, **7 tests** | the refuted abstraction recorded as a budget | **exactly 1**: `an_unsatisfiable_combination_needing_two_branches_reaches_a_refutation` |

`--check-anchors`: `suites=151 anchors=1100 stale=0`.

**The first mutation killed TWO on its first honest run**, and the fix is worth
recording because it is a lesson about the suite and not about the code:
`vanishes_inside` is what increments `delineability_exact_tests`, so mutating the
`if` away also stopped the counter and killed the separate fixture asserting the
check *ran*. Two tests for one guard says the suite is coarse, not that the guard
is covered. Performing the test and acting on its answer are now different lines
(`let degree_drops = …; if degree_drops {`), so they have different killers.

### The fixtures, and what each one isolates

Check 6a has three conditions and each one has a fixture that **only it** can
fire, because a suite where one fixture covers three conditions cannot tell you
which of them is doing the work:

| fixture | isolates | why the other two cannot fire |
|---|---|---|
| `a_sampled_check_passes_a_non_delineable_cell_and_the_exact_check_refuses` | (1) leading coefficient | `t·y − 1` is linear in `y`, so there is no discriminant, and there is one boundary polynomial, so there is no pair |
| `delineability_rejects_a_cell_whose_root_count_changes` | (2) discriminant | `y² − x` has the constant leading coefficient 1, and there is one boundary polynomial |
| `two_roots_that_cross_are_invisible_to_sampling_and_refused_by_the_exact_check` | (3) pairwise resultant | `y − t` and `y + t` both have leading coefficient 1 and are both linear in `y` |

**Two of the three are cases the sampling check ACCEPTS, and both assert that
half**, so neither can go quietly vacuous:

- `t·y − 1` has one root in `y` for every `t ≠ 0` and none at `t = 0`. A check
  that looks at finitely many points misses a single point almost surely; the
  cell `(−1, 5)` is chosen so no probe lands on 0.
- `y − t` and `y + t` each have exactly **one** root in `y` for every `t`, so
  every per-polynomial root count is 1 *everywhere* and sampling cannot fail no
  matter where it probes. It counts roots per polynomial and has no way to
  observe their **order**, which is what swaps at `t = 0`. This is a second,
  independent blindness in the sampling check, and it is the one that motivates
  condition (3).

**ADR-2121's own delineability-failure fixture still declines, and declines for
the same reason.** `a_nullified_projection_polynomial_declines_with_its_own_cause`
builds `x·y² − x`, which is the zero polynomial in `y` at `x = 0`, and because
both its atoms are level 1 the level-0 cell's sample IS `x = 0` — the route
reaches the nullified point by construction, not by luck. It still declines
`nullified-residual`, which is the **producer's** guard in
`nra_single_cell::project_level` and fires before any certificate exists for the
checker to examine. So the answer to "does it now decline exactly or answer with
an exact certificate" is the first: it declines, at the same place, and the exact
checker is never reached. That fixture's teeth are unchanged, and its mutation
(`if is_nullified_at(…)` → `if false`) still kills exactly one test in ADR-2121's
suite.

Check 6c has `a_generalisation_that_rests_on_another_generalisation_is_refused`,
which carries its own **positive control** — an all-atom sub-covering over the
same open cell is still accepted — because the negative half alone passes on a
checker that refuses every `Deeper` cell, which would make the route answer
nothing.

### The differential fuzz

Both sweeps run through the testing hooks rather than by setting
`AXEYUM_NRA_CAD`, for ADR-2121's reason: the lever is read once per process, so
a fuzz that set it would be a gate on one shell.

**Single-cell class**, 1500 instances, unchanged shapes:

```
total=1500 decided=239 (sat=237 unsat=2) agreements=239 declined=1261
          z3_unknown_skipped=0 checked_cells=11
          open_deeper_cells=2 exact_delineability_tests=4
```

The last two counters are new and they are the answer to §4's third point: **the
fuzz does reach check 6a** — 2 open `Deeper` cells, 4 exact root-freeness tests —
where the corpus reaches it zero times. The sweep now **asserts both are
nonzero**, so a change that stopped the generated population reaching 6a fails
loudly instead of passing quietly. Note the honest size of that exercise: four
tests. It is non-vacuous and it is thin, and a lane wanting more confidence in
6a should widen the generator toward deeper refutations rather than run this one
longer.

**Clause-loop class**, 1500 instances, new:

```
total=1500 decided=368 agreements=368 declined=1132 z3_unknown_skipped=0
          disjunctive_instances=1485
decline causes: nullified-residual 607, non-conjunctive 307,
                projection-sylvester-dim 129, slice-bounds 29,
                algebraic-witness 24, indeterminate-sign 17,
                projection-resultant-zero 7, clause-loop-unsat-uncertified 6,
                root-isolation 4, root-ordering 2
```

**0 disagreements against z3 over 368 decided instances**, every one a `sat`
replayed against the original assertions, and **1,485 of 1,500 instances carry a
genuine disjunction** — asserted, because a CNF of unit clauses is a conjunction
wearing a hat and would leave this class measuring the conjunctive route a second
time. The loop decides **368** where the single-cell class decides 239, on a
strictly harder shape.

The decline histogram also shows the `Projection` split doing its job on a second
population: `projection-sylvester-dim` 129 against `projection-resultant-zero` 7.
On the generated shapes the dimension cap dominates that bucket; on the 24 corpus
files it is 1 against 0. **The two populations disagree about the ratio**, which
is exactly why the corpus number and not the fuzz number is the one quoted as the
determinant lever's ceiling.

`clause_loop_never_refutes_a_division_by_constant_zero` is the degenerate-argument
class CLAUDE.md's hard rule requires, at the fuzz level: `(/ x 0)` **inside a
disjunction** is a shape only this route reaches, and both fixtures are
satisfiable, so a route that folded division-by-zero to a convention and refuted
would fail rather than silently agree.





## 5. Decision

1. **`nra_cell_cert`'s delineability check is EXACT, and that lands
   unconditionally.** It is a checker change, it moves no lever, and its effect
   on every existing arm is that a covering the sampling check would have
   accepted may now be rejected. On the populations measured here it rejects
   nothing it did not already reject: `certificate-rejected` is 1 of 24 before
   and after, and the fuzz's two refutations are accepted by both.

2. **The sampling probe stays, as check 6b.** It shares no code with 6a, so a
   failure after 6a has accepted is a disagreement between two independent
   implementations of one property. A checker that could not surface that would
   be the weaker artifact.

3. **Check 6c is new and it REJECTS**, which makes the accepted set smaller than
   it was. That is the right direction: ADR-2121's checker accepted coverings
   whose generalisation reached past its own argument, and nothing said so.

4. **`CadDecline::Projection` is split four ways**, and `Projection` now means
   only the enumerative decider's `project_strict`.

5. **The clause loop lands behind `AXEYUM_NRA_CAD=clause-loop`, OFF.** It is
   unmeasured on any corpus; the A/B that would price it is named in §7 and this
   lane did not run it. Its `unsat` is withheld and not reachable on any arm.

6. **`CAD_DEFAULT` moves from [`CadPolicy::SINGLE_CELL_SAT`] to
   [`CadPolicy::SINGLE_CELL`]. The route's `unsat` half ships ON.**

   The gates this lane set for that, and what they returned:

   | gate | result |
   |---|---|
   | 0 stable losses, pinned draw | **MET** — 0 (the one loss is BOTH-DECIDE) |
   | 0 `sat`↔`unsat` flips | **MET** — 0 across all four sweeps |
   | 0 stable losses, held-out draw | **MET** — 0 movers of any kind |
   | control division unmoved | **MET** — QF_LRA 0 rows, and `ab-report.py` exits non-zero if it moves |
   | `:status` disagreements | **MET** — 0 over 809 comparable verdicts |

   The cell cap does not move with it, so this is a route change and not a budget
   change, and the arm-table test asserts that. `single-cell-sat` and `default`
   both stay selectable by name through explicit arms in `parse_cad_arm`, so a
   later A/B can still ask for either.

   **What this lane will not claim for it.** The measured gain is two files out
   of four hundred, the held-out draw found none, and neither of the two rests on
   the exact delineability check — they are atom-cell refutations that never
   reach it. So the honest statement of the decision is not "the exact check
   bought +2". It is: *the reason ADR-2121 withheld this half no longer exists,
   the half costs nothing on two independent draws and a control, and it is worth
   two files on the one draw where its shape appears.*

   ADR-2121's arm-table assertion — "the shipped default must not emit `unsat`" —
   is replaced rather than deleted, by the invariant that is still true and still
   load-bearing: the shipped default is a table arm that runs the route, and its
   cell cap is the shipped one. Dropping the old assertion without putting
   something in its place would have left the default unguarded.

7. **`AXEYUM_NRA_CAD=clause-loop` ships OFF.** Its A/B was not run. Building it
   and not pricing it is a deliberate stopping point, not an oversight: the
   sizing says it is worth up to 12 of 24 files, which is larger than everything
   else in this ADR put together, and a lever that size deserves its own
   measurement rather than a tail-end one.



## 6. What this does not say

- It does **not** say the checker produces a machine-checkable proof in the sense
  the Lean-parity metric uses. It produces an **exact check**: every claim is
  re-derived by this module's own root counting, and nothing is sampled. That is
  a strictly stronger label than ADR-2121's "checked", and a strictly weaker one
  than "proved".
- It does **not** close the 2-dimensional generalisation. Check 6c names that
  boundary and rejects past it; the accepted set is smaller than the set the
  route can build.
- It does **not** implement Lazard evaluation. §2 lists what that would cost.
- It does **not** close ADR-2110 claim 2: coefficients are still cleared to
  `i128` and the route declines above `1 << 40`, 9 of the 45.
- It does **not** ship the clause loop's `unsat`, and §3d names the evidence that
  would.
- **It does not claim the exact check bought the +2.** §4 measures the opposite,
  and reporting it the other way would repeat exactly the overstatement ADR-2121
  caught itself making. What the exact check buys is that the route's `unsat`
  half can be on a default path *at all* without a sample in its justification —
  for the class that appears here because it never needed one, and for every
  other class because 6a is exact.
- **It does not claim check 6a is well exercised.** On 200 QF_NRA files it is
  reached zero times; in 1,500 generated instances it is reached on 2 open
  `Deeper` cells with 4 exact tests. Four tests is non-vacuous and it is thin,
  and the assertion that now guards it will notice a regression to zero but
  cannot make four into forty. Widening the generator toward deeper refutations
  is the work, not running this one longer.
- **A gap this lane found and did not fix.** `config_registry`'s
  `GOVERNED_FILES` list contains `nra.rs` and **none** of `nra_real_root.rs`,
  `nra_single_cell.rs`, `nra_cell_cert.rs` or `nra_clause_loop.rs`. So
  `MAX_CAD_CELLS`, `MAX_MULTI_SYLVESTER_DIM`, `MAX_CELL_VARS`,
  `MAX_CELL_DEGREE`, `CERT_MAX_DEGREE`, `REFINE_DEPTH` and
  `DELINEABILITY_SAMPLES` — every bounded-cost constant on this route — are
  watched by nothing, and this lane's two new ones join them. Adding the files
  to the list would demand registry entries for every constant in them at once,
  which is a cross-lane change and not one to make unilaterally mid-lane. It is
  recorded here so the next lane on this route can size it.

## 7. The next step, named

1. **Certify the clause loop's `unsat`**: a `CellRefutation` per blocking clause
   plus a DRAT refutation of the clause set. Both producers exist; the composite
   evidence format does not.
2. **The 2-dimensional generalisation** (check 6c's boundary), which is what
   lets a three-variable refutation be accepted.
3. **The algebraic sample** — `algebraic-witness`, 6 of 24, unchanged since
   ADR-2121 and now the largest single bucket after the clause loop's 12.
4. The fraction-free determinant is **1 file of 24**, measured, and belongs after
   all three.

## Evidence

- `bench-results/nra-cell-exact-20260916/` — the sizing, the re-bucketing and its
  controls, the A/B and its report, the held-out draw and its runner.
- `scripts/tests/mutation_controls.py` suites `nra-cell-exact-delineability` and
  `nra-cell-exact-clause-loop`.
