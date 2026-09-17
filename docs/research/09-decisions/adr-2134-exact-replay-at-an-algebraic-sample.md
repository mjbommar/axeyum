# ADR-2134: Exact replay at an algebraic sample — QF_NRA

Status: proposed
Index-summary: The single-cell CAD route refuses a cell whose representative
point is an irrational root — `algebraic-witness`, measured here at 7 of the
pinned 200 QF_NRA files with 6 of them `unknown`, which is the lever's whole
ceiling. This accepts such a point as the FINAL coordinate of a model, gated on
an exact replay of every original assertion at that exact point through the
ground evaluator's algebraic field arithmetic. Strictly additive: the acceptance
sits on the branch that otherwise returned `None`, it emits no `unsat`, and it
cannot flip a verdict. The model prints as `(root-obj p k)` and never as a
rounded rational. **The larger finding is not the lever.** Building it required
reading `RealAlgebraic::sign_at`, which decided a polynomial's sign at an
algebraic point by comparing the polynomial's values at the two ENDPOINTS of the
isolating bracket. Two point samples are not an enclosure of a range: for
`α = √2` bracketed by `(1, 2)` and `q = 25x² − 70x + 48`, `q(1) = 3 > 0` and
`q(2) = 8 > 0` while `q(√2) ≈ −0.995 < 0`, so the function answered `Pos` for a
value that is `Neg`. That is a wrong sign in the trusted evaluation path, in a
`pub` API whose doc comment claimed the stronger property the code did not
check. It is fixed by an exact Sturm root count over the bracket, not by a
smaller interval — a small interval is not evidence, a root count is. The
existing float-oracle property test structurally could not have found it: its
coefficient box has no integer solution satisfying the trap's three constraints.
**Ship decision, completed 2026-09-17:** pinned 124 → 128 (4 STABLE-GAIN, 0
loss, 0 flips) reproduces at head, but the 200-file held-out draw is 109 → 109
with zero movers, so the `≥ 1 stable gain on BOTH lists` clause fails and
`CAD_DEFAULT` stays `SINGLE_CELL`; the arm remains selectable, OFF.
Index-status: proposed

## Context

QF_NRA stands at 122 of 200 (z3 187) after ADR-2121's one-cell-per-conflict CAD
route and ADR-2126's exact delineability plus clause loop. Two independent
re-bucketings of what the route still declines named the same next lever:
`algebraic-witness` — the route finds a cell in which every collected atom
holds, but the cell's representative point is an irrational root, and the slice
carries rational samples only.

### The sizing, before any code

Measured with `--trace` on the pinned 200 through the shipped default arm
(`bench-results/nra-algebraic-witness-20260916/cause-single-cell-200.tsv`):

| cause | files |
| --- | ---: |
| `non-conjunctive` | 118 |
| `slice-bounds` | 28 |
| DECIDED | 19 |
| `coefficient-range` | 7 |
| **`algebraic-witness`** | **7** |
| everything else | 21 |

**7 of 200, and 6 of those 7 are currently `unknown`** — a file the ladder
already decides cannot be gained twice, so the mover ceiling is 6. That
triangulates ADR-2126's "6 of 24 in-bounds" and ADR-2131's "5 of 16 admissible"
rather than replacing either; the three have different denominators.

Behind `non-conjunctive`, via the clause loop's slot: the `clause-loop` arm
moves `non-conjunctive` 118 → 109 and DECIDED 19 → 24, and moves
`algebraic-witness` by **zero**, 7 → 7. That null is weaker than it looks and
the ADR records why rather than quoting it flat: `record_cad_decline` keeps the
FIRST cause and the loop runs after `non-conjunctive` is already in the slot, so
an `algebraic-witness` decline arising *inside* the loop is masked. The 109
`non-conjunctive` rows are an upper bound that may hide some, and this scan
cannot tell those two worlds apart.

## Decision

### 1. `RealAlgebraic::sign_at` gets the side condition its contract always claimed

This is the part that is not optional and is not behind a lever.

`sign_at(q)` locates `α` in an isolating bracket of its own defining polynomial
and reads `q` at the bracket's endpoints. It returned that sign as soon as the
two endpoint values agreed and were nonzero.

The bracket isolates a root of `α`'s defining polynomial. It says **nothing
about `q`**. `q(lo)` and `q(hi)` are two point samples, not an enclosure of `q`'s
range, and `q` may have an even number of roots strictly inside and dip through
the opposite sign between them — exactly where `α` may lie:

```
α = √2, bracketed by (1, 2)
q = 25x² − 70x + 48 = (5x − 6)(5x − 8),  roots 1.2 and 1.6

q(1) = 3 > 0        q(2) = 8 > 0        q(√2) ≈ −0.995 < 0
```

The old code answers `Pos`. The correct answer is `Neg`.

The fix is `poly_big::RootCounter`: an exact Sturm chain over `q`'s squarefree
part, built once per call and queried on each narrowed bracket. The endpoint read
is accepted only when the count of `q`'s roots strictly inside the bracket is
**zero** — with that, the intermediate value theorem gives `q` a constant nonzero
sign across the whole open interval, so the answer holds for every point in it,
including `α`, wherever in the bracket it sits. No separation bound to refine
below, and no "the interval got small" heuristic: **a small interval is not
evidence, a root count is.** When the count cannot be formed exactly the routine
keeps refining and finally returns `None` — a decline, never a guess.

On the `√2` fixture the correct answer arrives after two extra bisections.

#### Why the existing property test could not have found it

`sign_at_matches_float_oracle` sweeps `c0, c1 ∈ −5..=5` and `c2 ∈ −3..=3` against
a floating-point oracle. The trap needs `q(1) > 0 ∧ q(2) > 0 ∧ q(√2) < 0`, and
those three have **no integer solution in that box**: they force `c1 < −4.83`
together with a `c0` confined to an interval of width `< 0.08`. The nearest miss
is `c2 = 2, c1 = −5`, which needs an integer strictly between 3 and 3.07.

A blind population that cannot contain the defect measures the subset it happens
to cover. The replacement is an adversarial FAMILY — every quadratic
`(d·x − n₁)(d·x − n₂)` whose rational roots straddle `√2` strictly inside
`(1, 2)`, with an algebraic oracle (`n²` against `2d²`) and a non-emptiness
assertion so the family cannot silently generate nothing.

#### Is it a shipped wrong verdict?

**Not as far as this lane can show, and the ADR does not claim more.** Both
existing callers feed `sign_at` polynomials whose roots all sit in the same
sorted arrangement, and `sort_roots` declines unless the isolating intervals are
pairwise disjoint — so no root of `q` is inside `α`'s bracket and the endpoint
read happened to be sound. That invariant is external to `sign_at`, was not
stated by it, and is not owned by it. This lane adds call sites, so the function
now carries its own guarantee.

### 2. The lever: an algebraic FINAL coordinate

`CadPolicy::ALGEBRAIC_WITNESS`, one field apart from the shipped `SINGLE_CELL`.

Accepted **only at the last level**. The restriction is not caution, it is what
the arithmetic supports: a deeper level substitutes the sample into its atoms and
isolates the result's roots in exact rational arithmetic, which an algebraic
coordinate does not fit. At the last level nothing is substituted into anything
afterwards, so the sample is `rationals…, α` and the only remaining obligation is
the replay.

Accepted **only if the exact replay accepts**. `replay_model` binds the
coordinate as `Value::RealAlgebraic` and evaluates every ORIGINAL assertion
through the ground evaluator, which does `+`, `−`, `·` on real-sorted operands by
exact algebraic field arithmetic and compares them by exact interval refinement
(ADR-0038), reporting `AlgebraicArithmeticUnsupported` / `ArithmeticOverflow`
rather than guessing. So an `Ok(Bool(true))` is the *same* exact statement it is
at a rational point, reached by a different arithmetic — not a weaker gate.

**No rounding, ever.** A rational approximation can satisfy every atom while the
exact point violates one; the soundness-negative fixture builds exactly that and
shows the route refuses.

Two new typed causes, named apart because they call for different fixes:
`algebraic-replay-undecided` (the evaluator could not decide) and
`algebraic-replay-refuted` (it decided FALSE — a producer disagreement, since the
scan picked a cell where the collected atoms hold, so the assertions they came
from must hold too). On an all-rational sample the cause stays
`indeterminate-sign`, so the taxonomy on the shipped arm does not move.

### 3. `(root-obj p k)`, never a rounded rational

`RealAlgebraic::root_object` returns the **squarefree, primitive,
positive-leading** defining polynomial and the 1-based index of this root among
its distinct real roots. Squarefree because `(root-obj p k)` only names a value
if `p` and `k` agree on what "the k-th root" means, and a repeated factor makes
that ambiguous. Primitive and positive-leading because determinism is a public
promise and a model line is output: `x² − 2` and `2x² − 4` are both legitimate
stored forms of `√2` and must print the same text.

The printed spelling follows z3's `display_smt2` term for term. When the root
object cannot be formed exactly the printer **refuses**, as it did before this
arm existed — a rounded coordinate names a point that does not satisfy the query
the model answers, which is not a weaker answer but a wrong one.

## Design claims, at `file:line`

Read against `references/` in the main checkout. Note that this z3 checkout
carries local edits, so line numbers are for this tree.

### z3

* **Representation.** `algebraic_cell` at
  `references/z3/src/math/polynomial/algebraic_numbers.cpp:41-53`: a dense `mpz`
  coefficient array `m_p`/`m_p_sz`, a **dyadic** isolating interval `m_interval`,
  and bits `m_minimal`, `m_sign_lower`, `m_not_rational`, `m_i`. An `anum` is a
  tagged pointer, either that or an exact `mpq`
  (`algebraic_numbers.h:385-412`). Ours is the same shape — polynomial plus
  isolating interval — with `BigRational` endpoints rather than dyadic ones.
* **Refinement is a precision target, not a separation bound.**
  `refine_until_prec` (`algebraic_numbers.cpp:1112-1126`) delegates to
  `upolynomial.cpp:2810-2826`, whose stopping rule is
  `if (bqm.lt_1div2k(w, prec_k)) return true;` (`:2818`) — width below `1/2^k`
  for a caller-supplied `k`. There is **no** root-separation bound anywhere in
  z3's refinement loop.
* **Sign at an algebraic point is where the exactness lives.**
  `eval_sign_at` (`algebraic_numbers.cpp:2411`) tries an all-rational fast path
  (`:2417-2426`), then **interval arithmetic with bounded refinement**
  (`:2453-2484`) whose acceptance test is
  `if (!bqim().contains_zero(ri)) return is_pos ? sign_pos : sign_neg;`
  (`:2457-2459`) — an **enclosure of `q`'s range over the box**, not two endpoint
  samples. **This is the line that told us ours was wrong.** For the exact-zero
  case it eliminates the algebraic coordinates by resultants (`:2558-2559`) and
  uses `nonzero_root_lower_bound` (`:2565`, defined
  `upolynomial.cpp:2069-2092`) as the separation bound. We reach the same
  guarantee by a Sturm count, and settle the zero case by polynomial
  divisibility instead of a resultant.
* **Two-algebraic comparison** falls back to **Sturm–Tarski**
  (`algebraic_numbers.cpp:2218-2222`, `V == 0 ⇒ a == b` at `:2233`).
* **`to_rational` on an irrational is a hard abort**, not a refusal:
  `VERIFY(is_rational(a));` at `algebraic_numbers.cpp:339`.
* **Model export.** The nlsat model *is* an `anum` assignment
  (`nlsat_assignment.h:29-30, 66`); the tactic converts with
  `util.mk_numeral(m_solver.am(), m_solver.value(x), …)`
  (`nlsat_tactic.cpp:108`), and `arith_decl_plugin::mk_numeral`
  (`arith_decl_plugin.cpp:75-96`) stores the `anum` in a side table and makes an
  `OP_IRRATIONAL_ALGEBRAIC_NUM` constant holding only an index — **the AST node
  carries a handle, not a polynomial**. The polynomial reappears only at print
  time.
* **`(root-obj p k)` is emitted at exactly one place**,
  `display_root_smt2` (`algebraic_numbers.cpp:3216-3224`), over the polynomial
  printer `display_smt2_core` (`upolynomial.cpp:1195-1236`); the `get-model`
  path reaches it through `ast_smt2_pp.cpp:367`. The index is computed lazily by
  `get_root_id(...) + 1` (`algebraic_numbers.cpp:3209-3212`) — the same
  "position among the roots" we compute by Sturm.
* **Model checking at an algebraic point does not refuse.**
  `model_evaluator.cpp` has no algebraic code at all (only the comment at `:77`);
  the work is in `arith_rewriter.cpp` — `is_algebraic_numeral` folds `+`/`*`
  into one `anum` (`:1017-1045`) and comparisons dispatch to
  `am.le/ge/eq` (`:721-735`) — **but only up to defining degree 64**
  (`is_anum_simp_target` `:995-1014`, `arith_rewriter_params.pyg:8`), above which
  the rewriter returns `BR_FAILED` and leaves the assertion unevaluated. Our
  replay declines with a typed cause in the analogous situation rather than
  guessing, which is the same discipline.

### cvc5

* `RealAlgebraicNumber` (`references/cvc5/src/util/real_algebraic_number_poly_imp.h:46`,
  fields `:180-185`) wraps `poly::AlgebraicNumber`; **every non-rational
  operation is a one-line delegation to libpoly** — `sgn` at
  `real_algebraic_number_poly_imp.cpp:331-340` (`poly::sgn`), comparisons at
  `:184-226`. There is no Sturm sequence, no resultant and no separation bound in
  cvc5's own RAN code; libpoly is not vendored in-tree.
* **`toRational()` on an irrational silently returns an approximation**
  (`:136-145`, `poly::to_rational_approximation`), warned about in the header at
  `:107-112`. That is precisely the footgun this ADR refuses to build: our
  printer refuses rather than approximating.
* **cvc5 never emits `root-obj`.** It prints
  `(_ real_algebraic_number <p, (l, u)>)` (`smt2_printer.cpp:907-914`), which is
  libpoly's own debug rendering and is not re-parseable — its own regressions
  scrub the payload
  (`test/regress/cli/regress0/nl/sqrt2-value.smt2:1-4`). Internally the semantic
  form is a `WITNESS` term
  `(witness ((x Real)) (and (= p(x) 0) (< l x) (< x u)))`
  (`poly_conversion.cpp:372-397`), i.e. indexed by an INTERVAL rather than a root
  index, and marked non-closed
  (`non_closed_node_converter.cpp:114-115`).
* Evaluation at an algebraic point is exact and has **no degree cap**
  (`arith_evaluator.cpp:42-45`, `rewriter/rewrite_atom.cpp:191-224`).

**Why we take z3's `(root-obj p k)` and not cvc5's form.** An interval-indexed
witness is only as good as the interval it carries, so two refinements of the
same value print differently and neither can be compared to the other. A root
index is canonical once the polynomial is canonical, which is why
`root_object` normalises content and leading sign.

### ours

* `RealAlgebraic` — `crates/axeyum-ir/src/real_algebraic.rs:84` (`Repr` at `:96`).
* `sign_at_big`, with the side condition — same file, the `RootCounter` guard.
* `poly_big::RootCounter` — `crates/axeyum-ir/src/poly_big.rs`, over the existing
  `big_sturm_chain` (`:297`), `big_count_roots_in` (`:335`) and
  `big_squarefree_part` (`:206`).
* `big_root_object` — same file; canonicalisation in `big_normalize_primitive`.
* The acceptance branch — `crates/axeyum-solver/src/nra_single_cell.rs`,
  `solve_level`'s `CellRep::Algebraic` arm.
* `replay_model` — same file, the route's only `sat` gate.
* `smtlib_root_poly_text` — `crates/axeyum-solver/src/smtlib.rs`.

## Consequences

* A sixth `AXEYUM_NRA_CAD` arm, OFF by default.
* `CadPolicy::ALL` is now the single authority on what arms exist: `parse_cad_arm`
  scans it and the coverage test iterates it. Until this ADR that test held a
  LITERAL list of four arms and **`CLAUSE_LOOP` was not in it** — a test named
  "every arm" that carries its own copy of the arms measures the maintainer's
  memory, which is the one thing a test of that name must not do.
* `axeyum-solver` gains a direct dependency on `axeyum-arith` (already indirect
  through `axeyum-ir`, pure Rust, no C/C++).
* `sign_at` can now DECLINE where it previously answered, when the Sturm count
  cannot be formed. That is the sound direction and it costs verdicts, not
  correctness; §"Measurement" prices it.

## Alternatives rejected

* **Refine to a separation bound.** This is what the brief proposed and what z3
  does for its exact-zero case. It works, but it is strictly more expensive here:
  a Mahler/Cauchy separation bound has to be computed and then refined below,
  whereas a Sturm count over the bracket DECIDES in one chain. The bound is the
  right tool when you must prove a value is exactly zero and have no divisibility
  test; we have one.
* **Round the algebraic coordinate and replay the rational.** This is the wrong
  answer, not the cheap one — the soundness-negative fixture is a system where
  the rounded point satisfies every atom and the exact point violates one.
* **Carry algebraic coordinates into deeper levels.** The real generalisation,
  and genuinely larger: every downstream substitution and root isolation would
  have to work over algebraic coefficients. Left undone deliberately; the last
  level is where the measured 7 files sit.
* **Put the `sign_at` fix behind the lever.** Rejected. A wrong sign in a `pub`
  API documented as exact is not a treatment arm.

## Measurement

`bench-results/nra-algebraic-witness-20260916/README.md` carries the full tables,
the protocol and a harness incident. The headline:

**QF_NRA pinned 200, one binary, two env values, interleaved per file:
`single-cell` 124 → `algebraic-witness` 128, +4. Four movers, every one
`unknown → sat`. 0 `sat`↔`unsat` flips. 0 arm runs without a verdict token.**

Three-pass recheck of all four movers, arms alternating within the passes:
**4 STABLE-GAIN, 0 STABLE-LOSS, 0 UNSTABLE, exit status 0 on all 24 runs.**

Every gained `sat` replayed independently through the front door
(`examples/nra_algebraic_witness_replay.rs`):
`files=4 sat_with_algebraic_coordinate=4 replay_failures=0` — four of four, each
with exactly one irrational coordinate, each nameable as a root object. The same
checker on the shipped arm finds nothing and **exits 3**, so the evidence fails
in both directions rather than only one.

### The controls

| division | A | B | delta | movers | flips |
| --- | ---: | ---: | ---: | ---: | ---: |
| QF_NRA (pinned 200) | 124 | **128** | **+4** | 4 | 0 |
| QF_NIA (200) | 85 | 84 | −1 | 1 | 0 |
| QF_LRA (200) | 107 | 107 | **0** | **0** | 0 |

QF_LRA — the division the lever cannot reach — moved nothing. QF_NIA's single
`sat → unknown` is **ambient**: the three-pass recheck returns NEITHER-DECIDES
(both arms `unknown` 3/3), and arm A's lone `sat` in the sweep came at 23,225 ms
of a 24,000 ms budget. **0 STABLE-LOSS across all three divisions.**

### The sizing did not predict the movers

This is the ADR's second finding and it corrects its own §Context.

Of the 6 sized `algebraic-witness` + `unknown` files, **1** moved. **3 of the 4
movers were sized `non-conjunctive`.** Traced rather than assumed: on
`atan-problem-2-weak-chunk-0018.smt2` both arms decline the `nra-real-root` rung
with `non-conjunctive` — the cause the census reads — and the verdict diverges at
a LATER rung, where `nra.rs:339` calls `decide_real_poly_constraint`, which
offers `decide_single_cell` with `cad_policy().algebraic_witness`. The lever is
reached on a SUBPROBLEM long after the top-level rung has stamped a first-wins
slot.

**A first-wins decline slot makes a cause census non-predictive of a lever's
effect whenever the same decider is reachable from more than one rung.** The
census answers "why did this rung refuse"; it does not answer "what is this lever
worth", and §Context's ceiling of 6 is neither an upper nor a lower bound on the
measured +4. The A/B is the sizing. Any future lane sizing an NRA lever from
`CadDecline` counts should read this paragraph first.

## Status of the ship decision

**Not `accepted`, and the lever ships OFF — now by a completed measurement,
not by an incomplete one.**

The criterion for a default move is **0 stable losses AND 0 flips AND ≥ 1
stable gain on BOTH the pinned draw and the held-out draw**, with the QF_NIA
and QF_LRA controls flat.

### 2026-09-16, this ADR's own round (s5, `df2dfc0f…`)

Pinned QF_NRA +4 with 4 STABLE-GAIN / 0 STABLE-LOSS / 0 UNSTABLE, QF_NIA flat
after recheck, QF_LRA flat with zero movers, 0 flips anywhere, 0 arm runs
without a verdict token. **The held-out draw reached 23 of 200 files** (0
movers) before the round closed, so the criterion was not evaluated.

### 2026-09-17, the completion (lane `AX-2134-HELDOUT`, s7, head `43f1e0f90`)

`bench-results/nra-algebraic-witness-heldout-20260917/README.md` carries the
protocol and every row. One `smtcomp_cli` built `--release --features full`
from a snapshot of `43f1e0f90` (sha256 `d3606850…`; main had moved 60+
commits past this ADR's A/B, including the SAT-core changes of ADR-2142 and
ADR-2145), two `AXEYUM_NRA_CAD` values (`single-cell`, which IS `CAD_DEFAULT`
at that head, against `algebraic-witness`), interleaved per file on s7 core
pairs `1,9` / `3,11`, 24 s / 8 GiB, `$EPOCHREALTIME` timing with the 200 ms
self-check reading 203–205 ms.

| list | A `single-cell` | B `algebraic-witness` | delta | movers | flips | `:status` disagreements |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| pinned 200, re-run at head | 124 | **128** | **+4** | 4 (all `unknown → sat`) | 0 | 0 of 250 |
| **held-out 200** | 109 | **109** | **0** | **0** | 0 | 0 of 216 |

* **Pinned, at head:** the SAME four files as on 2026-09-16, every one in
  `meti-tarski/atan/problem/2/`; three-pass recheck 3× per arm with the arms
  alternating within the passes: **4 STABLE-GAIN, 0 STABLE-LOSS, 0 UNSTABLE,
  exit 0 on all 24 runs.** The SAT-core changes between the two heads moved
  neither arm's count.
* **Held-out:** the population is ADR-2126's held-out draw (same script,
  same `SEED = 20260916`, re-drawn at head to the byte-identical list);
  overlap with the pinned list checked at **0 of 200**. **Zero movers of any
  kind**, so there was nothing to recheck: 0 raw gains, 0 raw losses, 0
  flips, 0 nonzero exits. Arm A's 109 reproduces ADR-2126's own arm A on this
  population. The held-out list holds 4 `atan/problem/2` files and both arms
  decide all four in under 210 ms; the 91 files both arms leave `unknown`
  are 33 other `meti-tarski`, 21 `LassoRanker`, 11 `hycomp`, 9 `Sturm-MBO`
  and 17 more.

| criterion clause | pinned | held-out |
| --- | --- | --- |
| 0 stable losses | holds (0) | holds (0) |
| 0 flips | holds (0) | holds (0) |
| ≥ 1 stable gain | holds (4) | **fails (0)** |

**Decision: `CAD_DEFAULT` stays `CadPolicy::SINGLE_CELL`.** The
`algebraic-witness` arm remains selectable by name and OFF by default; this
ADR stays `proposed`. The lever is a real, reproducible, loss-free +4 on one
narrow shape and a null on the one population it was not built against, and
the criterion exists precisely so that a default move is earned on the second
of those. A lane re-opening this must draw a NEW held-out population (change
the seed in `draw-heldout-qfnra.py` and say so): this one has now been scored
twice and is no longer blind.

### Still unmeasured

* The binary-against-binary A/B that prices the `sign_at` exactness fix. That
  fix is not behind a lever and is in BOTH arms of every number above, so those
  numbers say nothing about its cost. It can only convert an accept into a
  decline, never a correct verdict into a wrong one, so what is unknown is lost
  coverage rather than soundness.
* The eight nonlinear z3 differential fuzzes were NOT RUN on 2026-09-17: they
  are mandatory only when the default moves, and it did not.

`docs/plan/status/nra-algebraic-witness.md` carries the per-criterion state.
