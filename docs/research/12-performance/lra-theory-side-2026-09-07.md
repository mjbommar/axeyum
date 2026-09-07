# QF_LRA, the theory side: cutting the `final_check` call count

Lane `lra-theory-side`, 2026-09-07. Diary — written as the work happens,
including the hypotheses that turn out to be wrong.

## Why this lane exists

[ADR-1732](../09-decisions/adr-1732-second-reference-per-division-not-a-replacement.md)
re-measured the QF_LRA frontier and the gap is **84 files**, not the 52 the
board carried: Yices 2.7.0 decides 181 of the committed 200-file list where
cvc5 decides 145 and we decide 97. That makes this the largest single
arithmetic target.

The [family page](../../plan/families/smt-quantifier-free/qf-lra.md) census
splits the loss cleanly in two, with no third class:

- **31 search timeouts.** Profiled: `final_check` → `feasibility` → simplex was
  84% of wall, called **1,150–15,000 times per file**. A prior slice fixed one
  redundant `O(rows × columns)` pass inside the pivot — the *per-call* half.
  The **call count** is untouched.
- **23 admission declines** at `MAX_ONLINE_LRA_ATOMS = 1_024`
  (`crates/axeyum-solver/src/lra_theory.rs`). That cap is load-bearing:
  removing it was measured at **0 new decides and 54 memory aborts**.

Two things this lane will not do. It will not unify the engine — that was
measured on 2026-09-06 and `CdclT` is already 3.4% *faster* than the native
core on the committed benchmark, because earlier slices closed the
Boolean-search gap. And it will not raise the atom constant; if that moves it
becomes a measured memory budget with a number (ADR-1752).

## The method, and why it is not negotiable here

The last person on this division found the plan's stated cause was **false**.
The belief was that the tableau needed a warm start. S4 wired six counters in
*before changing anything* and measured `simplex_cold_restarts = 0` across
6,571 checks: the engine was already warm, and the real cost was one redundant
pass. So the rule for this lane is **wire the counter, then look** —
`TheorySolver::engine_counters` and `TheoryLayerStats` already exist and get
extended rather than reasoned around.

## Where the code is

- `crates/axeyum-solver/src/lra_theory.rs` — the `CdclT` adapter
  (`CdcltLraTheory`), the atom cap, `check_qf_lra_online_cdclt`.
- `crates/axeyum-solver/src/lra_online.rs` — `LraTheory`: `assert`,
  `install_bounds` (the cheap O(1) partial check), `final_check`,
  `feasibility`, `rows_to_core`, `propagate_bounds`.
- `crates/axeyum-solver/src/cdclt.rs` — `run_final_check` and `solve_inner`.
- `crates/axeyum-bench/examples/smtcomp_cli.rs` — `--trace` prints the whole
  counter line.

The shape of the search under `deferred_final_check` (ADR-1701) is the thing to
keep in mind while reading the numbers: `assert` keeps **only** the O(1)
form-bound crossing test, and the complete simplex decision runs once per
**total Boolean assignment**, in `final_check`. So `final_checks` is literally
"how many complete Boolean assignments the search had to enumerate", and
cutting it means either pruning earlier (propagation, or a check before the
assignment is total) or learning stronger lemmas from each refutation.

## Pre-registered hypotheses, ranked before any measurement

Recorded now so that a later measurement can falsify them rather than confirm
whatever I end up doing.

**H1 — weak lemmas.** Most `final_check` calls return `Conflict`, and the cores
are large relative to the live set, so each learned clause excludes close to one
assignment and the search enumerates them. Prediction: `final_check` conflicts
much greater than `final_check` sats, and mean core size is a large fraction of
the atoms assigned. Test: split the conflict counter by call site and sum core
literals.

**H2 — the widening fallback fires.** `rows_to_core` widens to the *full*
asserted set when the Farkas multipliers name no rows. If that fires often the
lemma is maximally weak. Prediction: I expect this is rare; if it is not, it is
the single cheapest fix on the board. Test: a counter on that branch.

**H3 — the cheap `assert` check almost never fires.** `install_bounds` only
detects a crossing on the *same canonical form*. If assert-time bound conflicts
are near zero, then nothing at all prunes the search between two total
assignments except Boolean propagation, which explains the call count directly.
Test: a counter on `bound_crossing` returning `Some`.

**H4 — propagation is still thin after S4.** S4 generalized `unit_bound` to
`form_bound`, which should have lifted the 79-literals-across-6,571-checks
figure a lot. Prediction: `propagations_offered` is now materially nonzero but
still small next to `decisions`. Test: the existing counter, ratio to decisions.

**H5 — repeated work.** Consecutive `final_check` calls re-refute overlapping
constraint sets. Test: no direct counter yet; approximate with the ratio of
distinct core signatures to conflicts if H1 says it is worth building.

My prior ordering is H1 > H3 > H4 > H2 > H5. I expect H1 and H3 to be two
descriptions of the same defect.

## Log

### 2026-09-07 — lane opened

Read the family page, `lra_theory.rs`, the `LraTheory` half of `lra_online.rs`,
and `CdclT::run_final_check`. Nothing measured yet. Next: extend the counters
(split `final_check` outcomes, core literals, the widening fallback, assert-time
bound conflicts) and take the baseline on the 33-file population on an idle s7.

One thing already settled by reading rather than measuring: the atom cap's own
doc comment records that raising it to 16384 changed **no** verdict on the 64
files of the 200-file list that carry more than 1024 atoms, cost one file 24 s
it used to decline in 0.12 s, and made `QF_LRA/sc/sc-39.base.cvc.smt2` (1492
atoms) abort at the 8 GiB cap. The named cost is `AtomBuilder` normalization —
a dense `LinExpr` per atom polarity over ~700 variables — which the simplex
rewiring never touched. So the cap is a **normalization memory** budget, and
"raise the constant" is already a refuted move; the open question is whether
normalization can be made to cost less, not whether the number can be bigger.
