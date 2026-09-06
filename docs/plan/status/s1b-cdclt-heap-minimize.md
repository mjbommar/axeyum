# Lane: s1b-cdclt-heap-minimize — a VSIDS order heap and recursive learned-clause minimization for `CdclT`

<!-- plan-section: lane-status -->

**`CdclT` now decides off a VSIDS order heap and minimizes its learned clauses,
both ported verbatim from `proof_sat.rs`; the QF_IDL timeout population goes
11/50 → 27/50 decided (PAR-2 −40.1%) with zero verdict changes. Separately, the
QF_LIA −2 is **not** S1's — it is slice S2's admission preflight, named, and
handed back** (`DONE`, s1b-cdclt-heap-minimize, 2026-09-06, plan slice S1b).

Full measurement, method and caveats:
[`docs/research/11-design-review/2026-09-06-s1b-heap-minimize-measured.md`](../../research/11-design-review/2026-09-06-s1b-heap-minimize-measured.md).
Raw rows and every runner script: `bench-results/s1b-heap-minimize-20260906/`.

## Commits

| SHA | what |
|---|---|
| `13b0bc869` | the QF_LIA −2 explanation + its raw evidence |
| `16ab27ed1` | the order heap, the minimizer, the three new `TheoryLayerStats` counters |
| `75c3b1a3d` | `clippy::doc_markdown` on the new doc comments |
| `9a0615cfe` | before/after on both populations + the traced five |
| `0b80fc7fe` | both guards mutated out, and the criterion pair |
| *(this commit)* | `docs/internals/solver-dispatch.md`, the design-review note, this status file, `PLAN.md` |

## The QF_LIA −2, explained before anything was changed

The two files QF_LIA lost between `9914a1c0e` (114/200) and `b32377dc52`
(112/200), both declared `unsat`:

- `QF_LIA/bofill-scheduling/SMT_real_LIA/ex3000_2400_100.smt2`
- `QF_LIA/bofill-scheduling/SMT_real_LIA/ex4320_2400_100.smt2`

The pre-S1 sidecar no longer exists on s5 (the parity queue deletes
`parity-details/*.tsv` before each sweep), so they were found the other way: the
pre-S1 binary was run over **all 29** reference-only rows of the post-S1
sidecar; exactly two are decided by it, 27 are `unknown` in both arms.

Idle s5, `taskset -c 0-7`, 24 s, interleaved, three repeats, stable to ±1 ms:
BEFORE decides both `unsat` in **8.1 s** with `decisions=0` and one theory
conflict at level 0 — inside the *root* propagation fixpoint, so neither a
decision heuristic nor a clause minimizer is on that path. AFTER returns
`unknown` in **109 ms** with **no `--trace` theory-layer line at all**: not a
search, not a boundary, and `CdclT` is never entered.

`explain_corpus` names it in the AFTER tree's own words — `lia-dpll` declines
`(atoms=2850, cnf_vars=6533 …); declining before the online CDCL(T) probe
(dispatch-overrun fix: admission evaluated before the reserve was spent)` —
while BEFORE prints the **identical counts** under the other stage, `declining
before the first SAT round`. So `exceeds_pre_sat_skeleton_boundary(2850, 6533)`
was already true before S2; what changed is *when* it runs.
`check_with_arith_dpll` used to run `check_qf_lia_online_cdclt` first, and that
probe — which, as S2's own doc comment states, "has no size gate of its own" —
refuted both files. **This belongs to the S2 lane**: the heap and the minimizer
live inside `CdclT`, which these files no longer reach. S2's own before/after
measured six QF_IDL files and reported zero verdict changes; the QF_LIA parity
list was not in that population.

## Before/after

Idle s5, `taskset -c 0-7`, 24 s, arms interleaved per file. BEFORE = merge base
`ca31c1507` in a `lane-snapshot.sh` tree, AFTER = this worktree; binaries
confirmed different (`ee09f265b69f928a` / `561bb292d87b5fb3`).

| population | decided before | decided after | PAR-2 before | PAR-2 after |
|---|---:|---:|---:|---:|
| QF_IDL (50) | 11 | **27** | 1,953,492 ms | **1,170,032 ms** (−40.1%) |
| QF_LRA (33) | 8 | 8 | 1,254,037 ms | 1,254,132 ms (+0.008%) |

Zero verdicts contradict `declared` in either arm; nothing decided before went
`unknown` after. QF_LRA is flat as predicted (84% `theory_final_check` — slice
S4's target). These BEFORE figures are **not** interchangeable with S1's 6/50
and 4/33: that pair ran on a loaded s4.

`RVpredict_13` is the headline: **identical** 2,364,618 decisions, 3,415
conflicts and 17 restarts in both arms, identical `sat`, wall 15,526 → 1,813 ms.
Trajectory identity measured rather than argued — and it locates the 13.7 s,
since `TheoryLayerStats` covers every stage *except* decision selection and no
stage moved. Elsewhere: 28.8x more decisions in the same budget on
`edge-matching`, 2.9x on `a7.3.0`; the two jobshop files move ~2% because they
are 20.4–20.9 s of 21.1 s inside `theory_propagate`.

Both mutations are load-bearing. Heap → linear scan: decisions/s falls 1.09x to
28.8x with no verdict change (`RVpredict_13` 1,304,976 → 148,456 at an identical
decision count). Minimization off: mean learned length rises where the
trajectory stays comparable (`edge-matching` 12.333 → 14.115) and **falls** where
it diverges (`a7.3.0` 126.3 → 55.7, because the mutant runs a different search
and its mean is not over the same clauses) — which is precisely why the one-run
`learned_literals_premin − learned_literals` counters were added.
Criterion `cdclt_solve_php_6_7`: 2.8555 → 2.3304 ms, disjoint intervals.

## Gates — what ran, with counts

| gate | result |
|---|---|
| `test -p axeyum-solver --lib --features full -- --test-threads=8` | **1456 passed**, 0 failed |
| `--features full --test corpus_regression` | 1 passed |
| `--test cdclt_lia_online` / `cdclt_lra_online` / `cdclt_online` | 9 / 9 / 8 passed |
| `--features z3 --test qf_lra_differential_fuzz` | 5 passed |
| `--features z3 --test qf_uflra_differential_fuzz` | 1 passed |
| `--features z3 --test simplex_lra_fallback_differential` | 1 passed |
| `--test progress_frontier --features full -- --test-threads=1` | 12 passed, 0 failed, no REGRESSION |
| `check --workspace --all-targets` | clean |
| `build --target wasm32-unknown-unknown -p axeyum-solver` | clean |
| `clippy -p axeyum-solver --all-targets --all-features -- -D warnings` | clean |

The frontier run is advisory where its own reference-frame lines say so:
`nia_unsat` printed `NOT COMPARABLE` (throughput moved 71% mid-sweep on a loaded
s4, load 6.4 → 14.2) and `string_bound`'s `PROGRESS (+32)` is marked `ADVISORY
ONLY, do not raise the baseline`. **No baseline was raised** and
`bench-results/frontier/*.json` was reverted rather than committed. Nothing
regressed: `nia_unsat` 40 (baseline 40), `nra_degree` 40 (baseline 40).

**Did not run:** `./scripts/check-links.sh` and `python3 scripts/gen-plan.py
--check` after this final doc commit; `scripts/check-merge-hygiene.sh`; nothing
was pushed. A resumer should run all three before merging — this lane adds two
new relative links (`solver-dispatch.md` → the design-review note, and the note
→ `2026-09-05-s1-watched-literals-measured.md` and the parity plan).

## What remains, for whoever picks this up

- **The QF_LIA −2 is diagnosed, not fixed, and it is S2's.** The shape of the
  fix is visible in the trace: do not decline a query the online probe can still
  refute — gate the preflight on the probe having *also* declined, or bound the
  probe by a small reserve and decline only after it. Both file names are above;
  re-running them is a two-minute check.
- **S1's exit criterion is still unmet.** Parity is a count on the pinned
  200-file list under `scripts/parity-run.sh` on an idle host. This lane scored
  the 50/33-file timeout populations, which answers "did the named function stop
  being the bottleneck" and not "is QF_IDL at parity". `parity-run.sh QF_IDL` and
  `QF_RDL` on an idle host remain to be run, and the QF_IDL result here (11 → 27
  of 50 previously-timing-out files) is the reason to run them now.
- **The next bottleneck on these files is no longer Boolean.** After this slice
  `a7.3.0` and `edge-matching` are 15.5–16.6 s of their 22.5 s inside
  `boolean_propagate` — i.e. the search now runs long enough for propagation to
  dominate again — while the two jobshop files are 20.4–20.9 s of 21.1 s inside
  `theory_propagate`, which is S4's subject, not this one's.
- **Minimization is cheap but small here.** 22.9% of learned literals on one
  traced file, 1.3% on another, ~0 on three, and no verdict moved because of it.
  It was ported because S7 is a deletion only if both engines carry it. The
  counters that price it now exist on every `--trace` line.
- **Left deliberately conservative, and measurable:** minimization is skipped
  for a pure theory lemma (`all_theory`) and never forces a deferred
  `ExplanationId`. Both are documented at the call site; either could be relaxed
  and the `learned_literals_premin − learned_literals` counters would price the
  gain.

<!-- plan-section: landed-changes -->

| 2026-09-06 | `13b0bc869` | Named the two QF_LIA files lost between `9914a1c0e` and `b32377dc52` by sweeping the pre-S1 binary over all 29 reference-only rows, and attributed the loss to slice S2's `arith_dpll_admission_preflight` rather than S1's watched literals: BEFORE decides both `unsat` in 8.1 s inside the root propagation fixpoint (`decisions=0`), AFTER declines in 109 ms with no theory-layer trace line at all, and `explain_corpus` prints the `lia-dpll` decline naming the dispatch-overrun fix by name. |
| 2026-09-06 | `16ab27ed1` | `CdclT::pick_unassigned` becomes a MiniSat lazy-deletion VSIDS order heap (`heap`/`heap_pos`, `heap_before` keeping the linear scan's own highest-activity/lowest-index tie-break, Floyd re-heapify after an activity rescale) plus recursive `ccmin_mode = 2` learned-clause minimization (`minimize` + `lit_redundant` with the abstract-level filter), both copied from `proof_sat.rs` so slice S7 is a deletion. Two documented deviations for CDCL(T): the propagated literal is skipped by variable rather than by index, and a deferred `ExplanationId` is never forced during minimization. `TheoryLayerStats` gains `learned_clauses` / `learned_literals` / `learned_literals_before_minimization`. Guarded by a 20,000-step randomized differential against a `#[cfg(test)]` copy of the old scan (negative control run: flipping the tie-break fails it at the first pick) and by paired covered/uncovered minimization fixtures. Solver `--lib --features full`: 1456 passed, 0 failed. |
| 2026-09-06 | `9a0615cfe` | Before/after on the committed 50-file QF_IDL and 33-file QF_LRA populations, idle s5, arms interleaved, binaries confirmed different: QF_IDL 11/50 → 27/50 decided and PAR-2 −40.1%, QF_LRA flat; zero verdicts contradicting `declared`, nothing lost. `--trace` on the five profiled QF_IDL files, three repeats per arm: `RVpredict_13` decides `sat` in 1,813 ms instead of 15,526 at an **identical** 2,364,618 decisions and 3,415 conflicts. |
| 2026-09-06 | `0b80fc7fe` | Both additions mutated out in private copies on s5 and re-run against the intact binary. Heap → linear scan costs 1.09x–28.8x in decisions/s with no verdict change. Minimization off raises the mean learned length where the trajectory stays comparable and lowers it where the trajectory diverges — the finding that a two-run clause-length mean is uninterpretable under divergence, which is why the one-run counters exist. Criterion `cdclt_solve_php_6_7` 2.8555 → 2.3304 ms. |
