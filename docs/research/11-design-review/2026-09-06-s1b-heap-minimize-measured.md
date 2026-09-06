# S1b measured: a VSIDS order heap and clause minimization in `CdclT`, 2026-09-06

Slice **S1b** of the [SMT/SAT parity plan](../../plan/smt-parity-plan-2026-09-05.md)
(§2.1, row S1): the two things
[slice S1](2026-09-05-s1-watched-literals-measured.md) named as "the next
contained wins in this file" and left out of scope to keep that slice one
function. Raw rows: `bench-results/s1b-heap-minimize-20260906/`.

## 0. First, the QF_LIA −2 — and it is not S1's

The ledger recorded QF_LIA falling 114 → 112 between solver commits
`9914a1c0e` and `b32377dc52`, the window S1 landed in. This lane was told to
explain it before changing anything. It is **not** a boundary and **not** a
trajectory change; it is a route-admission decline introduced by a *different*
slice.

The pre-S1 `QF_LIA.tsv` sidecar no longer exists on s5 (the parity queue
deletes `parity-details/*.tsv` before each sweep and only four other divisions
were copied out), so the files were found the other way round: the pre-S1
binary was run over all **29** reference-only rows of the post-S1 sidecar.
Exactly two are decided by it, both declared `unsat`:

- `QF_LIA/bofill-scheduling/SMT_real_LIA/ex3000_2400_100.smt2`
- `QF_LIA/bofill-scheduling/SMT_real_LIA/ex4320_2400_100.smt2`

Idle s5, `taskset -c 0-7`, 24 s budget, arms interleaved, three repeats each,
stable to ±1 ms:

| file | arm | verdict | wall | trace line |
|---|---|---|---:|---|
| `ex3000_2400_100` | before | **unsat** | 8,115 / 8,116 / 8,115 ms | `theory_conflicts=1 decisions=0` |
| `ex3000_2400_100` | after | **unknown** | 109 / 108 / 107 ms | *(none)* |
| `ex4320_2400_100` | before | **unsat** | 8,216 / 8,216 / 8,115 ms | `theory_conflicts=1 decisions=0` |
| `ex4320_2400_100` | after | **unknown** | 109 / 108 / 109 ms | *(none)* |

109 ms is not a search and 8.1 s of a 24 s budget is not a boundary. The BEFORE
arm refutes both inside the *root* propagation fixpoint (`decisions=0`, one
theory conflict at level 0), so no decision heuristic and no clause minimizer is
on that path either way; and the absent `--trace` line says `CdclT` is never
entered in the AFTER arm at all.

`explain_corpus --json --timed-trace` names the cause in the AFTER tree's own
words — `lia-dpll` declining with

> `(atoms=2850, cnf_vars=6533, base_trigger=>1024/>4096, moderate_envelope<=1280/<=8192, …); declining before the online CDCL(T) probe (dispatch-overrun fix: admission evaluated before the reserve was spent)`

while the BEFORE tree prints the **identical counts** under the other stage,
`declining before the first SAT round`. So
`exceeds_pre_sat_skeleton_boundary(2850, 6533)` was already true before S2; what
changed is *when* it is evaluated. `check_with_arith_dpll` used to run
`lia_theory::check_qf_lia_online_cdclt` first, and that probe — which, as S2's
own doc comment states, "has no size gate of its own" — refuted both files in
8 s. S2's `arith_dpll_admission_preflight` (`crates/axeyum-solver/src/dpll_lia.rs`)
now returns `Unknown(ResourceLimit)` before the probe is ever launched.

This is outside S1b's reach — the heap and the minimizer live inside `CdclT`,
which these two files no longer reach — and belongs to the **S2** lane. The
shape of a fix is visible in the trace: do not decline a query the online probe
can still refute, e.g. gate the preflight on the probe having *also* declined,
or bound the probe by a small reserve and decline only after it. S2's own
before/after measured six QF_IDL files and reported zero verdict changes; the
QF_LIA parity list was not in that population, which is where the two files were
spent.

`explain_corpus` is diagnostic only — it disagrees with the shipped front door
on 134 of 397 benchmarks — and is quoted here **only** for the decline reason
string, which `smtcomp_cli` discards. The verdicts above are `smtcomp_cli`'s.

## 1. The change

**The order heap.** `CdclT::pick_unassigned` was an O(var_count) linear scan per
decision, taken 45,000+ times per file on the 330,000-variable skeletons S1
measured. It is now the MiniSat lazy-deletion order heap ported from
`proof_sat.rs`: `heap` / `heap_pos` with a `HEAP_ABSENT` sentinel, `heap_before`
(highest activity, lowest index on ties — the scan's *own* tie-break, so the
comparator is not a heuristic change), `heap_percolate_up`/`_down`, and a Floyd
`heap_rebuild` after a VSIDS rescale, because a rescale can collapse two
distinct tiny activities into a tie the prior layout never had to order.

One predicate a plain SAT core does not need: a variable may be **inactive**
(reserved for a theory atom no final-check lemma has named). Such a root is
discarded exactly like an assigned one and re-inserted by `activate_variables`,
which `register_new_atoms` now routes through instead of setting the flag
directly.

**Minimization.** Recursive (self-subsuming) minimization of the 1-UIP clause,
MiniSat `ccmin_mode = 2`: `minimize` plus the iterative `lit_redundant` walk
with the `abstract_level` bitmask filter and per-probe `to_clear` rollback. At
the `path_count == 0` point `seen[v]` is already true exactly for the
non-asserting literals, which is the reference's precondition. Two deliberate
deviations:

- `lit_redundant` skips the propagated literal **by variable**, not by taking
  `reason[1..]`. In a plain SAT core the implied literal is slot 0 of its reason
  by construction; here a reason may be a theory clause built by
  `theory_reason_clause`, whose literal order is the theory's.
- `minimization_reason` never forces a **deferred** explanation handle
  (ADR-1701). Resolution needs a reason to make progress; minimization does not,
  and forcing one spends theory time the search never asked for and can fail. A
  literal whose reason exists only as a handle reads as reasonless and is kept.

Minimization is skipped for a pure theory lemma (`all_theory`), so the
`is_theory_lemma` flag can never overstate what was derived.

`TheoryLayerStats` gains `learned_clauses`, `learned_literals` and
`learned_literals_before_minimization`; `smtcomp_cli --trace` prints all three.
Unchanged: the `TheorySolver` trait, the ten `CdclT::new` call sites, the theory
integration, phase saving, every proof contract.

## 2. Method

Host **s5**, idle (load 0.00–0.05 at start; 16 cores), `taskset -c 0-7`,
`MEM_LIMIT_GB=8 timeout 29 smtcomp_cli --timeout-ms 24000`, arms interleaved per
file. BEFORE is the merge base `ca31c1507` in a `lane-snapshot.sh` tree; AFTER is
this worktree. Both release-built on s5, confirmed different:

| arm | sha256 (first 16) | bytes |
|---|---|---:|
| BEFORE | `ee09f265b69f928a` | 42,237,624 |
| AFTER | `561bb292d87b5fb3` | 42,356,704 |

Populations are the committed ADR-1701 slice-1 ones, unchanged:
`qf_idl_population.tsv` (50 files) and `qf_lra_population.tsv` (33).

## 3. Result 1 — the populations

| population | decided before | decided after | PAR-2 before | PAR-2 after | change |
|---|---:|---:|---:|---:|---:|
| QF_IDL (50) | 11 | **27** | 1,953,492 ms | **1,170,032 ms** | **−40.1%** |
| QF_LRA (33) | 8 | 8 | 1,254,037 ms | 1,254,132 ms | +0.008% |

Sixteen QF_IDL files newly decided; **zero** verdicts contradicting `declared`
in either arm; **nothing** decided before that went `unknown` after. QF_LRA is
flat, as predicted — the profiles note puts that division at 84%
`theory_final_check`, which is slice S4's subject, not this one's.

The BEFORE figures here are **not** interchangeable with S1's (6/50 and 4/33):
that pair ran on a loaded s4, this one on an idle s5. Same caveat S1 recorded
about its own divergence from slice 1.

## 4. Result 2 — the traced five

`--trace`, three repeats per arm per file. Median of three:

| file | arm | verdict | wall (ms) | decisions | conflicts | `boolean_propagate_ms` | `theory_propagate_ms` | mean learned length |
|---|---|---|---:|---:|---:|---:|---:|---:|
| `RVpredict_13` | before | sat | 15,526 | 2,364,618 | 3,415 | 492 | 43 | — |
| `RVpredict_13` | after | sat | **1,813** | **2,364,618** | **3,415** | 469 | 42 | 6.291 |
| `edge-matching-…-c=11` | before | unknown | 22,531 | 90,378 | 5,642 | 1,095 | 2 | — |
| `edge-matching-…-c=11` | after | unknown | 22,533 | **2,603,240** | 18,057 | 15,519 | 48 | 12.333 |
| `a7.3.0.tweaked.3.asp` | before | unknown | 22,231 | 79,845 | 383 | 697 | 1 | — |
| `a7.3.0.tweaked.3.asp` | after | unknown | 22,232 | **230,766** | 1,481 | 16,572 | 4 | 125.7 |
| `jobshop20-…` | before | unknown | 21,132 | 78,962 | 853 | 30 | 20,429 | — |
| `jobshop20-…` | after | unknown | 21,132 | 80,113 | 861 | 30 | 20,859 | 6.876 |
| `jobshop26-…` | before | unknown | 21,130 | 30,656 | 472 | 22 | 20,579 | — |
| `jobshop26-…` | after | unknown | 21,132 | 31,195 | 475 | 23 | 20,855 | 7.480 |

`RVpredict_13` is the finding. **Identical** decisions, conflicts and restarts
in both arms, identical `sat` verdict, and the wall clock falls 8.6x. That is
the trajectory-identity claim measured end to end on a real file rather than
argued — and it *locates* the 13.7 s, because `TheoryLayerStats` covers every
stage except decision selection (its own doc says so) and no stage moved. The
time was the linear scan.

Where the trajectory is free to move, it moves a lot in the same budget:
28.8x more decisions on `edge-matching`, 2.9x on `a7.3.0`. The two jobshop files
are 20.4–20.9 s of 21.1 s inside `theory_propagate` and move ~2%, which is what
a Boolean-side change should do to a theory-bound file.

Minimization, read off the new one-run counters
(`learned_literals_premin − learned_literals`):

| file | learned clauses | mean length premin | mean length | literals removed |
|---|---:|---:|---:|---:|
| `a7.3.0.tweaked.3.asp` | 1,537 | 163.0 | **125.6** | 57,364 (22.9%) |
| `edge-matching-…-c=11` | 18,192 | 12.50 | 12.33 | 3,055 (1.34%) |
| `jobshop20-…` | 1,040 | 6.888 | 6.883 | 5 |
| `RVpredict_13` | 3,415 | 6.292 | 6.291 | 1 |
| `jobshop26-…` | 633 | 7.480 | 7.479 | 1 |

## 5. Result 3 — the guards are load-bearing

Each addition was removed in a private copy of the AFTER tree on s5 — never in
a worktree another lane builds — and the same five files re-run against the
intact binary, interleaved, two repeats. `mutate.py` asserts each anchor occurs
exactly once, so a silent no-op mutation is impossible; all three release
binaries differ by `sha256sum`.

**Heap removed** (fall back to the linear scan). Decisions per second falls on
every file; no verdict changes:

| file | intact dec/s | mutant dec/s | factor |
|---|---:|---:|---:|
| `RVpredict_13` | 1,304,976 | 148,456 | **8.8x** |
| `edge-matching-…-c=11` | 115,002 | 3,988 | **28.8x** |
| `a7.3.0.tweaked.3.asp` | 10,385 | 3,467 | 3.0x |
| `jobshop20-…` | 3,769 | 3,450 | 1.09x |
| `jobshop26-…` | 1,480 | 1,358 | 1.09x |

`RVpredict_13` is again the controlled case: identical verdict, identical
2,364,618 decisions, identical 3,415 conflicts — only the clock moves,
1,812 → 15,928 ms.

**Minimization removed.** Mean learned length rises where the trajectory stays
comparable — `edge-matching` 12.333 → **14.115**, `RVpredict_13` 6.2914 →
6.2917 at an identical decision count — and **falls** on the other three
(`a7.3.0`: 126.3 intact vs 55.7 mutant). That is not minimization making clauses
longer. The mutant explores a different search entirely (330,803 decisions and
1,139 learned clauses against 230,093 and 1,529), so the two means are not means
over the same clauses. **A mutant-versus-intact clause-length mean is only
interpretable when the trajectory does not diverge**, and on three of five files
it diverges — which is exactly why this slice added the one-run counters rather
than relying on a two-run comparison. The check that the mutation landed is that
the mutant's `premin` equals its `after` on every row.

Criterion `cdclt_solve_php_6_7`, idle s5, bench binaries confirmed different:
**2.8555 ms → 2.3304 ms**, disjoint intervals, 1.23x. Modest on purpose: the
committed pigeonhole is 42 variables, where a linear scan is 42 comparisons and
a heap ~6. The heap's win is asymptotic in the variable count and is measured on
the 330,000-variable skeletons instead.

## 6. Gates

| gate | result |
|---|---|
| `test -p axeyum-solver --lib --features full -- --test-threads=8` | 1456 passed, 0 failed |
| `--features full --test corpus_regression` | 1 passed |
| `--test cdclt_lia_online` / `cdclt_lra_online` / `cdclt_online` | 9 / 9 / 8 passed |
| `--features z3 --test qf_lra_differential_fuzz` | 5 passed |
| `--features z3 --test qf_uflra_differential_fuzz` | 1 passed |
| `--features z3 --test simplex_lra_fallback_differential` | 1 passed |
| `--test progress_frontier --features full -- --test-threads=1` | 12 passed, 0 failed, **no REGRESSION** |
| `check --workspace --all-targets` | clean |
| `build --target wasm32-unknown-unknown -p axeyum-solver` | clean |
| `clippy -p axeyum-solver --all-targets --all-features -- -D warnings` | clean |

The frontier run is **advisory** where its own reference-frame lines say so:
`nia_unsat` printed `NOT COMPARABLE` (throughput moved 71% during the sweep on a
loaded s4, load 6.4 → 14.2) and `string_bound`'s `PROGRESS (+32)` is marked
`ADVISORY ONLY, do not raise the baseline`. `bv_reduction` +6 and `lia_cuts` +9
read as ratchetable PROGRESS. **No baseline was raised from this run**, per the
ratchet's own instruction, and `bench-results/frontier/*.json` was reverted
rather than committed. Nothing regressed: `nia_unsat` 40 (baseline 40),
`nra_degree` 40 (baseline 40).

## 7. What this does not claim

It does not claim a division. Parity is a count on the pinned 200-file list under
`scripts/parity-run.sh`; this lane scored the 50/33-file timeout populations,
which is the right instrument for "did the named function stop being the
bottleneck" and the wrong one for "is QF_IDL at parity". `parity-run.sh QF_IDL`
and `QF_RDL` on an idle host remain S1's unmet exit criterion and are still
unmet.

It does not claim the QF_LIA −2 is fixed. It is explained, attributed, and
handed to S2 with the two file names.

It does not claim minimization is worth much on this population. It removes
22.9% of learned literals on one traced file, 1.3% on another and ~0 on three,
and no file's verdict moved because of it. It was ported because S7 is a
deletion only if both engines carry it, and the counters that price it now exist.
