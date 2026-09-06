# Lane: s1-cdclt-watched-literals — the CDCL(T) driver's Boolean propagation gets two watched literals

<!-- plan-section: lane-status -->

**`CdclT::unit_propagate` is now two-watched-literal BCP with blocking
literals, ported verbatim from `proof_sat.rs`; the QF_IDL timeout population
goes 0/50 → 6/50 decided with zero verdict changes** (`DONE`,
s1-cdclt-watched-literals, 2026-09-06, plan slice S1).

The measurement, with its method, its tables and what it does not claim, is
[`docs/research/11-design-review/2026-09-05-s1-watched-literals-measured.md`](../../research/11-design-review/2026-09-05-s1-watched-literals-measured.md).

## The headline numbers

| | before | after |
|---|---:|---:|
| QF_IDL population (50 files) decided | **0** | **6** |
| QF_IDL PAR-2 | 2,400,000 ms | 2,193,999 ms (−8.6%) |
| QF_LRA population (33 files) decided | 4 | 5 |
| QF_LRA PAR-2 | 1,429,562 ms | 1,385,164 ms (−3.1%) |
| `boolean_propagate_ms` on `edge-matching-w=7-h=7-c=11` | 17,520 | 1,895 |
| `boolean_propagate_ms` on `a7.3.0.tweaked.3.asp` | 16,881 | 1,144 |
| `decisions` on both of those files | **0** | 45,516 / 48,307 |
| `cdclt_solve_php_6_7` (criterion median) | 48.725 ms | 3.4547 ms |

Zero verdicts contradict `declared` in either population, in either arm, and no
file decided before and went `unknown` after.

The `decisions` row is the finding. Before this change, the search on those two
files never left its **first propagation fixpoint**, so every other stage read
exactly zero — not because the theory was cheap but because it was never
reached.

## What is deliberately unchanged

The `TheorySolver` trait, the ten `CdclT::new` call sites, the theory
integration, `TheoryLayerStats`, every proof contract. `boolean_propagate`
therefore times the same stage on both sides and is its own scoreboard. The
watch code is copied from `axeyum-cnf`'s `proof_sat.rs` rather than invented,
which is the design memo's stated precondition for slice **S7** (moving CDCL(T)
onto the native core) being a deletion instead of a reconciliation of two watch
schemes.

## Two things a watch scheme needs that a rescan did not

- **A clause inserted mid-search cannot be seen by watches alone.**
  `add_permanent_clause` is called *after* an `Outcome::Sat`, under a total
  assignment the new clause usually falsifies, and no further assignment will
  ever trigger it. So its watches are chosen against the current assignment
  (non-false first, then deepest false) and it gets one full evaluation from a
  pending queue — unit implies, falsified conflicts. Input clauses of fewer
  than two literals go through the same queue.
- **`reduce_db` must rebuild the watch lists** so none names a tombstoned
  clause. Its locked-clause test also moved from a per-candidate full scan of
  `reason_clause` to one walk; that was quadratic, and it only became reachable
  once propagation was fast enough to get there.

## Sized, and not done — what the next lane needs

- **The plan's actual exit criterion is not met yet.** Parity is a count on the
  pinned 200-file list under `scripts/parity-run.sh` on an **idle** host. This
  lane scored the 50/33-file timeout populations on a loaded s4, which answers
  "did the named function stop being the bottleneck" and not "is QF_IDL at
  parity". `parity-run.sh QF_IDL` and `QF_RDL` on an idle host remain to run.
- **Three of the five profiled QF_IDL files still print no `--trace` line at
  all, in either arm.** That is Finding 0 of the profiles note reproducing
  unchanged — the dispatcher's per-route budgets sum past `smtcomp_cli`'s outer
  watchdog and the process dies inside routing. Slice **S2** (a shared,
  shrinking deadline) is the precondition for measuring those files at all, and
  one AFTER attempt on `a7.3.0` fell into the same hole before three clean
  repeats, so the boundary is not stable.
- **QF_LRA barely moved, as predicted.** The profiles note puts that division
  at 84% `theory_final_check` and 10% Boolean propagation; it is slice **S4**'s
  target. The 4/33 before-arm reading here is not interchangeable with the
  slice-1 note's 5/33 — that ran on an idle s5, this on a loaded s4, and the
  file in question is `unknown` in both arms of this pair.
- **The next contained wins in this file are `pick_unassigned` and clause
  minimization.** `pick_unassigned` is still an O(var_count) linear scan per
  decision, where `proof_sat.rs` has an order heap with the same comparator
  (highest activity, lowest index on ties — so it is trajectory-identical, not
  a heuristic change); on a 330k-variable skeleton now taking 45k+ decisions
  that is the next thing to measure. `proof_sat.rs`'s recursive learned-clause
  minimization (`minimize`) is likewise not ported. Both were left out of scope
  here to keep this slice one function.

## The guard is load-bearing, and that was checked rather than asserted

The blocking-literal fast path was mutated out
(`if false && self.lit_sat(blocker) == Some(true)`) in a throwaway
`lane-snapshot.sh` tree — never in a worktree another lane builds. Propagation
stage time rose 1,392 → 17,908 ms on `a7.3.0` and 216 → 20,927 ms on
`plan-30.cvc`, and `plan-30` went from `unsat` (its declared status) to
`unknown`. No verdict became a wrong one. On these instances (330k CNF
variables, 800k clauses) most watch visits are of satisfied clauses, so without
the cached blocker every visit dereferences the arena: the blocker is most of
the win here, not a garnish.

<!-- plan-section: landed-changes -->

| 2026-09-06 | `7376295cf` | `CdclT::unit_propagate` becomes two-watched-literal BCP with blocking literals: `lit_code`, `Watch { clause, blocker }`, `ClauseHeader { offset, len }` over a flat literal arena, the `i`/`j` watch-list compaction, and the highest-level-literal-to-index-1 convention in `analyze_conflict` — all copied from `axeyum-cnf`'s `proof_sat.rs` so slice S7 is a deletion. Reasons become clause ids read from the arena on the conflict path instead of a `Vec<Lit>` cloned at every implication. `add_permanent_clause` installs assignment-aware watches plus one pending evaluation, so a clause inserted at the final-check boundary still implies when unit and conflicts when falsified. Solver `--lib --features full`: 1449 passed, 0 failed. |
| 2026-09-06 | `889b9e558` | `clippy -p axeyum-solver --all-targets --all-features -- -D warnings`: both clause arguments are consumed into the arena rather than copied out of a borrow (no signature moves, so the ten call sites stand), the deadline-check constant moves to module scope, and the BCP loop carries a reasoned `too_many_lines` allow — splitting it would create the second watch scheme the memo warns against. |
| 2026-09-06 | `703dc05ef` | Before/after on the committed 50-file QF_IDL and 33-file QF_LRA timeout populations, arms interleaved per file on a loaded shared host, binaries confirmed different by `sha256sum`. QF_IDL 0/50 → 6/50 decided, PAR-2 −8.6%; QF_LRA 4/33 → 5/33, PAR-2 −3.1%; zero verdicts contradicting `declared`, nothing lost. |
| 2026-09-06 | `71d24d86e` | `--trace` stage tables on the five profiled QF_IDL files, both arms, with `a7.3.0` repeated three times per arm; plus the blocking-literal mutation, which costs a 13x–97x propagation-stage regression and one decided file while changing no verdict into a wrong one. Three of the five files still emit no trace line in either arm — Finding 0, slice S2's subject. |
