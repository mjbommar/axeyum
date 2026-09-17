# Lane `ax-lia-pop` — `LiaTheory`/`LraTheory` lose a shadowed assertion on `pop` (ADR-2143)

<!-- plan-section: lane-status -->

**Repaired, gated, A/B'd (`DONE`, ax-lia-pop, 2026-09-17).** The ax-proptest
audit's STOP finding: `LiaTheory::assert` overwrote a live atom's polarity in
place and logged only the index, so `pop` set the atom to `None` instead of
restoring the shadowed outer value (`push; assert(x ≥ 10); push;
assert(¬(x ≥ 10)); pop; assert(x ≤ 0)` was accepted). `LraTheory` had the same
bookkeeping; its `live` list still conflicted but the stale marker made
`rows_to_core` emit the wrong polarity in a later core. **Sizing: no wrong
verdict could ship** — both CDCL(T) drivers assign a SAT variable once until
backtrack and map it 1:1 to an atom, the front door re-solves every `check-sat`
from scratch, and the 10 committed + 67 public incremental scripts with the
script-level shape agree with z3 before and after. Fix: an opposite-polarity
re-assert returns the conflict `[(a, live), (a, new)]` and touches no state, so
every log entry is `None → Some` and `pop` is exact by construction. Four
mutation controls (conflict check killed 2/2 per theory — the three-step unit
test and the schedule fuzz; pop restore killed 4 / 3), the z3 linear-arithmetic
gate, `--lib --features full` (1,979), corpus_regression, 32 dispatch/reason
suites, progress_frontier (12), and an interleaved 800-file A/B on s7:
800 files, 499 → 500 decided, 1 raw mover (QF_IDL, ambient — both arms decide it 3/3 on recheck), 0 `:status` disagreements in either arm, 0 non-zero exits.

| exit criterion | state |
| --- | --- |
| 1. reproduce and scope | **MET** — red test confirmed (7/8, seed 9); front door answers `unsat unsat sat` = z3 on both logics; corpus census: 10 committed push/pop scripts (0 with the shape), 67 of 3,940 public incremental scripts with the shape, every one run through both binaries and z3 |
| 2. diagnosis at file:line | **MET** — ADR-2143 §Diagnosis (`lia_online.rs` `assigned`/`assigned_log`/`assert`/`pop`; `lra_online.rs` `rows_to_core` `unwrap_or(true)`) with the z3 `bound_trail` / CaDiCaL failed-assumption comparison |
| 3. fix both theories + tests | **MET** — red fuzz green (`polarity_conflicts=903`), LRA twin fuzz, three-step unit test per theory, two front-door fixtures pinned |
| 4. gates with nonzero counts | **MET** — table in ADR-2143 §Gates |
| 5. A/B on QF_LIA/QF_LRA/QF_UFLIA/QF_IDL | **MET** — 0 stable losses, 0 stable gains, 0 new disagreements (`bench-results/lia-pop-20260917/ab/summary.md`) |
| 6. ADR-2143, status, gen-adr-index, gen-plan | **MET** |

<!-- plan-section: landed-changes -->

| 2026-09-17 | `ax-lia-pop` | ADR-2143: `LiaTheory`/`LraTheory` reject an opposite-polarity re-assert as a conflict instead of overwriting (the ax-proptest STOP finding); `pop` exact by construction with a `debug_assert` invariant; red schedule fuzz green + LRA twin (finalized LCG) + core-polarity checks + three-step unit tests; `corpus/incremental/13-*`, `14-*` front-door fixtures; four mutation controls; corpus census (67 public scripts with the shape, 0 disagreements with z3); 800-file A/B (`bench-results/lia-pop-20260917/`). No wrong verdict shipped or could ship. |
