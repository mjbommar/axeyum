# coordinator-solver — the three improvement lists (cindergraph, Glaurung, Axeyum)

<!-- plan-section: lane-status -->

Status: **all three lists complete and pushed, 2026-09-17 afternoon** — cindergraph 16/16 (`8bd2051` on GitHub), Glaurung 10/10 on the GitHub cindergraph crate (`d61be9ba`), Axeyum 16/16 (`178639959`). The A13 solver queue continues: item 1 closed (the algebraic witness's held-out draw refused it), items 2–4 in flight. The user's goal is to
work through the three lists written the same afternoon:
[Axeyum](../improvement-list-2026-09-16.md) (committed, `8df853252`),
cindergraph `docs/improvement-list-2026-09-16.md` and Glaurung
`docs/development/improvement-list-2026-09-16.md` (both untracked in the
user's clones at `../cindergraph` and `../glaurung`). Foreign-repo lanes work
in their own `git worktree` under `/data0/axeyum/scratch/wt-*` on a branch,
commit there, and never push; Axeyum lanes use the usual isolated worktrees.


## Round one (parallel)

| lane | repo | items | model | notes |
|---|---|---|---|---|
| CG-EXPORT | cindergraph | 1, 2, 4, 5, 6, 8, 9, 10, 11, 14 | Opus | branch `cg-export-2026-09-16`; must keep the Axeyum consumer's table unchanged |
| GL-PIN | Glaurung | 1, 2, 6, 8, 9 + a `solver-NNN` decision record | Opus | branch `gl-pin-2026-09-16`; pin → Axeyum `8df853252`; 733 malformed corpus files quarantined, 107 valid become a verdict set |
| AX-BINDINGS | Axeyum | 1, 2, 3, 4, 13 | Sonnet | example on `axeyum.smt`, overflow predicates, `axeyum-bench` `full` feature, doc pointers, Python example inventory |
| AX-PROPTEST | Axeyum | 5 | Opus | ADR-2141 if a decision; inventory of every boxed generator, reachability per row, mutation control per finding |
| AX-POLICY | Axeyum | 6, 7, 9 | Opus | ADR-2140; `ModelPreference {Any, PreferZero, LeastUnsigned}`, bounded minimisation, `stats()` in the bindings; QF_BV A/B on s7 |

## Landed (2026-09-17, by 06:00)

| lane | repo | result | where |
|---|---|---|---|
| CG-EXPORT | cindergraph | `op`, `type`/`operand_type`, `line`/`column`, declarator and parameter structure, `expr_internal` CFG marks, `__version__`, path-argument errors, the export schema contract (items 1, 2, 4, 5, 6, 8, 9, 10, 11, 14) | `6971e30` on local `main` |
| CG-OPS | cindergraph | `repr="ops"`: the evaluation plan as typed operations with explicit promotion / usual-arithmetic / assignment conversions; the plan has no cast rule (item 3) | `3d8c36e` |
| CG-FINISH | cindergraph | loop metadata for an unroller, the single-parse session documented and pinned, a 13-sample defect conformance corpus, the list's status (items 12, 13, 15) | `1ff114a` |
| CG-FACTS | cindergraph | `// @cindergraph capacity(p) = v` grammar (with `// axeyum:` alias) and an API argument, both landing as `facts` on exported nodes with diagnostics (item 7) | `de1865c`; **15 of 16 done**, 16 = Milestone H |
| GL-PIN | Glaurung | pin → `8df853252`; 735 of 842 shadow-split files were z3-rejected exports, quarantined; 107 valid with pinned verdicts replay 107/107; capture parses with z3; traces without `.git`; July notes frozen (items 1, 2, 6, 8, 9; solver-032) | `11b68faf` on local `master` |
| GL-SIXCELL | Glaurung | the timing campaign at the new pin: inconclusive under ADR-0272; cold Axeyum at parity or faster than z3 on 3 of 4 drivers, **warm session latency grows with age** (item 3; solver-033) | `3b3f2b4b` |
| GL-GATE | Glaurung | shadow-split capture as a weekly tier with a regression floor; first capture: 41,493 checks, 0 disagreements, 27 new scripts all decided one-shot, floor 107 → 134 (item 7; solver-034) | `f8eab42b`; **7 of 10 done**, 4/5 wait on Axeyum pushes, 10 = Milestone H |
| AX-BINDINGS | Axeyum | the example on `axeyum.smt`, overflow predicates, `axeyum-bench` `full` feature, doc pointers, Python example inventory (items 1–4, 13) | `dafe6cd6e`, pushed |
| AX-LIFTER | Axeyum | loop unrolling, six new sink kinds, 9 replayed findings on cindergraph's own fixtures (items 10–12) | `0cd81574e`, pushed |
| AX-POLICY | Axeyum | `ModelPreference` OFF (ADR-2140), least-witness search in the bindings, typed stats; forcing the SAT phase moves 0 of 15 models (items 6, 7, 9) | `904f8e222`, pushed |
| AX-WARM | Axeyum | the warm regression bisected to the native core becoming the engine; the target-phase snapshot re-walked the trail per decision; fixed, trajectories byte-identical, 306 → 7.5 ms per check (ADR-2142) | `d9907b3c2`, pushed |
| AX-PROPTEST + AX-LIA-POP | Axeyum | 599 boxed generators audited, 328 unreachable, 24 fixed with a ratchet (ADR-2141); the LIA/LRA shadowed-assertion `pop` defect fixed, no wrong verdict could ship (ADR-2143) (item 5) | `11b895a35`, pushed |

## Round three and four (landed)

| lane | repo | result | where |
|---|---|---|---|
| AX-2134-HELDOUT | Axeyum | A13 item 1: pinned +4 stable held, held-out 109 → 109 with zero movers; the lever stays OFF by the criterion | `f7cd4195f`, pushed |
| GL-CINDER | Glaurung | **the user's instruction**: Glaurung on the GitHub cindergraph crate at `ed5e55e`, 32,872 embedded lines deleted, suite identical by name; four Sep-13 parity corrections found missing upstream (source-001) | `3be252e5`, pushed |
| CG-PARITY | cindergraph | those four corrections ported with their tests and mutation kills; projection byte-identical on 930 functions; the `for (;;)` empty-body case undecided by any recorded Joern output | `8bd2051`, pushed |
| GL-CINDER2 | Glaurung | re-pinned to `8bd2051`; projection byte-identical; nothing waits on cindergraph | `d61be9ba`, pushed |
| AX-GATE | Axeyum | item 16: the defects example is a gate (`scripts/check-cindergraph-defects.sh`, in `just py-check` and `check.sh`), cindergraph pinned in the dev group, three subject mutations each kill one test | `178639959`, pushed |

## In flight (the A13 solver queue)

| lane | items |
|---|---|
| A13-LRA | ADR-2146 tableau admission on nonzeros, ADR-2147 the disequality split lemma (s5/s6) |
| A13-NIA | ADR-2148 lemma emission separated from the refine share (s7) |
| A13-QUANT | ADR-2149 nested-binder activation: fixtures, per-core split, lever OFF, 53-core sweep with a threshold (s6 spare cores) |
| AX-CACHE | Axeyum | item 8 done: the canonical constraint cache in the engine, OFF (ADR-2144); 49 % hits on a real driver session, flat QF_BV A/B | `1f23fa26a`, pushed |
| AX-WARM2 | Axeyum | the warm residual: keep surviving scopes' trail across solves, **ON** (ADR-2145 accepted); replayed session 1.21 → 0.45 s; new incremental z3 fuzz in the hook | `43f1e0f90`, pushed |
| AX-BOARD-2142 | Axeyum | the user's question: the ADR-2142 fix on the 16-division board is +8 stable gains, 0 losses, 0 flips (QF_UFLIA +5, QF_ABV +1, QF_BV +1, QF_NIA +1); QF_ABV decided files 2× faster | `5d21c9db7` |
| GL-REPIN | Glaurung | pin → `11b895a35`; DptfDevGen sizing 59.5 s → 6.0 s, 0 Axeyum splits; `GLAURUNG_AXEYUM_MODEL_PREFERENCE` (item 4; solver-035) | `12a8c088` on local `master` |
| GL-CACHE | Glaurung | pin → `43f1e0f90`; warm same-stream 1,516 → 517 ms; the library cache consumed and shown to dominate Glaurung's own (item 5; solver-036); **9 of 10 done** | `af9f826d` |

Next after these, in order: a same-day z3/cvc5 reference board on the parity-lists population (the 09-14 totals differ in four divisions' membership); Glaurung's ADR-0272 campaign re-registered with a work-bounded budget (the default-backend decision); the defects pipeline over a real C library; cindergraph's `for (;;)` empty-body policy needs a Joern run; Glaurung's `benches/ir_dataflow.rs` is broken on master.

## Round two (after round one lands)

| lane | repo | items | depends on |
|---|---|---|---|
| CG-OPS | cindergraph | 3 (typed operations export) | CG-EXPORT merged (one lane per foreign repo at a time) |
| GL-SIXCELL | Glaurung + `scripts/run-glaurung-six-cell-neutral.py` | 3 (the timing campaign) and Axeyum 14 | GL-PIN merged |
| AX-CACHE | Axeyum | 8 (canonical constraint cache in the incremental engine) | AX-POLICY merged (same file) |
| AX-LIFTER | Axeyum | 10, 11, 12 (loop unrolling, more sinks, real inputs) | AX-BINDINGS merged; CG-EXPORT's attributes reduce the lifter |
| AX-GATE | Axeyum | 16 (wire `check.py` into a gate) | cindergraph `__version__` and a pinned dependency |
| A13 | Axeyum | 15 (the solver queue) | last, per the user's ordering |

## Merge discipline

Axeyum lanes: verify on the branch (battery clippy, workspace check, the
suites the lane names, fmt, hygiene, gating, anchors, registry, links, PLAN
and ADR index current), merge `--no-ff -F msgfile`, regenerate PLAN.md and the
ADR index on conflict, run the cheap gates, push in a batch. Foreign lanes:
merge the branch into the clone's default branch locally after the same
verification in that repo's own terms; pushing those two repositories is the
user's call and is not done by this coordinator.
