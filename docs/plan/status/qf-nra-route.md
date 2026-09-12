# Lane: qf-nra-route — why QF_NRA declines, on all 77 winnable files

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, qf-nra-route, 2026-09-12).**

**Task.** QF_NRA is the largest undiagnosed gap on the 2026-09-11/12 head-to-head
board: axeyum 117 of 200, z3 187, cvc5 186, with **77 winnable** files (we return
`unknown`, a reference decides). z3 does them in a mean of 1.31 s, so it is not a
speed problem. Census all 77 — not a sample — find the largest cause, and fix it
only if a sound fix exists.

## The census — all 77, 100% reason coverage

[`bench-results/qf-nra-route-20260912/`](../../../bench-results/qf-nra-route-20260912/README.md)
(`README.md` = population + method + result, `census-77.tsv` = per-file rows,
`winnable-77.txt` = the pinned list). All 77 ran to completion inside a
180 s wall around a 24 s budget: **0 killed, 0 reasonless rows**.

| cause, from the solver's own `give-up detail` | files |
|---|---:|
| **`ERROR: unsupported by backend: QF_LRA: nonlinear real multiplication`** | **20** |
| `preprocessed dispatch timeout after reduced solve` | 18 |
| `nonlinear abstraction: refinement reached a fixpoint without deciding` | 16 |
| `nra lazy SMT: wall-clock timeout reached` | 7 |
| watchdog fired before the worker thread returned | 5 |
| `nonlinear abstraction: … past the consuming engine's capacity … (needs nlsat/CAD)` | 4 |
| `lra: Fourier–Motzkin elimination exceeded the wall-clock / size budget` | 3 |
| `nonlinear abstraction: refinement round bound reached` | 2 |
| online CDCL(T) LRA model did not replay | 1 |
| integer literal outside the `iN` reference range (ADR-1702) | 1 |

Three findings the numbers force:

1. **The largest class is a defect, not a capability wall.** 20 of 77 are a
   `SolverError::Unsupported` escaping the dispatcher, from one un-rewritten
   refinement lemma in `solve_relaxation`. Localised with the admission lever,
   not argued.
2. **The second-largest is an opaque relabel.** 18 of 77 say only that the clock
   ran out, because `dispatch_reduced` REPLACES the reduced solve's own reason.
   The same sentence is the top named `Timeout` detail in two other censuses
   (QF_NIA 41 of 110, all-divisions 30 of 260).
3. **`last` would have blamed the string engine.** 52 of 77 name
   `fd:bounded-completeness-unsat` as the last route. `bound_by` says `nra` on
   47. Classifying by `last` — refuted here before — would have named a string
   front-door wrapper as the cause of two thirds of a nonlinear-arithmetic
   division.

**22 of 77 are a genuine capability wall** and say so in their own words: *"this
needs a nlsat/CAD engine"* (ADR-0058 Phase C/D). `mbo_E1` projects 771
cross-products to 36,945 linear-real atoms against a capacity of 1,024. This
lane does not attempt that.

## The fix, and what it measured

[ADR-1925](../../research/09-decisions/adr-1925-an-engine-internal-unsupported-is-a-decline-and-a-relabel-must-carry-what-it-replaces.md).
One root cause and two rules:

- **Root cause.** `solve_relaxation`'s refinement point lemma now refines over
  the **abstracted** operands — rewritten through the product→fresh-variable map
  *before* their values are read. Its guard skipped an operand that *is* a
  product but not one that *contains* one, and `(+ c (* x (* x k)))` — the
  MetiTarski/Horner shape — is the second kind.
- **Rule 1.** An `Unsupported` raised inside a theory engine is a decline, not
  an error out of the dispatcher. Stated honestly as a safety net with **no
  current exerciser**: the root-cause fix removed the only known producer.
- **Rule 2.** A budget relabel appends the reason it replaces. Prefix
  byte-identical, so existing consumers still match.

### The A/B: 117 → 117, and that is the finding

200 files, interleaved, both arms back to back on the same cores with the order
alternating 100/100, 24 s budget, box idle. Raw rows in `ab-200.tsv`.

| | base | treat |
|---|---:|---:|
| decided | **117 / 200** | **117 / 200** |
| gains / losses / flips | — | **0 / 0 / 0** |
| runs killed by the wall | 0 | 0 |
| wall | 1,092.0 s | 1,210.9 s (**+10.9%**) |

The base arm reproduces the board's QF_NRA row exactly. **Disagreements: 0** —
every decided verdict on both arms checked against the declared `:status` (116
of 117) and both reference columns (233 checks).

So the largest named cause of the gap, 26% of it, was a defect, and repairing it
**moves zero files**. An error and an `unknown` are both "not decided" to a
scorer. The +10.9% is concentrated exactly where predicted: files that used to
abort early now run the relaxation to its fixpoint or its budget.

**A variant that scored +1/−1 is recorded and NOT shipped.** Rewriting the
finished lemma instead of the operands gained
`exp-problem-10-3-weak-chunk-0081.smt2` (`unsat`, 7.0 s) and lost
`sin-problem-7-chunk-0353.smt2` (`sat` in 1.7 s → `unknown`). Both movers were
freshly re-verified against both references at 120 s: 0081 is declared/z3/cvc5
`unsat`, 0353 is declared/z3/cvc5 `sat` — so the gain was correct and the loss
was real. The shipped version is the one incremental linearization prescribes
(the lemma must exclude the *current* spurious point), not the one that scored
better. Which point the lemma pins is a real degree of freedom, worth one file
in each direction here.

### The re-census: what the two repaired labels were hiding

Same 77 files, shipped binary (`census-77-after.tsv`). `Error` **20 → 0**;
the 18 causeless timeouts **→ 0**, replaced by the reason each was carrying.
**Thirteen of the eighteen were the CAD wall** — cross-products projecting past
the consuming engine's atom capacity, reported for months as "the clock ran out".

| the gap, on the repaired diagnosis | files | share |
|---|---:|---:|
| **the linear abstraction's own boundary** (fixpoint 27, capacity 13 + 4, round bound 2) | **46** | **60%** |
| clock (lazy SMT 12 + 4, watchdog 5, Fourier–Motzkin 3, dispatch budget 2) | 26 | 34% |
| other (wide integer literal 3, model replay 2) | 5 | 6% |

Before: 26% error, 23% "it ran out of time", 21% relaxation boundary. After,
**60% is one thing and it names itself** — the capacity rows' own decline text
says this *"needs a nlsat/CAD engine"*. That is ADR-0058 Phase C/D, now the
measured majority of the division's gap rather than an inference from a fifth
of it. **This lane does not attempt it**, and says so: no bound tuning reaches
`mbo_E1`'s 771 cross-products → 36,945 atoms against a capacity of 1,024.

## Gates

Every count read off the run:

- `-p axeyum-solver --features full`: `nra` 37, `nra_real_root` 86,
  `nra_no_hang` 3, `nra_census_levers` 8, `cas_ideal_route` 36, `nra_sos` 9,
  `nra_fbbt_route` 6, `nra_interval_refutation` 6, `ufnra_route` 7,
  `corpus_regression` 2, `nra_point_lemma_abstraction` 1,
  `preprocessed_timeout_carries_the_reason` 2 — all green.
- **`--features z3` differential fuzzes, the only independent-oracle check on
  this route**: `nra_differential_fuzz` 3 passed (1,285 s, 2,000 instances),
  `qf_ufnra_differential_fuzz` 1 passed. DISAGREE = 0.
- `progress_frontier --features full -- --test-threads=1`: **12 passed**, no
  REGRESSION, run on an idle box (load 0.77) so the reference frame holds.
- `clippy -p axeyum-solver --all-targets --all-features -D warnings` green;
  `check --workspace --all-targets --all-features` green.
- **Mutation controls, both `killed 1`**: `nra-point-lemma-abstraction`
  (delete the operand rewrite), `preprocessed-timeout-reason` (drop the carrier
  phrase). **Two fixtures were REJECTED by the control before one worked** and
  both rejections are recorded in the test's module docs: `y*(1 + x*x) = 7` over
  a box is decided outright by `decide_real_poly_constraint` so the relaxation
  never ran, and a front-door version of the surviving fixture passed with the
  guard deleted because rule 1's safety net caught the error one layer up.

**Pre-existing red, NOT this lane**: `--test unknown_reason_coverage` fails 2 of
7 (`an_errored_dispatch_publishes_the_routes_that_ran_and_the_error_text`,
`an_unsupported_decline_carries_the_refusing_calls_message`). Verified identical
— same two names, 5 passed / 2 failed — on a clean `lane-snapshot.sh main`
snapshot at `84f9e7d19` carrying none of this lane's changes. Its QF_DT fixture
now produces `backend failure: preprocessed sat model does not replay as
emitted: assertion #7` rather than the `unsupported` the test looks for. This
lane did not cause it and did not fix it.

**Not run**: the full `just check` / `./scripts/check.sh` aggregate.

<!-- plan-section: landed-changes -->

| 2026-09-12 | qf-nra-route | the 77 winnable files resolved and checked, committed before any result | `39ad0135d` |
| 2026-09-12 | qf-nra-route | census of all 77: the biggest cause is an escaping `Err`, not a capability wall | `730b7858d` |
| 2026-09-12 | qf-nra-route | the point-lemma abstraction rewrite, the `Unsupported`→`unknown` net, and the relabel carrier; two mutation-controlled tests | `63b4ea0f5` |
| 2026-09-12 | qf-nra-route | workspace clippy on the new test | `99819fa45` |
| 2026-09-12 | qf-nra-route | ADR-1925 and the regenerated ADR index | `f4363c1a0` |
| 2026-09-12 | qf-nra-route | refine over the ABSTRACTED operands — rewriting the finished lemma lost a `sat` | `3360880be` |
| 2026-09-12 | qf-nra-route | the 200-file A/B: 117 → 117, 0 gains, 0 losses, 0 flips, 0 disagreements | `30c21219e` |
| 2026-09-12 | qf-nra-route | the re-census: 13 of the 18 opaque timeouts were the CAD wall | `c10ba60fc` |
