# Lane: watchdog-residual — a kill must name the phase it was inside

<!-- plan-section: lane-status -->

**A watchdog kill destroyed its own diagnosis, and the residual was the OTHER
abstractor** (`watchdog-residual`, 2026-09-12). Follow-on to
[`deadline-overrun`](deadline-overrun.md) (`47f902ea1`). **That lane's closing
hypothesis was wrong** and is withdrawn here: it named `lra::solve` on a path
whose deadline was still `None`; on merged main `lra::solve` takes a deadline,
polls both its loops, and its one production caller passes a real one. The
hypothesis came from a `perf` profile, and **a profile answers a different
question from a budget** — cycles concentrate in the callee, the budget is spent
by the caller that loops.

**The instrument first, because the old ones could not answer.** Every
instrument in this tree records at a boundary a stage has already CROSSED, so a
killed run's last word is always the name of something that had finished. On
`QF_UFLRA`'s `cpachecker-induction.minepump_spec1_product56…` the trail ended
with `nra` declining at **38 ms** and then said nothing for 25 s.
`crate::phase_breadcrumb` is a stack pushed on ENTRY and popped on return,
behind an `Arc` on the `live_instruments` board, so the thread enforcing the
wall clock reads it while the worker is still inside the frame. `smtcomp_cli`
prints it as `; partial phase …` under `; partial route-open` — the line that
could only ever ask the question this one answers.

**Four defects, each found by re-reading the phase stack after the previous
fix.**

1. **A membership question answered by running a decision.**
   `ArithAbstractor::ensure_supported_atom` ran a whole conjunctive decision per
   distinct atom and discarded the verdict; every `Unsupported` either route can
   raise comes from its COLLECTOR. `47f902ea1` memoised this from 11,236 calls
   to one per distinct atom — the right guard, and not enough: **540 distinct
   atoms is still 540 whole decisions**, 539 reaching Fourier–Motzkin, inside
   one abstraction build. `lra:certified` 540 → 1, `lra:fm-solve` 539 → 0.
2. **The same DAG tree-walk, in the abstractor nobody looked at.** `c4046c2d6`
   memoised `dpll_t::Abstractor` — the abstractor the `nra` route reaches. The
   `euf` lazy-UF+arithmetic route, where **49 of `QF_UFLRA`'s 51** watchdog
   files are, goes through `dpll_lia::ArithAbstractor`: a different struct, same
   unmemoised recursion over an assertion DAG. Its `atom_of` map reads like the
   memo and is not — it caches the LEAVES, and the sharing is in the Boolean
   structure above them.
3. **`IncrementalArithDpll::new` hardcoded `None`.** ADR-1906's shape a third
   time, in the argument: the CEGAR round held the remaining budget and called a
   constructor whose whole body threw it away.
4. **The one ladder rung that reset the budget.** Every rung of
   `dispatch_uf_fast_paths` derives its config from `ladder_deadline` except
   `check_with_uf_arithmetic`, which took the caller's ORIGINAL config — a fresh
   24 s handed to a route with 6 s of wall clock left.

**What it buys on the file the lane started from**
(`minepump_spec1_product56`, 24 s): the `uf-arith-lazy-overbound` route now runs
to 17,998 ms and **declines in good order** (`reason=budget`) with a detail
naming its own state (`total_rounds=6, atoms=562, min_oracle_calls=1120`), where
before the trail's last word was a route that had returned at 38 ms. Ten
abstraction calls complete where two did not.

**The A/B.** Interleaved per-file against `47f902ea1` — both arms back to back
on the **same pinned core**, arm order alternating by file index, 24 s budget.
Population: every watchdog file in `QF_UFLRA` (51), `QF_LIA` (28) and `QF_IDL`
(19), plus a 60-file control of files the board records us deciding: **158
pairings**. Watchdog kills **92 → 81**, **0** newly killed, **0** verdict
regressions over all 158.

Of the 11 files that stopped being killed, 4 came back with a verdict and 7 now
return `unknown` INSIDE the budget (16.65–24.48 s) rather than at 25.0 s —
which is the contract, not a capability gain, but not nothing either, since a
killed run loses the model, the proof and the evidence it had produced. Three
of those seven are the `32_1_cilled…` family the previous lane left open.

**Two of the four converts were noise, and re-running is what found them.**
Re-run twice more in both arm orders on a quiet box, the two `QF_IDL` files are
decided by the BEFORE arm too, in 6.8–10.9 s; their `unknown 25.03` in the
sweep was the box at load ~100. **Raw 5 converts / 11 freed kills; re-checked 3
converts / 10 freed kills**, all ten in `QF_UFLRA`:

| file | before | after | z3 | cvc5 | `:status` |
|---|---|---|---|---|---|
| `…minepump_spec2_product38…` | unknown 25.01 | **unsat 18.09** | unsat | unsat | unsat |
| `…minepump_spec2_product62…` | unknown 25.01 | **unsat 18.07** | unsat | unsat | unsat |
| `…minepump_spec3_product23…` | unknown 25.01 | **sat 6.31** | sat | sat | sat |

Each convert is confirmed three independent ways, by a cross-checker whose exit
status depends on the finding: a planted wrong verdict on a known file makes it
print `DISAGREE` and exit 1.

The seven freed-but-undecided files were re-run the same way, twice each in both
arm orders: **14 of 14 pairings reproduce**, before 25.00–25.04 s (killed),
after 16.87–24.34 s (the solver stops itself). No flake in either direction.

**The census is not the fix.** 149 files board-wide end in a watchdog kill; that
is how often this happens, not how many a fix wins. The number to quote from
this lane is **3 converts and 10 freed kills**, not 149.

**Gates, with counts, because a feature-gated suite compiles to nothing and
exits 0.** All five z3 differential fuzzes green — `qf_lra` 5,
`simplex_lra_fallback` 1, `qf_uflra` 1, `difference_logic` 4, `qf_lia` 4 (15
tests). This lane touches the LRA/LIA collector entry points and the dispatch
ladder, so they are the gate, not a formality. Beside them: the solver unit
sweep `--lib --features full` **1398 passed**, `corpus_regression` 2,
`smtcomp_cli` 14, and the capability frontier ratchet **12 passed**.

Full note:
[`../../research/03-measurements/the-watchdog-residual-is-the-other-abstractor-2026-09-12.md`](../../research/03-measurements/the-watchdog-residual-is-the-other-abstractor-2026-09-12.md).

**Determinism.** Nothing new reads a clock when no timeout is configured:
`past_deadline(None)` short-circuits before `Instant::now()`, both fragment
probes pass `None` exactly as the calls they replace did, the memo is a
`TermId`-keyed lookup that is only ever `get`/`insert` and never iterated (so no
hash order can reach output), and `phase_breadcrumb::enter` without an installed
board is one thread-local `bool` read. Verified end to end: without `--trace`
the binary's output is the verdict and nothing else.

<!-- plan-section: landed-changes -->

| 2026-09-12 | `3f49aff46` | `crate::phase_breadcrumb`: a phase stack written on ENTRY, published as a live handle to the `live_instruments` board, printed by `smtcomp_cli` as `; partial phase …` on a watchdog kill. Frames on the arithmetic/EUF spine only — never per pivot or per abstraction node. Off without `--trace`. Guards: mutating `innermost` from `last` to `first` kills three tests across two suites, one of which enters and LEAVES a third frame before blocking, so a reader that named the returned one (what every other instrument here would name) fails on exactly the confusion this exists to end. |
| 2026-09-12 | `311fc52cd` | Four deadline-blind phases on the `euf`/`dpll_lia` spine: `lra::atom_in_lra_fragment`/`atom_in_lia_opaque_fragment` answer fragment membership with the collector instead of a whole decision; `ArithAbstractor::abstract_term` is memoised (a timed-out walk is never cached); `IncrementalArithDpll::new_within` takes the caller's deadline; `dispatch_uf_fast_paths`'s eager `uf-arithmetic` rung takes the REMAINING budget like every other rung. The memo's guard counts EXPANSIONS, not seconds — mutation-controlled at 20 levels: 2,621,439 against a bound of 336. The probe guards DERIVE their expectation by running the full decision beside the probe, and assert the case list exercises both sides. |
