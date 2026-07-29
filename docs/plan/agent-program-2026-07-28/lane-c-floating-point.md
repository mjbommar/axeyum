# Lane C — Floating point (QF_FP / QF_BVFP / QF_ABVFP)

**Ranked-program anchor:** **Rank 0 residual** (the one open soundness-floor
exit criterion) + Rank 6 (P2.8 polish).
**Phase:** [P2.8 FP polish](../track-2-theories/P2.8-fp-polish.md).
**Worktree / branch:** `~/projects/personal/axeyum-fp` / `agent/fp/binary79-residual`.
**Owns:** `crates/axeyum-fp/`, FP routes in `crates/axeyum-solver/src/`, the
**FP regions** of `crates/axeyum-smtlib/src/parse.rs`.
**Blocks on:** Phase 0 T0.2 (which lands this lane's own in-flight ADR-0373).

---

## C1 is the highest-priority task in the whole program

**Rank 0 of the ranked program is "fix both P0 wrong verdicts (soundness
floor)," and its exit criterion 3 is still marked PARTIAL.** Nothing in this
repository ships as "parity" until it closes.

Recap of P0-A (the FP wrong-`sat`): on
`QF_ABVFP/20170428-Liew-KLEE/…/query.26.smt2` (declared `unsat`) axeyum returned
`sat` in 0.12 s while cvc5 1.3.4, Bitwuzla 0.9.1, and the declared status all
said `unsat`. Root cause: the finite add path forced every exact nonzero
cancellation to `+0`; under `roundTowardNegative` IEEE/SMT-LIB requires `-0`.
The same latent convention existed in FMA. **Model replay could not catch it** —
replay evaluates the same lowered FP circuit, so a wrong convention is invisible
to it. That is the structural lesson: *replay checks the lowering, not the
semantics.*

Repair is landed and bit-for-bit `rustc_apfloat` all-mode tests, a minimized
regression, a differential fuzz seed class, and a 600-script cvc5 sweep
(267 sat / 333 unsat, 0 disagreements) are green. Both preserved twins now
return `unsat`.

---

## C1 — Close the Rank 0 exit: full selected-slice revalidation (W1, first)

**Goal.** Re-run the **complete** selected QF_FP, QF_BVFP, and QF_ABVFP slices
on the repaired binary and show DISAGREE = 0.

**Steps**
1. Build release off the post-Phase-0 `main`. Record the exact commit — the
   credited run must be bound to a tested SHA (precedent: `5a9e5335`
   "bind custom FP evidence to tested commit").
2. Run all three selected slices through the SMT-COMP CLI at the committed
   budget. Do not substitute the eight-file Bitwuzla regression slice for the
   selected slices — they are different populations and only the selected ones
   discharge the exit criterion.
3. Score against declared `:status` **and** at least two independent oracles
   (cvc5 1.3.4, Bitwuzla 0.9.1 — both already staged under
   `references/smtcomp-solvers/`).
4. Commit the artifact plus a dated result note; update the Rank 0 §0 exit
   criterion 3 in
   [`full-library-gap-closing-plan-2026-07-22.md`](../full-library-gap-closing-plan-2026-07-22.md)
   from PARTIAL to DONE **only if** the number is actually zero.

**Exit criteria**
- Three committed slice artifacts, DISAGREE = 0, zero replay failures, bound to
  an exact tested commit.
- The soundness-floor claim in `STATUS.md` ("the complete QF_FP/QF_BVFP/QF_ABVFP
  selected slices must return to DISAGREE = 0 before the broader soundness floor
  is called restored") is discharged with the artifact cited.
- If DISAGREE ≠ 0: **stop the lane**, that is a P0 and it preempts everything.

**Size:** M (compute-heavy, low code risk). **Do this before any new FP feature.**

---

## C2 — The 18–20 non-decisions: attack the SAT search, not the split

**Goal.** Decide the residual of the frozen 108-family binary79 diagnostic
(currently 88 correct / **18 unknown** / 2 outer timeouts / 0 wrong).

**Key measured fact, already established.** All the non-decisions **reach pure
BV after FP lowering.** So this is no longer an FP-semantics problem — it is a
BV search problem wearing an FP hat. Two candidate mitigations have already been
tried and **rejected**, and this lane must not re-litigate them:

- **ADR-0371 rejects** post-deadline definite-result retention — it produced
  zero paired decision gain.
- **ADR-0372 rejects** serial splitting of the representative prefix-sum
  counterexample — the three branches take ~0.205 s + 0.096 s + 2.893 s
  (3.194 s total) versus 1.70–1.80 s monolithic, and the split returns
  `unknown` at the two-second gate.

STATUS names the next move explicitly: **target the hard third ordering
obligation itself, or the underlying SAT search. Do not widen the rejected
split.**

**Steps**
1. Isolate the hard third ordering obligation as a standalone BV query and
   commit it as a benchmark.
2. Profile it: encoding size, CNF variables/clauses, where the CDCL time goes.
3. Decide the lever — this is likely a **Lane F** conversation (preprocessing
   P1.2, inprocessing P1.1, or SAT-core P1.3). Coordinate rather than building a
   private FP-only path.
4. Whatever lands, the credit is only for exact measured gains — the 108-family
   diagnostic is a *diagnostic*, and only format-boundary gains get credited
   (that discipline is why ADR-0368 credited 4 rows out of an 83-correct run).

**Exit criteria:** the 18 unknowns drop with zero wrong and zero retained loss;
the two outer timeouts are either decided or shown to be host contention (a
contention timeout that passes in isolation is not a capability regression, but
it must be demonstrated, not assumed).

**Size:** L. **Coordinate with Lane F before writing code.**

---

## C3 — Preserve the 34/34 ESBMC set as a no-loss gate

**Goal.** Turn the current best result into a ratchet so it cannot silently
regress.

**Current state.** The serial five-second ESBMC population is 34/34 declared/Z3
UNSAT, DISAGREE = 0, zero errors, zero replay failures; the four former
residuals take 1.609–3.948 s. It was reached by ADR-0367's fail-closed
shared-antecedent disjunction split (one large root, 4–16 unique negated
implications, one common guard, one global deadline, no recursion, mandatory
original-root replay for SAT).

**Steps**
1. Add the 34-file population as a committed no-loss regression gate.
2. Note the constraint: parallel throughput is **not claimed** — two parallel
   attempts were invalidated by host contention and produced no artifact. The
   gate must be serial, or the gate is noise.
3. Do **not** widen ADR-0367's split. Its admitted class (4–16 obligations, one
   exact antecedent) is deliberately narrow and was preregistered before gains
   were observed.

**Exit criteria:** a serial gate that fails if any of the 34 regresses;
documented runtime envelope; wired into the appropriate `just` recipe.

**Size:** S. Cheap and high-value — do it in W1 alongside C1.

---

## C4 — Rotate back to the measured SMT-LIB residue map

**Goal.** Stop optimizing the ESBMC/binary79 clusters and select the next
*distinct* current-code residue cluster from the measured library.

**Why.** STATUS says it plainly: *"rotate back to the measured SMT-LIB residue
map … select the next distinct current-code residue cluster; do not widen the
split or treat this as the credited selected QF_FP/QF_BVFP/QF_ABVFP rerun."*
QF_FP is 40,407 library benchmarks and the curated row is 16/16 — the curated
row is not telling us anything anymore.

**Steps**
1. Consume Lane D's per-logic residual data once QF_FP is reached (or build a
   curated slice from the staged library if D has not got there).
2. Cluster the declines by operator/format/rounding-mode shape.
3. Pick the largest cluster that is *not* binary79 and *not* ESBMC.

**Exit criteria:** a committed FP residue census; the next increment is selected
from it with a named row count.

**Size:** M. **Gated on:** C1 (do not measure on an unvalidated binary).

---

## C5 — FMA for custom formats: deliberately closed

**Status: CLOSED, and it stays closed until demand is measured.** ADR-0368/0369/
0370 admitted binary79 add/sub/mul, division, and sqrt respectively. FMA remains
fail-closed **because the frozen selection contains no binary79 FMA demand.**

Reopen only if C4's residue census shows real FMA demand with a row count. If it
does, follow the same pattern: private `rustc_apfloat` oracle over all five
rounding modes, thousands of structured + random all-mode cases, neighboring-
encoding rejection, and a preregistered ADR — *before* observing gains.

**Symbolic custom formats outside the admitted operators remain fail-closed.**
That is the correct default; do not relax it opportunistically.

---

## Lane C rolling exit

> The complete selected QF_FP / QF_BVFP / QF_ABVFP slices return DISAGREE = 0 on
> the repaired binary (Rank 0 exit), and the QF_FP residual is being chosen from
> a measured library census rather than from the two clusters already optimized.

## C0 — Finish the ADR-0373 bound (blocks the route landing)

**Status: merged onto `integration/fp-adr0373-20260728` (`0a37ef2b`), held off
`main`.** Full detail in the
[Phase 0 result note](../phase0-integration-result-2026-07-28.md#6-why-fp-ground-div-did-not-land).

The route's **soundness core is clean** — top-level conjuncts only, `Unsat`-only,
a checked `non_nan` precondition before `nonnegative` (closing the vacuous-truth
trap for NaN), and RNE-only with no subtraction and no mixed signs, which makes
the 2026-07-22 exact-cancellation P0 class structurally unreachable. An
independent 1,800-case differential fuzz against z3 fired 86 times, agreed 86/86.

It is held on **availability**. `normalize_source_fp_expr` substitutes each
`let`-bound value at every use, so `k` nested bindings that each mention the
previous one twice emit `2^k` nodes. This is at *parse* time, where the solver
timeout does not apply.

A partial fix is on the branch: a work budget charged during construction, plus
a `source_mentions_fp_add` pre-gate so QF_BV/QF_ABV BMC output stops paying a
normalizing clone. Measured under a 6 GiB `mem-run.sh` cap, 4/8/12/16/20 nested
bindings now decline cleanly — but **24 still aborts on allocation** from a
1,928-byte script.

**Where to pick it up.** Instrumentation shows the four small assertions
normalize with 99,990 of 100,000 budget remaining, and the fifth dies *inside*
`normalize_source_fp_expr` without returning — the `checked_sub` charge is not on
the path that allocates. Two suspects, in order:

1. `let mut extended = environment.clone()` runs at every `let` level, never
   charged.
2. `environment.get(atom).cloned()` materializes the subtree *before* the budget
   is charged. Charge must precede allocation: look up, count, charge, then clone.

The committed test is capped at 20 bindings so it passes honestly. **Do not raise
that cap or land the branch until 24+ declines.**

Then also address, from the same review: duplicate `:named` bindings are silently
rebound (`parse.rs:6184`), which this route turns into a wrong `unsat` on
non-conforming input; the negative controls assert only the internal flag and
never an end-to-end `sat` verdict; and there is no fuzz generator for the route.

---

## In-flight declarations

*(`parse.rs` FP-region announcements go here. Lane B holds priority on
conflicts.)*

- ADR-0373 source FP prefix monotonicity — **held**, see C0. Lives on
  `integration/fp-adr0373-20260728`; touches `parse.rs` and
  `axeyum-solver/src/smtlib.rs`. Its `parse.rs` conflict against the landed
  strings work was exactly one `Script` field insertion, resolved by keeping
  both fields.
