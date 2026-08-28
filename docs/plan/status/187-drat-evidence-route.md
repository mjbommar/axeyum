# Lane: drat-evidence-route — route the `unsat` evidence path off the quadratic forward DRAT checker

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, drat-evidence-route, 2026-08-28).**

**The question.** Why did the evidence/certificate path call `check_drat` — the
forward reference checker, superlinear in proof length — when
`check_drat_backward` and `elaborate_drat_to_lrat_backward` (ADR-0382, ~66x)
had existed since 2026-08-12? Was there a deliberate reason?

**The answer: no. It is precedence, not a decision.** ADR-0382 was written to be
additive ("`check_drat` must not change, because it is the reference; the new
checker must be additive") and its item 9 explicitly deferred re-basing the LRAT
elaborator as "an obvious follow-on ... deliberately not in this slice". The
follow-on was never taken. `git log -L` dates the accepting call sites in
`evidence.rs` and `proof.rs` to **2026-06-13**, two months before the fast engine
existed. No ADR, comment or test pins them. The backward engine is meanwhile used
throughout the campaign tooling, `cube.rs`, `weighted.rs` and half a dozen
examples — everywhere except the certificate route.

**Why the naive fix was still wrong.** Swapping in `check_drat_backward` at the
accepting sites is exactly what ADR-0382 refused, and for a good reason: it moves
the trusted base from a few dozen readable lines to ~2,700 lines of watched
literals and clause arenas. Speed bought with assurance is not a trade this
repository makes.

**What landed instead (ADR-0613): the fast engine became a producer.**
`certify_unsat_via_lrat` runs `elaborate_drat_to_lrat_backward` as an
**untrusted** emitter of antecedent hints, then has `check_lrat` — small,
search-free, linear — verify those hints against the formula directly. A
`Certified` is discharged by `check_lrat` alone, so a bug anywhere in the
backward engine yields a decline, never a wrong `unsat`. The trusted base does
not grow; it **shrinks**, from a checker that searches for a refutation to one
that is handed it. `check_drat_backward` appears only in *rejecting* position
(the DRAT conjunct in `UnsatProof::recheck`), where it can reject and never
accept. The forward reference is untouched and remains the accepting authority
whenever the LRAT route declines (a RAT lemma, or a checking budget too small for
a stage that cannot be interrupted).

**Measured, `smtcomp_cli --evidence --progress`, release, contended host:**

| query | before | after |
| --- | --- | --- |
| `neg-fp8-add-monotone-rne.smt2` | 25m46s (ledger figure) | **5.028 s end to end**, of which 2.555 s checking; `certified=1 recheck=ok` |
| `neg-fp16-add-monotone-rne.smt2` | decide 11.09 s; check ~95 steps/s -> ~2.4 h extrapolated, never observed to finish | **not completed in this lane's bounded run** — see below |

**The fp16 number DID NOT RUN to completion here.** The run was started with a
540 s internal budget and the lane's shell moved it to the background at 120 s;
the lane does not report a background result as a measurement. Treat fp16 as
**unmeasured after this change** until someone runs it in the foreground and
records the number. `F:fp16-add-monotone-rne` is deliberately left `open` — its
measured obstruction is worth more than an overclaim, and flipping it requires a
checking route that actually completes with a `checker_command` that fails when
the claim is false.

**Soundness discipline.** The load-bearing fixture is over **satisfiable**
formulas, because on an unsatisfiable one every accepted proof is sound
vacuously. `never_certifies_a_satisfiable_formula` attacks random SAT instances
(counter asserted `>= 20`) with a borrowed refutation, a truncated proof, a bare
unjustified empty clause and random garbage ending in an empty clause. The
bare-empty-clause shape is the one that kills a missing `check_lrat` gate:
`elaborate_drat_to_lrat_backward` answers `Ok(vec![])` when there is no
refutation, and an empty LRAT proof is `Ok(false)` to the trusted checker, *not*
an error — so a composition returning `Certified` on elaboration success alone
would certify a satisfiable formula from an empty proof. Mutation-verified: that
is exactly what the mutant does.

**Mutation results, stated precisely rather than rounded to "exactly one":**

| guard deleted | tests that died |
| --- | --- |
| the `check_lrat` gate | 3 — soundness plus two decline-reason precision tests |
| the `check_drat_backward` conjunct in `recheck` | 2 |
| the whole budget gate | 3 |
| the deadline half of the budget gate only | **1** |

Only the deadline half carries exactly one claim, and exactly one test dies for
it. The others kill more than one because the guard carries more than one claim;
saying so is more useful than a number that looks tidier.

**What the next lane needs to know.**

- **The RAT gap is now on the hot path.** `LratStep` cannot carry a pivot or
  negative hint blocks, so a RAT core lemma declines the fast route and drops
  back onto the superlinear one. Our CDCL core emits RUP-only proofs so this is
  rare today, but a future RAT-emitting technique (blocked-clause addition,
  symmetry breaking) would silently lose the whole improvement. The fix is an
  LRAT step that can express RAT — not another checker.
- **The backward stage is not step-interruptible**, so it is admitted only when
  the budget can accommodate it whole. A live deadline admits it and can be
  overshot by that stage's cost; an overshoot that certifies is a genuine
  verification, never a timeout promoted to a pass.
- `CheckingProgress` gained a `BackwardLratCertify` variant reporting exactly
  twice (opening, closing). Any exhaustive match needs an arm; `smtcomp_cli` was
  the only other consumer.

<!-- plan-section: landed-changes -->

| 2026-08-28 | drat-evidence-route | `certify_unsat_via_lrat`: the backward engine emits LRAT hints (untrusted), `check_lrat` verifies them (trusted, search-free) — fp8 evidence 25m46s -> 5.0 s with no move of the trusted base (ADR-0613) |
