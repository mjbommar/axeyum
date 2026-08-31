# Lane: unblock-draw-15

<!-- plan-section: lane-status -->

Status: DONE — cycle index 3 is filled. Draw 15 is possible.

ADR-1160. Four draws declined in a row on one constraint: cycle index 3 is a
held-out slot and nothing late-sorting, topically fresh and reduction-blind was
available to sit in it. This lane screened NINE late-sorting candidates against
the real `select()`/`assign_partitions()`/`screen_family()`/
`is_closed_evaluation` — each candidate's constructions simulated into the
environment BEFORE anything was declared — and built the winner.

## What landed

- `DecidablePred.{u}` in the LOGIC prelude (`prelude.rs`), Mathlib's own
  definition with `α` explicit. It goes there rather than in `nat_prelude`
  because `every_nat_declaration_is_checked_and_axiom_free` filters the
  environment on the `Nat.` prefix, so a root-level name declared from there
  would be invisible to the one assertion that reads coverage from the
  environment.
- `Nat.findGreatest` (`nat_prelude/find_greatest.rs`), Mathlib's structural
  recursion with the witness explicit and `Decidable.byCases` in place of
  `ite`. Mirror stays `open` (the `Nat.nth`/`Nat.minFac` criterion).
- Six discriminating evaluation tests (`find_greatest_tests.rs`), each with a
  negative control naming the wrong definition it rules out.
- Environment snapshot refreshed 2593 -> 2625. The regenerated
  `nursery-v2-extension.json` is byte-identical: 0 dropped, 0 added, 0 moved.

**No theorem is declared and no fact is registered** (ADR-0653, and the
precedent of every prior unblocking lane).

## Measured

Post-declaration re-screen against the real 2625-declaration environment, two
independent 4-family layouts, `natural-find-greatest` at index 3 in both:
R5 PASS, R9 0/10, R12 0/10, R11 topic and vocabulary clean on both held-out
families. The only remaining refusal is R11's authorable disclosure — the draw
lane's job.

Kernel: `--lib nat_prelude::` 284 passed / 0 failed (up from 278);
`--lib prelude::` 622 / 0; `--lib find_greatest` 6 / 0.
Gates: nursery OK, dispatch-baseline `--check` OK, refill `--check` OK,
holdout-closed-evaluation PASS, holdout-isolation `held_out=146 settled=0 PASS`
before and after.

## The finding beyond the family

ADR-1115's pre-declaration check is necessary and NOT sufficient.
`is_closed_evaluation` is binder-free by construction, so a `∀`-quantified
DEFINING EQUATION (`f P 0 = 0`) is settled by reduction and reports clean —
measured directly on `Nat.findGreatest_zero`'s own statement. Run the
classifier, then READ the drawn ten for boundary equations your definition will
make `refl`. That reading is what separated `Find` (zero such rows in the ten)
from `Factorization.Root` (three) and `MaxPowDiv` (six).

## Landed changes

| what | where |
| --- | --- |
| `DecidablePred.{u}` + coverage | `crates/axeyum-lean-kernel/src/prelude.rs`, `prelude/prelude_tests.rs` |
| `Nat.findGreatest` | `crates/axeyum-lean-kernel/src/nat_prelude/find_greatest.rs` |
| evaluation suite | `crates/axeyum-lean-kernel/src/nat_prelude/find_greatest_tests.rs` |
| wiring + inventory | `crates/axeyum-lean-kernel/src/nat_prelude.rs`, `nat_prelude/nat_prelude_tests.rs` |
| snapshot refresh | `artifacts/autogenesis/kernel-environment-snapshot-v1.json` |
| decision | `docs/research/09-decisions/adr-1160-the-index-3-slot-is-filled-mathlib-data-nat-find.md` |
