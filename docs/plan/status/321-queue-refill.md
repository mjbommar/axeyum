# 321 — queue refill

<!-- plan-section: lane-status -->

## Status

LANDED. The frontier gate now fails at a floor instead of at zero, and there is
a repeatable, gated answer to "can the queue be refilled".

**The gate is RED on this branch, deliberately, at 3 dispatchable against a
floor of 10.** That is the true state of the queue, not a regression. It goes
green when someone authors a draw — which is now two names off a printed list
rather than a hand derivation.

## What was wrong, mechanically

Three candidate causes were on the table. Measured, not assumed:

1. **"The nursery is finite and mostly held-out, so it cannot be refilled."**
   Half right. 45% of every draw goes to held-out (the partition cycle restarts
   at index 0 per draw, so held-out takes `ceil(n/3)`, not a third — the
   committed manifest is 9/6/5 over 20 families). But the pool is not exhausted:
   **2,295 unused propositions survive every screen, across 94 modules, giving
   19 ready families.** A draw of all 19 would add 120 dispatchable rows.
   The queue can be refilled without going near a held-out row.

2. **"The extension pipeline has headroom but nothing runs it on a schedule."**
   This is the real cause, and it is worse than "nothing schedules it":
   **a refill is not a runnable operation at all.** `gen-autogenesis-nursery-
   refill.py` emits `PER_FAMILY * len(FAMILY_MODULES)` rows from two
   module-level dicts. Re-running it unchanged is a byte-level no-op that prints
   `AUTOGENESIS_NURSERY_REFILL_OK` and adds nothing. A draw is a SOURCE EDIT:
   add a family to `FAMILY_MODULES`, add its routes to `FAMILY_ROUTES`, re-run.
   Draws 2, 3 and 4 were all hand-authored on 2026-08-29 and nothing has run
   since.

   The drain rate makes that fatal: draw 4 put 110 non-held-out rows into the
   population and **107 were settled within a day**. The flywheel consumes
   population far faster than a human authors draws, and nothing computed
   whether a draw was even possible.

3. **"The statable screen may be too narrow a word list."** It is not a word
   list. `admissible = env | bridge`, where `env` is 2,207 declarations read
   from `kernel.environment()` and `bridge` is 70 constants DERIVED from settled
   mirrors. Every rejection names a constant this kernel does not declare. Do
   not loosen it — see ADR-0617 for what measuring it did turn up.

## What landed

Detail moved to [`../notes/321-queue-refill.md`](../notes/321-queue-refill.md).

