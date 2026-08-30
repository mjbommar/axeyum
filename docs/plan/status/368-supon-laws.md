# Lane 368 — `CReal.supOn` characterization laws

<!-- plan-section: lane-status -->

**Status: IN PROGRESS (started 2026-08-30).**

Goal: make `CReal.supOn` a *characterized* supremum rather than a value with a
convergence law, by landing

1. the **upper-bound law** — `∀ x, le a x → le x b → le (F x) (supOn F a b hab u)`;
2. the **approximate least-upper-bound law** — for every `eps > 0` there is a
   point of `[a, b]` at which `F` exceeds `supOn − eps`. It must stay
   approximate: `CReal.evt_attained_max_decides_sign` refutes the exact form.

No `argmax`-shaped declaration will be added. The supremum VALUE is
constructive; the ARGMAX is not, and that is EVT's row 2.

This entry is a placeholder committed at lane start so a stalled lane can be
resumed; it will be replaced by the real handoff.
