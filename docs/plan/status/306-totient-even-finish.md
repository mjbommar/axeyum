# Lane: totient-even-finish — `Nat.totient_even` closed, two mirrors flip, one still open

<!-- plan-section: lane-status -->

**DONE for this dispatch (`totient-even-finish`, 2026-08-29).**

## The task

Finish `Nat.totient_even` from `docs/plan/status/299-totient-even-exec.md`'s
verified general lemma (`Nat.countRange_reversal_even`), then land the three
mirrors it unblocks per `totient_lemmas.rs`'s module doc:

```
F:ml430-nat-totient-even-28e0415f
F:ml430-nat-odd-totient-iff-b6a6596f
F:ml430-nat-odd-totient-iff-eq-one-d0491d84
F:ml430-nat-totient-coprime-totient-iff-3932cf83   (half)
```

## Result: three of four closed, one left open with a concrete plan

- **`F:ml430-nat-totient-even-28e0415f`** — `proved`, `kernel-lean`,
  `axiom_footprint: []`.
- **`F:ml430-nat-odd-totient-iff-eq-one-d0491d84`** — `proved`, same route
  class.
- **`F:ml430-nat-odd-totient-iff-b6a6596f`** — `proved`, same route class.
- **`F:ml430-nat-totient-coprime-totient-iff-3932cf83`** — still `open`. See
  "What's left" below; the plan is concrete but was not attempted this
  session (budget).

## `Nat.totient_even` — the bug the exec lane's build could not have caught

The general lemma `Nat.countRange_reversal_even` (`count_range_reversal.rs`,
landed by `totient-even-exec`) needed no changes. Wiring it to `totient`
needed:

Detail moved to [`../notes/306-totient-even-finish.md`](../notes/306-totient-even-finish.md).

