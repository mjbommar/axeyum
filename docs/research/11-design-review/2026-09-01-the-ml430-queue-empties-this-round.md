# The ml430 queue empties this round, and the refill needs two families

**Measured 2026-09-01**, `scripts/check-dispatchable-frontier.py`:

```
open ml430 mirrors: 228
  held-out (blind evaluation, do not dispatch): 185
  mutation negative controls (never closable):   12
  structurally blocked by a divergence:           11
  DISPATCHABLE:                                   20
```

Nineteen of those twenty were dispatched to four lanes this session. **The
frontier floor is 10. After this round it is 1.**

This is not a surprise and it is not a failure of the lanes — it is the
arithmetic of a preregistered population. 185 of 228 open mirrors are
held-out **on purpose**: they are a blind evaluation population and
dispatching one spends it (ADR-0542; one capsule registered against a
held-out row once cost 19 of 76 held-out propositions for a single theorem).
The dispatchable set is the small remainder, and it drains.

## What the refill screen says

`scripts/propose-nursery-refill.py --remeasure` (the un-remeasured run FAILS
on R2 stale-snapshot and R4 module-already-drawn — `Mathlib.Data.Int.Fib.Basic`
and `Mathlib.Data.Nat.Fib.Basic` are already owned):

```
survivors      2260 across 88 module(s)
READY FAMILIES 3 (>= 10 unused survivors, not already owned)
      37  Mathlib.Data.Nat.Log
      18  Mathlib.Data.Nat.Bitwise
      15  Mathlib.NumberTheory.FactorisationProperties
the frontier floor is 10, so a draw needs 2 new family(ies)
```

Three hygiene-clean families, and a draw of two clears the floor. **The tool
is explicit that this is an upper bound, not a count of drawable families** —
these are not screened for R9 contamination or R11 adjacency, and draw 10 was
DECLINED against this same shortlist (ADR-0900).

## Why the draw must wait for two lanes to return

Two of the three candidates are **contamination-exposed right now**, which is
exactly the ADR-0653 failure:

- `Mathlib.Data.Nat.Bitwise` — the `nat-size-squarefree` lane is landing
  `Nat.size` / `Nat.bit` work as this is written.
- `Mathlib.NumberTheory.FactorisationProperties` — the same lane holds
  `F:ml430-nat-squarefree-ext-iff-7218327d`.

ADR-0653's measurement: a lane sent to unblock a family declared the
construction **and seven supporting theorems**, five carrying exact Mathlib
mirror names, and R9 correctly refused the draw as not blind. The sibling lane
that declared the construction ONLY survived at 0 of 11. Same brief, same
session, opposite outcome.

So the sequence is: let those lanes return, screen the two exposed families
against what they actually declared, then draw. **A readiness figure measured
before an unblock exists is a figure about a different tree** — ADR-0645's
`0 of 18` was honest when written and false by the time it was used.

`Mathlib.Data.Nat.Log` (37 survivors, the largest) is not touched by any
running lane and can be screened now. Note one thing a screener will hit:
our `Nat.log` is a **fuel** construction (`log b n := logAux b n n`,
`nat_prelude/log.rs`) and `nat_prelude.rs:3537` already records that
**Mathlib's `Nat.log` recurses on `n / b`**, which is a different recursion.
Whether that blocks a given mirror is the per-statement mirror-flip question,
not a blanket verdict — and this repository has now mis-sized that same
question three times in a row on `Nat.fastFib`, in three different directions.
