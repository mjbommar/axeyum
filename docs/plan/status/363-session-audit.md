# 363 — session audit (adversarial review of the 2026-08-29/30 coordinator claims)

<!-- plan-section: lane-status -->

**Status:** complete. Read-only audit lane; it wrote only its own report and
controls, and edited no fact, proof or gate.

**Deliverable:** [`docs/research/11-design-review/2026-08-30-session-audit.md`](../../research/11-design-review/2026-08-30-session-audit.md).

## What it found

Nine claims refuted or shown unverifiable, five gate guards shown to be
survivors, and four headline claims that survived attack.

The three that most change what may be said out loud:

1. **`natural-parity` (10 held-out rows) was never blind.**
   `Nat.even_iff_mod_two_eq_zero` landed five hours before the family was
   preregistered held-out. Identical in shape to the `natural-divisibility`
   amendment made today; undiagnosed. A further **3 of 10** `fermat-numbers`
   rows were established in-tree 21 minutes before draw 7 preregistered them —
   an evaluation test asserts exactly those three propositions by `def_eq` and
   names the Mathlib lemmas in its doc comment.
2. **"IVT is Pareto-dominant" overstates the audit it rests on.** That document
   records three axes where Mathlib wins, one of them "real and permanent", then
   applies a strict dominance test to EVT and a loose one to IVT. Applied
   consistently, IVT is *mutually non-dominated*, not dominant — and its
   dominance failure is the permanent one while EVT's is fixable.
3. **Five gate guards are survivors**, including every guard in
   `check-merge-hygiene.sh` (landed today with zero registered mutation
   controls) and `check-aggregate-scope.sh`'s fail-on-new-divergence guard,
   which can be replaced with `if false` while its registered controls stay
   green.

## What survived

The excluded-middle unprovability result (eleven `Provable` constructors read
out of the kernel environment are exactly the IPC natural-deduction rule set;
`Formula` has no `top`; strict positivity is checked; 50 declarations
axiom-free; the checker discriminates in both directions),
`Nat.totient_mul_of_coprime` (coprimality load-bearing and pinned by an
`m = n = 2` negative control, numerics re-run rather than inherited), the
per-prelude axiom table measured on a freshly built binary with four fail
directions tested, and the ledger histogram re-derived independently twice.

## Follow-on work this lane deliberately did not do

Amending `natural-parity` and the three `fermat-numbers` rows (ADR-0542 repair
is by amendment, never deletion); registering mutation controls for
`check-merge-hygiene.sh`; ratcheting `check-cas-substance.py`'s headline count;
fixing `strip_wrappers`' quote-blind split in `check-aggregate-scope.sh`; adding
`hooks/*` to the shell-antipattern scan. Each belongs to a lane that may write.
