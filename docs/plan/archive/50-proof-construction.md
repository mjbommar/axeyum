# Lane: proof construction

<!-- plan-section: lane-status -->

**Lane extension — from verification to proof (2026-08-12).** The general-`k`
shell lower bound became a **theorem with a written, reviewed proof** (for
`a >= 2`, `gcd(a,b) = 1`, `b < a`, `k >= 2`), which with a closed-form
monochromatic witness for every `b > a`, `k >= 3` gives the characterisation
**solution-free iff `b < a` or `k = 2`**. axeyum's in-tree Lean kernel checks
9 `forall`-quantified theorems over `N` with **zero axioms**, and the algebra
is verified by axeyum's own CAS. Not claimed: no upper bounds; not tight at
`k = 5`; the Lean export has **not** been checked by real Lean. Record, with
three retracted errors:
[`proof-approaches-2026-08-12/`](docs/plan/proof-approaches-2026-08-12/README.md).
