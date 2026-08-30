# Lane: cas-ledger — registering the four CAS Spivak-spine results, honestly labeled

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, cas-ledger, 2026-08-27).** ADR-0601 requires that
CAS evidence either reconstructs through `Kernel::add_declaration` or is
visibly labeled `cas-internal`. `crates/axeyum-cas/` had landed four results on
the Spivak spine — `mvt.rs` (Mean Value Theorem), `extremum.rs` (polynomial
extremum / EVT), `taylor.rs` (Taylor with Lagrange remainder), and
`partial_fractions.rs` (all four rungs) — and **none were in the fact ledger**,
so ADR-0601's labeling rule was satisfied only by absence. This lane registers
all four as hand-curated (not generated) ledger facts.

## What was registered, and the call on each

All four are **`proof_route: cas-certificate`, classified `cas-internal`**
(no `axeyum-lean-kernel` package is named by any evidence `checker_command`,
so `scripts/validate-facts.py`'s `classify_cas_certificate_checker` puts every
one of them on the honest, weaker side of the split). None reconstructs
through the kernel; none is claimed to.

| fact | module | concrete instance chosen | irrational witness named exactly |
|---|---|---|---|
| `F:cas-mvt-cubic-witness-sqrt3` | `mvt.rs` | `p=x^3` on `[0,3]` | `c = sqrt(3)` |
| `F:cas-extremum-irrational-argmax` | `extremum.rs` | `p=x^3-6x` on `[-3,2]` | argmax `-sqrt(2)` |
| `F:cas-taylor-quartic-lagrange-witness` | `taylor.rs` | `p=x^4`, `a=0`, `n=1`, `b=2` | `xi = sqrt(2/3)` |
| `F:cas-partial-fractions-mixed-general-case` | `partial_fractions.rs` | `(x+1)/((x-1)^2(x^2+1))` | n/a (pure algebra) |

Each cites one existing unit test (not a new derivation), read directly from
source rather than hand-transcribed, matching the convention the prior
`F:cas-ivt-cbrt2-in-1-2` / `F:cas-ivt-sign-bracket-cbrt2-kernel-checked` pair
established (138-bridge-ivt / 141-cas-mvt lanes).

**Zero declined.** All four modules had a shippable, checkable certificate
route with at least one existing test naming an exact, non-trivial (in three
of four cases, irrational) instance, so nothing was skipped.

## The one honesty call this task flagged in advance, applied

Detail moved to [`../notes/145-cas-ledger.md`](../notes/145-cas-ledger.md).

