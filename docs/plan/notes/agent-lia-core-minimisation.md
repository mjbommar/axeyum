# Notes: agent-lia-core-minimisation

Detail moved out of [`../status/agent-lia-core-minimisation.md`](../status/agent-lia-core-minimisation.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **The diagnosis's A/B reproduces**: identical baseline (92), +20 here against
  its +17 on a more loaded sweep.
- **The shipped version strictly dominates the constant bump** — every file the
  bump decides, plus two more, losing none, while keeping the memory protection.
- The decline it targets (`retained N literals in unminimized theory cores`)
  occurs 31 times in the baseline arm and **0 times in 400 patched runs**. The
  QF_UFLIA files that still decline now fail on the *pre-SAT skeleton envelope* —
  a different constant, the diagnosis's separate `S2` class, and the next
  increment on this route.
- 7 of 8 guard mutations kill **exactly one** test; the survivor is a pre-existing
  arm whose unreachability is documented in the test rather than papered over.
- The control's single loss re-decides `unsat` on **all three** arms in isolation
  — but the shipped arm is ~**11 %** slower on that file, which on a loaded box
  pushed a 15-second file past the external kill. The change costs measurable
  time on QF_IDL and buys nothing there; that is what the control shows.

Capability ratchet (`progress_frontier`, `--features full`, 10 tests, 0 failed):
no REGRESSION on any family, and the reference frame reports **scale 1.09x–1.14x**
at load 3.1–4.2, so nothing is NOT COMPARABLE or ADVISORY. `lia_cuts` — the family
whose engine this touches — sits at 35 against a floor of 26. No baseline raised.

Not a parity result: the reference here is z3 4.13.3, cvc5 is absent on this
host, and only `scripts/parity-run.sh` may move a `PARITY.md` number.

Full method, controls and per-file data:
[the budget-driven theory-core minimisation note](../../research/05-algorithms/budget-driven-theory-core-minimisation-2026-08-21.md),
[ADR-0538](../../research/09-decisions/adr-0538-theory-core-minimisation-is-rationed-by-oracle-calls-not-by-core-width.md).
