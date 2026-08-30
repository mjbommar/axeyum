# Lane: nat-fastfib-minfac — `Nat.fastFib_eq` and `Nat.coprime_of_lt_minFac`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-fastfib-minfac, 2026-08-29).** Two
independent ml430 facts, briefed together. One closes with real new content
under its own name (not a flip); the other is sized and left open with a
precise reason, per the brief's explicit "one of two is a good outcome"
bar — but the one that closed does the harder of the two proof arguments the
prior lane (`docs/plan/status/241-nat-minfac-relprime.md`) sketched and left
undone.

## `F:ml430-nat-coprime-of-lt-minfac-0f79bdba` — closed via a NEW fact, not a flip

`docs/plan/status/241-nat-minfac-relprime.md` already established (reading
Mathlib's actual source, not inferring) that this mirror must stay `open`:
Mathlib's `Nat.minFac` is well-founded recursion on a `sqrt n`-bounded
measure that skips even candidates and exits early once `k*k > n`; this
repository's `Nat.minFac` (`min_fac.rs`) is fuel-STRUCTURAL recursion
scanning every candidate `2, 3, 4, …` with no skip and no early exit. Same
value at every `n`, different construction — the `Nat.multichoose` case in
CLAUDE.md's mirror-flip criterion, not `Nat.descFactorial_of_lt`'s. That
lane's own handoff sketched exactly the two pieces still needed and sized
them as "further, separate work." This lane built both:

Detail moved to [`../notes/250-nat-fastfib-minfac.md`](../notes/250-nat-fastfib-minfac.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-fastfib-minfac | `Nat.minFacAuxMinimal`/`Nat.min_fac_minimal_of_two_le`/`Nat.coprime_of_lt_min_fac`; new fact `F:nat-coprime-of-lt-minfac`; `F:ml430-nat-coprime-of-lt-minfac-0f79bdba` confirmed staying `open` (not flipped) |
| 2026-08-29 | nat-fastfib-minfac | `F:ml430-nat-fastfib-eq-cde11774` sized and left `open`: needs a new binary/well-founded recursion combinator this prelude does not have yet (not a same-day slice); doubling identities are free from `fib_add(n,n)` once attempted |
