# Budget curve: is the remaining gap engineering, or capability?

**Status: METHOD PINNED, MEASUREMENT IN FLIGHT.** This section was committed
before any number was read, so the protocol cannot be chosen after the data is
visible. Results and the classification follow below as they land.

## The question

Almost everything fixed on 2026-09-08 was a constant factor: a route consuming
24.009 s of a 24 s budget; 97 % of a budget spent on a method with a 0 % success
rate; fourteen files finishing at 24.2 s that now finish at 18.2 s. Constant
factors are exactly what a longer budget buys. So the open question is whether
what remains is more of the same — engineering — or something a clock cannot
reach — capability.

A budget curve separates them, but **only if the reference is on the same
curve.** If our solved count climbs steeply from 24 s to 60 s and the
reference's does not, the remainder is engineering. If both flatten together, we
are missing capability and more time will not close it.

## THE 24 s ROW IS THE HEADLINE. THE 60 s ROW IS NOT A PARITY NUMBER.

`scripts/parity-run.sh`'s own header lists the ways this repository has
historically made a gap look smaller, and one of them is *"a 2-second budget,
where both solvers time out and distance collapses."* **A long budget flatters
from the other end.** If the reference saturates — decides everything it is ever
going to decide — and we keep picking up easy files, the ratio rises while
nothing about the solver got better. The 60 s ratio is diagnostic; it is not a
score.

So, stated in advance and not retrospectively:

- **24 s is the only externally comparable number**, because that is what
  SMT-COMP publishes. Every headline claim in this repository stays on the 24 s
  row.
- The 6 s and 12 s rows exist to show the SHAPE of the left half of the curve,
  not to be quoted either.
- The 60 s row answers one question and one only: *does the count still move?*
- **If a later reader quotes the 60 s figure as our parity number, that reading
  is refused here, in advance, by the lane that produced it.**

## Protocol

Fixed before the run; nothing below was selected after data was visible.

| knob | value |
|---|---|
| harness | `scripts/parity-run.sh` (the committed protocol harness; no second harness was written) |
| budgets | 6 s, 12 s, 24 s, 60 s — `PARITY_BUDGET_S` |
| memory | 8 GiB per file at **every** budget — `PARITY_MEM_GB=8`, unchanged across the curve |
| population | the committed pinned lists, `bench-results/parity-lists/{QF_UFLIA,QF_LRA,QF_LIA,QF_ABV}.txt`, 200 files each, whole list as denominator |
| divisions | the four that moved on 2026-09-08 |
| reference | **run at every budget too** — cvc5 1.3.4 for QF_UFLIA / QF_LRA / QF_LIA, bitwuzla 0.9.1 for QF_ABV, exactly as the harness's own division table selects. No portfolio flags. |
| solver commit | `e99d08848` |
| binary | one `target/release/examples/smtcomp_cli`, built once and copied to every host, so no arm is confounded by a different build |
| budget order | **24 s first**, then 6, 12, 60 — so an interrupted sweep still yields the externally comparable row |

The reference running at every budget is the point of the exercise. A curve of
only our own numbers is unreadable: our count rises with budget for any solver
that is not already saturated, so the rise means nothing on its own. **The
quantity that matters is the ratio at each budget**, and the shape of the
reference's own curve beside ours.

## Machine reality — recorded, not assumed

`s5`, `s6` and `s7` were **not idle** at dispatch. They were measured at
dispatch and again at the end, and both numbers appear in every ledger entry
(`parity-run.sh` stamps them). Each host has 16 cores.

At dispatch, 2026-09-09T02:46:42Z:

| host | load (1/5/15 min) | division | other work on the box |
|---|---|---|---|
| `s5` | 3.04 / 3.08 / 3.00 | QF_LIA | the `parallel-portfolio` lane's `route_solo` per-route oracle sweep — 3 processes at ~100 % CPU |
| `s6` | 3.23 / 3.29 / 3.49 | QF_LRA | same `route_solo` sweep — 3 processes at ~100 % CPU |
| `s7` | 4.09 / 4.14 / 4.06 | QF_UFLIA **and** QF_ABV (separate worktrees) | `route_solo` + `smtcomp_cli --trace` from the same lane, 4 processes at ~100 % CPU, plus a long-running Minecraft `java` server at ~13 % |
| `s4` | 10.88 / 9.80 / 7.80 | **nothing scored** | several lanes building and testing; deliberately not used to measure, its load was too high and too variable |

Two consequences, both stated before the data:

- **Decided counts survive contention far better than wall times do**, which is
  why this measurement is worth taking on a shared box at all. Contention only
  ever LOSES files; it cannot produce a wrong verdict.
- **It does not follow that the RATIO is a floor.** `parity-run.sh`'s own header
  records the 2026-08-21 case where load cost the reference ten QF_LRA files and
  cost us none, so a loaded run reported a ratio six points HIGHER than the
  quiet one. A high-load row is a floor on our own count and **nothing at all**
  on the ratio.
- **Files near a budget boundary flip.** A file deciding at 23.8 s under load 4
  misses at load 8. Any row whose start and end loads differ materially is
  marked NOT COMPARABLE below rather than quietly averaged.

<!-- RESULTS SECTION FOLLOWS ONCE THE SWEEPS LAND -->
