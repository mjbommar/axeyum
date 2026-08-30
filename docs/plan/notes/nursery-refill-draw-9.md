# Notes: nursery-refill-draw-9

Detail moved out of [`../status/nursery-refill-draw-9.md`](../status/nursery-refill-draw-9.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **`Mathlib.Data.Nat.Dist`** — re-screened per this session's own standing
  rule (a readiness figure from before an unblock exists is a figure about a
  different tree). Still R9 2/10 (`dist_comm`, `dist_self` already declared,
  per ADR-0653/ADR-0695's incident). **Used for `natural-distance` as
  TRAIN, not held-out** — contamination in a published partition is
  harmless; R9 would refuse it for held-out.
- **`Mathlib.Data.Nat.Factorial.Basic`, `Mathlib.Data.Int.GCD`** — R9
  1/10 each, contaminated. Not drawn this round (real supply remains for a
  future dev/train slot).
- **`Init.Data.Nat.Bitwise.Lemmas`, `Batteries.Data.Nat.Bitwise.Lemmas`,
  `Mathlib.Data.Nat.GCD.Basic`, `Mathlib.Data.Nat.Choose.Basic`** — R9
  clean but topically adjacent to published `natural-bitwise`/`natural-gcd`/
  `natural-binomial`. **Unsafe for held-out** (R11 would refuse — this is
  the exact ADR-0762 counter-example). `Init.Data.Nat.Bitwise.Lemmas` drawn
  for `natural-bitwise-basics` as DEVELOPMENT, where the adjacency is a
  feature not a defect.
- **`Nat.nthRoot`, `Squarefree`** (ADR-0762's own candidates) — not pursued;
  both require a new kernel construction, and this draw found a route that
  needs none. Left for a future lane if the below-floor route runs out
  (ADR-0830's consequences section: it is close to exhausted after this
  draw).
- **58 un-owned modules with >= 1 admissible survivor** were enumerated
  (286 rows total). Coarse topic-clash filter against the published
  dev/train topic vocabulary (`Bitwise, Choose, Coprime, Div, Dvd, Even,
  Factorial, Fermat, Fib, GCD, Gcd, Lcm, Log, Mod, ModEq, Parity, Prime,
  Totient`) left 100 rows in topic-clean modules; the two held-out families
  drawn here account for 23 of those 100 (11 + 12), each independently
  confirmed R9/R11-clean via the real screen rather than the coarse filter.
  `Mathlib.Data.Int.Fib.Basic` (6, genuinely novel Fibonacci content, no
  existing family) was considered and set aside for a future draw — not
  enough supply alone to reach the floor without either combining with the
  contaminated `Mathlib.Data.Nat.Fib.Basic` pool (whose one in-env row
  `Nat.fib_add` falls inside the first 10 alphabetically) or reaching a new
  construction.
- **`Init.Core`'s `Nat.add_zero`** — the only OTHER leftover row in the
  small-module sweep, excluded: already `IN-ENV` (R9-contaminated), so it
  cannot serve held-out and was not needed for the dev/train slots.

## Verification

| check | result |
| --- | --- |
| `gen-autogenesis-nursery-refill.py --check` | exit 0, idempotent post-regen: `entries=340\|development=130\|held-out=120\|train=90\|attested=411\|unattested=143` |
| `check-dispatchable-frontier.py` | exit 0 — dispatchable set non-empty, **1 -> 21** against floor 10 |
| `check-autogenesis-holdout-isolation.py` | exit 0 — `held_out=136 files_scanned=1110 settled=0 references=0 PASS` |
| `validate-facts.py` | exit 0 — `2314 facts checked, 0 errors` |
| `check-holdout-adjacency.py` (standalone, R11) | exit 0 — 13 held-out families, 0 refused; both new held-out families `topic=0 vocab=0/10 env=[]` |
| `check-merge-hygiene.sh` | exit 0 — `PASS` |
| `check-autogenesis-nursery.py` | **exit 1 — PRE-EXISTING, reproduced against `HEAD`'s own extension file with none of this draw's rows present; unrelated to this draw. See ADR-0830.** |

The one red gate (`check-autogenesis-nursery.py`, "declared dependency
component crosses evaluation partitions") was confirmed pre-existing by
swapping `artifacts/autogenesis/nursery-v2-extension.json` back to `HEAD`'s
committed version, re-running the check (same exit 1, same error), and
restoring this draw's version (`git diff --stat` confirmed byte-identical to
this draw's regenerated file afterward). The three leaking dependency
components (sizes 206, 4, 3) are entirely pre-existing `F:ml430-int-modeq-*`
/ `F:ml430-nat-div-gcd-*` / `F:ml430-int-add-*` facts committed 2026-08-29/30,
none of which touch any family this draw adds. This draw's 40 new entries
carry `depends_on: []` (the generator's standing convention for newly-drawn
rows) and are graph-isolated, so they cannot join or create a leaking
component.

## How long this draw lasts

**Not long — one more draw, maybe two, before the queue starves again on
this route.** The below-floor, un-owned, non-adjacent supply this draw
tapped is close to exhausted (`natural-elementary-bounds` already had to
reach into ten different tiny modules, including single-simp-lemma files, to
find ten rows). The two big remaining supplies — `Mathlib.Data.Nat.
Factorial.Basic`/`Mathlib.Data.Int.GCD` (contaminated for held-out, real for
dev/train) and the genuinely novel but too-small `Mathlib.Data.Int.Fib.Basic`
— can fund ONE more dispatchable dev/train family each, but neither opens a
new held-out family on its own. The next draw will most likely need
ADR-0762's original route: a construction-only kernel declaration (its own
`Nat.nthRoot` candidate is still clean and unspent) or a genuinely new
Mathlib area this inventory has not screened.

## Prohibitions honored

Floor was not lowered (still 10, unchanged in `check-dispatchable-frontier.py`).
No existing held-out row was touched — `git status` shows only new `??`
fact files plus the two generator/manifest edits. Nothing drawn this round
was proved; all 40 new rows are `open`.
