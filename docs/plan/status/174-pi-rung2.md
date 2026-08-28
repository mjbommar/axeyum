# Lane: pi-rung2 — π rung 2, `cosFnWide (8/5) < 0`

<!-- plan-section: lane-status -->

**Status: IN PROGRESS (pi-rung2, 2026-08-27).** Arithmetic re-verified
independently of the brief; route survey under way. Nothing has gone through
`Kernel::add_declaration` yet.

Verified by hand, against `169-pi.md`'s numbers:

- `a k := (8/5)^{2k}/(2k)!`; `a 0 = 1`, `a 1 = 32/25 = 1.28`,
  `a 2 = 4096/625/24 = 512/1875 ≈ 0.27307`. So `a 1 > a 0` — the GLOBAL
  antitonicity `alternatingLowerBound`/`alternatingUpperBound` demand fails at
  `k = 0`, exactly as `169-pi.md` measured.
- `a 1 − a 2 = 2400/1875 − 512/1875 = 1888/1875 ≈ 1.006933`, margin
  `13/1875 ≈ 0.006933` over `1`. Both confirmed.
- Equivalently and more usefully: the ODD partial sum
  `O 1 = a 0 − a 1 + a 2 = 1 − 32/25 + 512/1875 = −13/1875 < 0`, and
  `cos(8/5) ≈ −0.0292 ≤ −13/1875`. The margin is the same `13/1875`.

<!-- plan-section: landed-changes -->

| 2026-08-27 | pi-rung2 | WIP: arithmetic of rung 2 independently re-verified (`1888/1875`, margin `13/1875`); route survey in progress |
