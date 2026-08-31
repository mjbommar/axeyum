# nursery-refill-draw-12

<!-- plan-section: lane-status -->

**Status: DECLINED.** Decision record:
[ADR-1045](../../research/09-decisions/adr-1045-draw-12-is-declined-a-clean-second-family-was-not-found.md).

Dispatched against a reported "4 dispatchable against a floor of 10". This
worktree's tree reads **10 dispatchable** (exactly at floor, not below) --
seven ADR-0542 amendments landed since draw 11 (`natural-gcd`,
`natural-binomial`, `natural-logarithm`, `natural-divisibility`,
`natural-parity`, `fermat-numbers`, `natural-bit-decode`, all moved
`held-out -> development` because ordinary hand development or closed
evaluation had already spent them blind), which is why the frontier did not
drain further despite five theorem lanes closing ~30 mirrors since draw 11.
This also resolves ADR-0925's two named residuals: `check-autogenesis-
nursery.py`'s stale cross-population exemption now passes clean, and
`check-holdout-closed-evaluation.py`'s 2-violation spend
(`Nat.bit_false_zero`/`Nat.size_one`) is gone because the family carrying it
(`natural-bit-decode`) is no longer held-out.

Refreshed the environment snapshot (2507 -> 2552 declarations via a fresh
`shape_search --release` build) and re-ran the real `select()`/`guard()`/
`screen_family` (not `propose-nursery-refill.py`'s looser mirror) against
every un-owned Nat/Int module (32 modules, 94 total candidates, none
individually >= the 10-row floor) and every below-floor combination this
lane could construct from them. All either R9-contaminated or R11-refused
against a published development/train family -- the elementary-number-theory
territory (gcd, choose, factorial, prime, totient, fib, bitwise, parity,
divisibility, log) is now claimed across twelve draws' worth of families.
Reproduces and extends ADR-0900's finding on a tree with more families
claimed and fewer excluded-from-screening held-out rows (the seven
amendments above moved their subjects INTO the screened dev/train
population, making future attempts near those topics harder, not easier).

**One genuinely clean, floor-clearing construction target was found by
simulation**: declaring `Nat.avg : Nat -> Nat -> Nat` and `Nat.pair : Nat ->
Nat -> Nat` (both plain, typeclass-free, `Prod`-free definitions --
`avg a b := (a+b)/2`, `pair a b := if a < b then b*b+a else a*a+a+b` -- built
from existing `Nat.add`/`Nat.mul`/`Nat.lt`/`ite`) opens
`Batteries.Data.Nat.Bisect` + `Mathlib.Data.Nat.Pairing` as one 15-candidate
held-out family: R9 0/10, R11 fully clean (zero topic hits, zero vocabulary
hits, zero environment-sweep hits), verified by adding both names to a
simulated environment and re-running the real screen. This alone is not
sufficient -- R5 needs TWO new held-out families -- and a comparably clean
second was not found this session (checked and rejected: `Nat.divMaxPow`,
only 7 real candidates; `Nat.doubleFactorial`, topic-collides with the
published Factorial family; `Nat.factorizationLCMLeft`/`Right`,
vocabulary-collides via `Nat.lcm`; Bell/Schröder/Stirling numbers, need
`Finset`/`List` machinery this kernel does not model). `Init.Data.Nat.MinMax`
(30 candidates) is the largest remaining opportunity but needs typeclass-name
bridging (`Max.max`/`Min.min`/`Nat.instMax`/`instMinNat`), a harder route than
a plain definition, and is named as the next thing to scope rather than a
confirmed unblock.

**Next draw needs:** build `Nat.avg` + `Nat.pair` in
`crates/axeyum-lean-kernel` (opens one held-out family, verified clean), and
either scope the `Init.Data.Nat.MinMax` typeclass-bridging route or find a
different second construction -- R5 needs two.

## Verification (current tree, environment snapshot refreshed, no other change)

| check | result |
| --- | --- |
| `check-dispatchable-frontier.py` | exit 0, `DISPATCHABLE: 10` (floor 10 -- exactly at floor) |
| `gen-autogenesis-nursery-refill.py --check` | exit 0, `entries=380\|env=2552\|development=150\|held-out=130\|train=100` |
| `check-autogenesis-nursery.py` | exit 0, `AUTOGENESIS_NURSERY_OK\|...\|evaluation=214\|blockers=0` + `AUTOGENESIS_NURSERY_CROSS_POPULATION_OK\|...\|v1=216\|v2=380\|components=301` |
| `check-autogenesis-holdout-isolation.py` | exit 0, `held_out=146 files_scanned=1110 settled=0 references=0 verdict=PASS` |
| `check-holdout-closed-evaluation.py` | exit 0, `held_out=146 closed_shaped=0 violations=0 ... verdict=PASS` |
| `validate-facts.py` | exit 0, `2365 facts checked, 0 errors` |
| `gen-adr-index.py --check` | exit 0 |
