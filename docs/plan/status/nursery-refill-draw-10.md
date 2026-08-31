# nursery-refill-draw-10

<!-- plan-section: lane-status -->

**Status: DECLINED.** Decision record:
[ADR-0900](../../research/09-decisions/adr-0900-draw-10-is-declined-the-below-floor-held-out-safe-supply-is-exhausted.md).

Dispatched against a reported "3 dispatchable against a floor of 10". This
worktree's tree (branched from `origin/main`, fetched and confirmed only 6
unrelated commits ahead) shows **21 dispatchable** already — draw 9's
`natural-bitwise-basics`/`natural-distance` rows, undrained here. All four
required gates already pass in the unmodified tree: `check-dispatchable-
frontier.py` (21 >= 10), `check-autogenesis-nursery.py` (both OK lines),
`check-autogenesis-holdout-isolation.py` (`held_out=136 ... PASS`),
`validate-facts.py` (`2318 facts checked, 0 errors`).

Screened anyway, per the brief: every `propose-nursery-refill.py --remeasure`
"ready" module (re-measured with the real `select()`, not the proposer's
looser screen) is R11-adjacent to a published development/train family
(gcd, factorial, choose, bitwise). Every below-floor combination tried from
the remaining ~40 tiny un-owned modules was either R9-contaminated
(`Mathlib.Data.Nat.BinaryRec`'s `Nat.bit*` subject is exhaustively developed
natively — 43 matching kernel declarations) or R11-refused (fib, gcd/choose,
prime/ModEq/totient vocabulary). Exactly one combination
(`Mathlib.Data.Nat.Bits` + `Mathlib.Data.Nat.Size`) is mechanically clean
(R9 0/10, R11 topic 0, vocabulary 0/10) but R5 needs two new held-out
families and no second clean one exists — declined rather than forcing a
contaminated or adjacent second family through. Full screening trail in
ADR-0900.

One unrelated repair landed alongside: `artifacts/autogenesis/nursery-v2-
extension.json`'s own `extension_sha256` did not match its body (a sibling
lane hand-added `cross_population_component_split_exemptions` without
recomputing the digest), which blocked `gen-autogenesis-nursery-refill.py`
entirely regardless of what any draw would do. Fixed with a 1-line digest
recomputation; `check-autogenesis-nursery.py` is unaffected either way.
Residual gap (the generator's own `build_extension()` does not round-trip
that key, so `--check` still reports the file stale) is recorded in
ADR-0900, not fixed — out of this lane's scope.

**Next draw needs:** ADR-0762's construction-only route (`Nat.nthRoot`,
still unbuilt), a second construction alongside it (R5 needs two new
held-out families), or a genuinely new source of un-owned Mathlib modules —
the pinned inventory here is `Nat`/`Int`-scoped only.

## Verification (current tree, unmodified by this draw)

| check | result |
| --- | --- |
| `check-dispatchable-frontier.py` | exit 0, `DISPATCHABLE: 21` (floor 10) |
| `check-autogenesis-nursery.py` | exit 0, `AUTOGENESIS_NURSERY_OK` + `AUTOGENESIS_NURSERY_CROSS_POPULATION_OK` |
| `check-autogenesis-holdout-isolation.py` | exit 0, `held_out=136 files_scanned=1110 settled=0 references=0 verdict=PASS` |
| `validate-facts.py` | exit 0, `2318 facts checked, 0 errors` |
| `gen-adr-index.py --check` | exit 0 |
