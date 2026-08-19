# Lane: creal-lean-divergence — which Lean rejected it

<!-- plan-section: lane-status -->

**Lean's kernel accepts all 470 declarations of the constructed-real carrier;
it is Lean's ELABORATOR that refuses four** (`WIP`, creal-lean-divergence,
2026-08-18). The handover said our kernel admits what Lean's kernel rejects.
It does not. `scripts/lean/replay-lean4export.lean` drives
`Environment.addDeclCore` from our official NDJSON — Lean's kernel, from
`mkEmptyEnvironment` — and over the **whole** carrier reports
`the real Lean kernel accepted 438 declaration records … environment now holds
470 constants` in **1.4 s**. Tampering `CReal.Equiv.not_zero_one`'s proof makes
the same binary reject it naming `Not (CReal.Equiv (CReal.ofRat Rat.zero)
(CReal.ofRat Rat.one))`, so it checked *that* declaration against *that* type.

**The mechanism, isolated to one token per line.** Lean's elaborator does not
unfold a `theorem` while reducing; its kernel does. Re-spell every `theorem` in
the *same emitted file* as `def` — nothing else changed — and the elaborator
accepts it: the `not_zero_one` module (695,655 B) in 5.0 s and the **whole
carrier** (2,541,928 B) in 27.9 s, against 4 refusals as emitted.
`Nat.gcd`'s descent is justified by the *theorem* `Nat.mod_lt`, so `gcd 0 3`
(base case) is accepted and every recursive `gcd` refused, while `Nat.mod/div/
sub` and a bare `WellFounded.fix` reduce fine. Not the sharing pass (hand-
inlined: identical refusal), not a budget (`maxRecDepth 1000000`,
`maxHeartbeats 0`, `smartUnfolding false` move nothing). `internal exception #3`
is the command abort after the term error.

**The coverage hole is closed.** Emission was reachability-driven, so Lean had
only ever seen the reachable slice (343 of 465 when ADR-0482's lane measured it). `real_lean_creal_carrier_kernel_replay`
exports the complete environment with no filter and requires Lean's reported
constant count to **equal** the count read out of our kernel, so "accepted"
cannot mean "accepted a subset". `real_lean_wellfounded_elaborator_divergence`
pins the residue over the ℕ prelude alone. Lean gate **20 suites, floor
212 -> 218**. The fix (`theorem` -> `def` in the renderer) is measured and
deliberately handed to the renderer's owner, not taken here.

ADR-0488. Detail in
[`../notes/103-creal-lean-divergence.md`](../notes/103-creal-lean-divergence.md).

<!-- plan-section: landed-changes -->

| 2026-08-18 | `PENDING` | Lean has two checkers (ADR-0488): the kernel accepts all 470 carrier declarations, the elaborator refuses those whose checking must reduce a `theorem`. `real_lean_creal_carrier_kernel_replay` (whole carrier, no reachability filter, count-equality + tamper control) and `real_lean_wellfounded_elaborator_divergence` (`gcd` refused / `mod` accepted / same module with `theorem`->`def` accepted / kernel takes both); gate floor 212 -> 218. |
