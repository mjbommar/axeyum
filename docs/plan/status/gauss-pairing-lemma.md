# Lane: gauss-pairing-lemma

## Status: in progress (2026-08-31)

Working piece 2 of the Gauss's-lemma connecting theorem (ADR-0970/
ADR-0985/ADR-0990). ADR-0990 verified in place before starting: the
`InjectiveOn`/`MapsInto`-on-a-self-map route (no explicit bijection/
partner-index construction) checks out against `Int.prodRange_permute`'s
actual signature.

## Plan (from ADR-0990, re-verified)

1. `Nat.least_residue_ne_zero_of_coprime` -- the one lemma ADR-0990 flagged
   as genuinely absent from the tree. Route: `leastResidue pp a k = 0` gives
   `pp | a*k` (`Nat.dvd_iff_mod_eq_zero`), `Nat.gauss_lemma` (the EXISTING,
   DIFFERENT-from-our-target Euclid-cancellation theorem, `gcd x y=1 -> x|y*z
   -> x|z`) cancels the coprime factor `a` to give `pp | k`, contradicting
   `0 < k < pp` via `Nat.le_of_dvd`/`Nat.lt_of_le_of_lt`/`Nat.lt_irrefl`
   (identical shape to `bezout.rs:1690-1700`'s existing contradiction).
2. `Nat.gaussFold` definition + `InjectiveOn`/`MapsInto` on `[0,m)`.

## Progress

- [ ] `least_residue_ne_zero_of_coprime` -- in progress
- [ ] `gaussFold` definition
- [ ] `InjectiveOn` (same-sign + opposite-sign-vacuous cases)
- [ ] `MapsInto`

Axiom footprints will be read from `theorem_axiom_footprint` and recorded
here as each piece lands.

## Scope

`crates/axeyum-lean-kernel/src/nat_prelude/gauss_lemma.rs` only. Do NOT
touch `artifacts/autogenesis/`. ADR-1015 reserved.
