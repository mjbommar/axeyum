# Lane: nat-minfac-relprime — close `IsRelPrime`, build `Nat.minFac` as a bonus

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-minfac-relprime, 2026-08-29).** Landed the
required fact and the bonus definition sized in
[`docs/plan/status/240-nat-singles.md`](240-nat-singles.md).

`Nat.IsRelPrime m n := ∀ d, d ∣ m → d ∣ n → d = 1` (`rel_prime.rs`), a genuine
new `Definition` — Mathlib's generic `∀ d, d∣x → d∣y → IsUnit d`
(`Mathlib/Algebra/Divisibility/Units.lean:150`) specialized to `Nat`'s only
unit, `1`. Both directions of `Nat.coprime_iff_isRelPrime` were exactly as
cheap as the handoff predicted: forward combines `d∣m`/`d∣n` via `dvd_gcd`,
transports along the hypothesis to `d∣1`, and closes with
`eq_one_of_dvd_one`; backward applies the hypothesis directly at
`d := gcd m n`, discharged by `gcd_dvd_left`/`gcd_dvd_right`. No case
analysis in either direction, and neither unfolds `Nat.gcd`'s own recursion.
Closes `F:ml430-nat-coprime-iff-isrelprime-0c08eb25` (flipped `open` ->
`proved`; the mirror flip is honest — verified by reading Mathlib's actual
source for `IsRelPrime` at the pinned commit, not inferring from the
theorem's statement).

**Bonus: `Nat.minFac`/`Nat.minFacAux` landed** (`min_fac.rs`), a fuel-recursive
linear divisor search — structural `Nat.rec` on a `fuel` argument (the same
device `Nat.div`/`Nat.mod`/`Nat.log` use), fuel `= n - 2`, scanning candidates
`2, 3, 4, …` via `beq (mod n candidate) 0`. Fuel exhaustion coincides exactly
with `candidate = n` (never earlier), so the base case "return the candidate
unchanged" is correct — `n` trivially divides itself. `minFac 0 = 2` and
`minFac 1 = 1` are an outer case split before the search runs, matching
Mathlib's boundary conventions.

Detail moved to [`../notes/241-nat-minfac-relprime.md`](../notes/241-nat-minfac-relprime.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-minfac-relprime | `Nat.IsRelPrime`/`Nat.coprime_iff_isRelPrime`: closes `F:ml430-nat-coprime-iff-isrelprime-0c08eb25` |
| 2026-08-29 | nat-minfac-relprime | `Nat.minFacAux`/`Nat.minFac`: fuel-recursive least-prime-factor definition (bonus; no fact closed, `ml430` mirror stays open — different algorithm from Mathlib's) |
