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

**The `F:ml430-nat-coprime-of-lt-minfac-0f79bdba` mirror stays `open`,
deliberately.** Mathlib's own `Nat.minFac` is NOT this — theirs is
well-founded recursion on `sqrt n`-bounded measure, skips even candidates,
and exits early once `k*k > n`. The two agree pointwise (both are "the least
divisor ≥ 2 of `n`" with identical boundary values) but are structurally
different `def`s, so per the established mirror-flip criterion this is the
`Nat.multichoose` case, not the `Nat.descFactorial_of_lt` case. A theorem
about coprimality relative to THIS `minFac` needs its own new `F:nat-*` fact
and a minimality property (`∀ d, 2 ≤ d → d ∣ n → minFac n ≤ d`) not attempted
here — sized as further, separate work.

**Kernel REJECTED nothing in this lane** — both declarations and every test
were accepted on first `add_declaration`/`declare_theorem`. The one real
correctness risk (a `Definition` that type-checks but computes the wrong
value; `Kernel::add_declaration` cannot catch this) was caught by evaluation
tests, not the kernel: `min_fac_computes_the_least_prime_factor_with_negative_controls`
checks `minFac 12 = 2` against `minFac 15 = 3` (the brief's discriminating
pair — "first divisor" and "smallest prime divisor" coincide for an
upward-from-2 scan, argued in `min_fac.rs`'s module doc) plus `minFac 0 = 2`,
`minFac 1 = 1`, `minFac 2 = 2`, `minFac 9 = 3`, each with a negative `def_eq`
control (including `minFac 12` vs `minFac 15` not collapsing to each other).

`nat_prelude` count: **85 + 443 -> 88 + 444** (1 new theorem
`coprime_iff_isRelPrime`, 3 new definitions `IsRelPrime`, `minFacAux`,
`minFac`; confirmed by `the_build_is_deterministic`'s own panic message, not
hand-counted).

## Verification run

- `cargo test -p axeyum-lean-kernel --lib nat_prelude` (targeted `nat_prelude::`
  filter): **127 passed, 0 failed** (was 126 before this lane's declarations
  + tests, 120 before `nat-singles`).
- `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings`:
  clean, no allow-lists needed.
- `rustfmt --edition 2024` on every touched file.
- `python3 scripts/validate-facts.py`: 0 errors (1922 facts, 1834 proved).
- `F:ml430-nat-coprime-iff-isrelprime-0c08eb25`'s new `checker_command`s run
  and confirmed to actually discriminate: `nat_theorem_inventory` prints the
  exact rendered type for `Nat.coprime_iff_isRelPrime`,
  `nat_axiom_inventory --require-axiom-free nat` exits 0, and both
  concrete-instance tests (mp/mpr round trip at (3,5); a real
  `Not (IsRelPrime 4 6)` proof from `gcd 4 6 = 2`) pass individually by name.
- Did NOT run the full aggregate `just check`/`./scripts/check.sh` (out of
  scope for a single-lane targeted change; the coordinator re-runs the full
  gate before merge per standing project convention).

## What's still needed for `F:ml430-nat-coprime-of-lt-minfac-0f79bdba`

A NEW fact (not the `ml430` mirror — see above) stating coprimality relative
to THIS `Nat.minFac`, which needs:

- **Minimality**: `∀ n, 2 ≤ n → ∀ d, 2 ≤ d → d ∣ n → minFac n ≤ d` — that
  `minFac n` really is the LEAST divisor `≥ 2`, not merely A divisor. Not yet
  proved; the natural route is an induction over the fuel search itself
  (every candidate `2, …, minFac n - 1` was tried and failed), mirroring
  `primes.rs`'s existing `least_divisor_search` minimality argument but
  adapted to the concrete recursive function rather than an existential
  witness.
- **The coprimality argument itself**, once minimality is in hand: for
  `m ≠ 0`, `m < minFac n`, suppose `g := gcd n m > 1`; `g ∣ n` and `g ≥ 2`
  gives `g ≥ minFac n` by minimality, but `g ∣ m` and `m ≠ 0` gives `g ≤ m`,
  contradicting `m < minFac n ≤ g ≤ m`. So `gcd n m = 1`.

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-minfac-relprime | `Nat.IsRelPrime`/`Nat.coprime_iff_isRelPrime`: closes `F:ml430-nat-coprime-iff-isrelprime-0c08eb25` |
| 2026-08-29 | nat-minfac-relprime | `Nat.minFacAux`/`Nat.minFac`: fuel-recursive least-prime-factor definition (bonus; no fact closed, `ml430` mirror stays open — different algorithm from Mathlib's) |
