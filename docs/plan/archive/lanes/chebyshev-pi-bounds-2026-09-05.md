# Lane `chebyshev-pi-bounds` — the prime-counting shelf (roadmap W3-11, second slice)

<!-- plan-section: lane-status -->

**Status:** shelf opened, keystone landed; Chebyshev's bounds NOT landed and
re-sized from measurement. ADR-1655.

## What landed

Four theorems in `crates/axeyum-lean-kernel/src/nat_prelude/prime_counting_bounds.rs`,
all admitted through `Kernel::add_declaration` with an EMPTY `axiom_footprint`:

| name | statement |
| --- | --- |
| `Nat.primeCounting'_mono` | `∀ m n, m ≤ n → primeCounting' m ≤ primeCounting' n` |
| `Nat.primeCounting_mono` | `∀ m n, m ≤ n → primeCounting m ≤ primeCounting n` |
| `Nat.isPrime_eq_true_of_prime` | `∀ n, prime_condition n → isPrime n = true` |
| `Nat.primeCounting'_unbounded` | `∀ k, ∃ n, k ≤ primeCounting' n` |

Four fact-ledger rows, all `proved` / `kernel-lean` / empty footprint:
`F:nat-prime-counting-prime-mono`, `F:nat-prime-counting-mono`,
`F:nat-is-prime-eq-true-of-prime`, `F:nat-prime-counting-prime-unbounded`.

## The finding

The brief's blocker was not Chebyshev's combinatorics. `Nat.isPrime` was
declared construction-only under ADR-0653 and had **no theorem at all** —
`shape_search --const Nat.isPrime` over 3,277 declarations returns ABSENT — so
no source of primes in the kernel could reach `Nat.primeCounting'`.
Monotonicity was landable without that bridge only because it is true of
`Nat.countRange` at an ARBITRARY predicate, which is what made the shelf look
open when it was not. `Nat.isPrime_eq_true_of_prime` is the bridge, and
`Nat.primeCounting'_unbounded` (Euclid in counting form) is the first statement
on the shelf that is not also true of `countRange` at an arbitrary predicate.

## What did not land

* **Erdős's primorial bound `primorial n ≤ 4^n`.** Needs a product-over-
  restricted-range divisibility law (`shape_search --const Nat.prodRangeIf
  --const Nat.dvd`: ABSENT, ~650 lines, ADR-1637's estimate stands) AND
  `p ∣ choose (2m+1) m` for `m+1 < p ≤ 2m+1`, which is also unbuilt: the only
  choose-divisibility lemma in the kernel is `Nat.prime_dvd_choose :
  ∀ p k, prime p → 0 < k → k < p → p ∣ choose p k`, the freshman's-dream lemma
  with the prime on TOP. Different statement, cannot be specialised.
* **Chebyshev's lower bound in ℕ exponent form.** Needs both of the above plus
  Legendre's `p^(v_p(choose 2n n)) ≤ 2n`, and that piece is additionally
  **partition-blocked**: `Nat.divMaxPow`'s lemmas are in
  `natural-max-power-dividing`, genuinely held-out, which also carries
  Bertrand's postulate.

## Partition trap worth carrying forward

`artifacts/autogenesis/nursery-v2-extension.json` states each family's partition
in two disagreeing places. The per-entry `partition` field is CURRENT; the
top-level `family_partitions` / `preregistered_family_partitions` maps are the
PREREGISTERED record and are stale for exactly the two families moved by breach
repairs (`discrete-step-and-counting-bounds`, `natural-elementary-bounds`); the
other 52 agree. A lane checking only the map refuses briefable work. A lane
filtering on `partition != "development"` also mis-classifies every `train`
family as held-out — this lane did that on its first pass and had to redo the
check.
