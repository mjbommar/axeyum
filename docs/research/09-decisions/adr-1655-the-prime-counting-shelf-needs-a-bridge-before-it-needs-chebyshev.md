# ADR-1655: the prime-counting shelf needs a bridge before it needs Chebyshev

Status: accepted
Date: 2026-09-06
Lane: `chebyshev-pi-bounds` (roadmap W3-11, second slice)
Index-summary: The prime-counting shelf's blocker was never Chebyshev's combinatorics; it was that `Nat.isPrime` had no theorem at all, so no source of primes in the kernel could reach `Nat.primeCounting'`. The bridge and Euclid-in-counting-form land; Erdős's primorial bound is re-sized from measurement.

Follows [ADR-1637](adr-1637-the-primorial-is-a-product-over-minfac-and-chebyshev-runs-into-a-blind-family.md)
and [ADR-0653](adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md).

## Context

[ADR-1637](adr-1637-the-primorial-is-a-product-over-minfac-and-chebyshev-runs-into-a-blind-family.md) built the
primorial and the odd central binomial bound but declined the whole
`Nat.primeCounting'` shelf, because five of the ten rows of the preregistered
held-out family `discrete-step-and-counting-bounds` are statements about that
pair and the family had never been scored.

That family moved `held-out -> development` on 2026-09-05, recorded in
`artifacts/autogenesis/mathlib-nursery-split-policy-v1.json` under authority
[ADR-0542](adr-0542-held-out-partition-breach-repair.md): a producer contract
(`psatz-sum-of-squares-v1`, ADR-1649) cited
`F:ml430-int-le-sub-one-of-not-le-fc32b89d` by name as a `non_example`, and the
partition unit is the whole family, so all ten rows moved together. Nothing was
proved; the blind-evaluation value was spent by the citation. The move is
irreversible.

This lane's brief therefore listed three deliverables: the two cheap counting
rows, Erdős's primorial bound `primorial n <= 4^n`, and Chebyshev's lower bound
in exponent form `4^n <= (2n+1) * (2n)^(pi'(2n))`.

## Decision

**The shelf is opened with a bridge, not with a bound.** Four theorems land:

| name | statement |
| --- | --- |
| `Nat.primeCounting'_mono` | `∀ m n, m ≤ n → primeCounting' m ≤ primeCounting' n` |
| `Nat.primeCounting_mono` | `∀ m n, m ≤ n → primeCounting m ≤ primeCounting n` |
| `Nat.isPrime_eq_true_of_prime` | `∀ n, prime_condition n → isPrime n = true` |
| `Nat.primeCounting'_unbounded` | `∀ k, ∃ n, k ≤ primeCounting' n` |

Erdős's bound and Chebyshev's bound do NOT land, and the reason is recorded
below as a measurement rather than an estimate.

## Why a bridge was the blocker, and why nobody had noticed

The brief sized the infinitude row as "two lines from `exists_prime_gt`". It is
not two lines, and the reason generalises past this lane.

`prime_counting.rs` declares `Nat.isPrime` under
[ADR-0653](adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md) as a
CONSTRUCTION ONLY — the definition, its evaluation test, and deliberately no
theorem, not even a defining equation. A `shape_search --const Nat.isPrime`
over the whole environment (`declarations=3277`, freshly built, positive control
retrieving a theorem declared minutes earlier) returns **ABSENT**.

So nothing in the kernel connected the `Bool` predicate that
`Nat.primeCounting'` actually counts to this prelude's propositional
`prime_condition` — and every source of primes in the kernel
(`Nat.exists_prime_gt`, `Nat.exists_prime_dvd`, `Nat.min_fac_prime`) produces
the propositional form. The two halves of the shelf could not meet.

What hid this is worth naming, because it is a general shape:

> **Monotonicity was landable without the bridge, and monotonicity is the only
> kind of fact that is.** `primeCounting'_mono` is `countRange_le_of_le` at the
> predicate `Nat.isPrime`, accepted by delta alone through
> `primeCounting' (14) -> count (13) -> countRange (12)`. It is true of
> `countRange` at an ARBITRARY predicate. A shelf whose first theorem is
> structural looks open when it is not: the proof never evaluates the predicate,
> so a `Nat.isPrime` computing something else entirely would leave the theorem
> admitted, axiom-free, and useless.

This is the reason the module's evaluation rows are not decoration and are
required by the same rule that requires them for a `Definition`. `Nat.isPrime`
is pinned at ten concrete arguments with a negative control on each. The
discriminating row is `isPrime 1 = false`: `1` has one divisor in `[1,1]`, not
two — and it is exactly the value `Nat.primorial`'s own predicate
(`beq (minFac i) i`) answers `true` at, harmlessly for a product and fatally
for a count. The two shelves use two different primality predicates, and that
was not previously written down anywhere.

### What the bridge costs

`isPrime n` unfolds to `beq (countRange (fun j => beq (n % (j+1)) 0) n) 2` — a
divisor COUNT, not a trial division. The proof shows the count is exactly two:
`1 ∣ n` supplies index `0`, `mod_self` supplies index `n-1`, and every index
between is refuted by primality's own divisor clause (`c = 1` by
`succ_ne_zero`, `c = n` by `lt_irrefl` against the range hypothesis). The count
is assembled by peeling the last index with `countRange_succ_of_true` and the
first with `countRange_split` at `1`, leaving
`countRange_eq_zero_of_all_false` for the middle: `2 = 1 + 0 + 1`.

Two costs are worth recording because the next lane on this shelf will meet
both:

* **`Nat.add` recurses on its RIGHT argument**, so the `add 1 k` that
  `countRange_split` puts into its shifted predicate is STUCK at symbolic `k`.
  It is not `succ k` by reduction. Every step that meets a front-peel needs the
  `succ_add`/`zero_add` pair, isolated here as `one_add_eq_succ`. Peeling the
  LAST index is free; peeling the FIRST is not, and the asymmetry is invisible
  until a proof is attempted.
* **Only the FORWARD direction is proved.** The converse — `isPrime n = true`
  implies `prime_condition n` — is a different argument: a count of two forces
  the divisor set to be exactly `{1, n}`, which needs a pigeonhole on the count
  rather than two witnesses. It is not claimed, and no consumer here needs it.

## What did not land, sized from measurement

**Erdős's primorial bound `primorial n <= 4^n`** needs two absent pieces, and
ADR-1637's `~650 lines by analogy with Int` was an estimate against only the
first of them:

1. **A product-over-predicate-restricted-range divisibility law with pairwise
   coprime factors.** `shape_search --const Nat.prodRangeIf --const Nat.dvd`:
   **ABSENT**. This is the ~650-line item and the estimate stands.
2. **`p ∣ choose (2m+1) m` for every prime `p` with `m+1 < p <= 2m+1`.** The
   brief suggested `Nat.Prime.dvd_choose_*` "may exist under other names".
   `shape_search --const Nat.choose --const Nat.dvd` returns exactly ONE match,
   `Nat.prime_dvd_choose : ∀ p k, prime p → 0 < k → k < p → p ∣ choose p k`.
   **That is the freshman's-dream lemma `p ∣ C(p,k)`, a different statement**:
   its dividend is `choose p k` with the PRIME on top, not `choose (2m+1) m`.
   It cannot be specialised to the needed form. This piece is unbuilt, not
   merely unnamed, and it needs `choose (2m+1) m * m! * (m+1)! = (2m+1)!`
   together with `p ∤ m!` and `p ∤ (m+1)!` from `p > m+1`.

**Chebyshev's lower bound in exponent form** needs both of the above plus
Legendre's `p^(v_p(choose 2n n)) <= 2n`. That last piece is additionally
**partition-blocked**: `Nat.divMaxPow`'s lemmas live in the family
`natural-max-power-dividing`, which is genuinely `held-out` (verified against
the per-entry `partition` field, not the stale top-level `family_partitions`
map — see below), and that family also carries Bertrand's postulate. A lane
that formalises Legendre's formula by proving `divMaxPow` lemmas spends that
family. It must be approached either through a construction that does not
mention `Nat.divMaxPow`, or not at all until the family is scored.

## A trap in the partition manifest

`artifacts/autogenesis/nursery-v2-extension.json` carries the partition in TWO
places that disagree, and only one is current:

* the per-entry `partition` field on each of the 540 entries, and
* the top-level `family_partitions` / `preregistered_family_partitions` maps.

For `discrete-step-and-counting-bounds` the entries read `development` and both
maps still read `held-out`. The same disagreement exists for
`natural-elementary-bounds`. Those are exactly the two families moved by
breach repairs; the other 52 agree. **The entries are current and the maps are
the preregistered record.** A lane that checks the map alone will refuse
briefable work; a lane that checks only `p != "development"` will also
mis-classify every `train` family as held-out, which this lane did on its first
pass. Check the per-entry field, and confirm against `partition_moves` in
`mathlib-nursery-split-policy-v1.json`.

## Consequences

* The shelf is open and its keystone is in. Any future statement about
  `Nat.primeCounting'` — Chebyshev, Mertens, a sieve bound — now has a route
  from a prime to the count, which it did not have before.
* `Nat.primeCounting'_unbounded` is a lower bound with NO RATE. It says nothing
  about how large `n` must be for `pi'(n)` to reach `k`. Supplying a rate is
  what Chebyshev's bounds are for, and that remains the open work.
* The two shelves in this area use two different primality predicates
  (`Nat.isPrime` for counting, `beq (minFac i) i` for the primorial) and they
  disagree at `i = 1`. Connecting the primorial to `primeCounting'` will need a
  second bridge; it is not the one landed here.
