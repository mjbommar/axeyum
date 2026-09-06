# Lane: fermat-two-squares — Fermat's theorem on sums of two squares is proved

<!-- plan-section: lane-status -->

**`Int.fermatTwoSquares` is admitted and axiom-free** (`DONE`,
fermat-two-squares, 2026-09-05). Every prime `p = 2m+1` with `m` even — that
is, every prime `p ≡ 1 (mod 4)` — is a sum of two integer squares, established
in this kernel with no assumption behind it. W3-10 closes.

Twelve declarations in a new `int_prelude/fermat_two_squares.rs` (ADR-1650)
complete the four pieces ADR-1647 sized, and **every one was admitted on the
first attempt**. Nothing in ADR-1647's sizing turned out to be stale — a
departure from that ADR's own finding about its predecessor.

The four pieces:

1. `Int.exists_next_multiplier` — from `m·p = a²+b²` and centered `c ≡ a`,
   `e ≡ b (mod m)`, the norm `c²+e²` is again a multiple of `m`. Stated as
   `m·q = c²+e²` so it matches `Int.descentMultiplierBounds` and
   `Int.descentStep` verbatim; the `symm` happens once here rather than at
   both call sites. Positivity of `m` is NOT a hypothesis — every congruence
   on this leg is unconditional in the modulus.
2. `Int.dvd_of_degenerate_descent` plus `Int.not_dvd_ofNat_of_prime_of_lt` —
   the `q ≠ 0` argument, split at the point primality enters. The first is a
   true statement about **any** nonzero `m` with no primality, no bounds and
   no `Nat` in it; the second is the refutation and is the **only** declaration
   in the module that reads a primality condition.
3. `Int.exists_sum_of_two_squares_of_multiple` — Euler's descent, by
   `Nat.strongInduction` at a `Prop` motive.
4. `Int.fermatTwoSquares` — the theorem, in three named steps:
   `Int.firstSupplementaryLawResidue` → `Int.exists_small_multiple_of_sq_add_one`
   → the descent. The only glue is the `Nat` bridge ADR-1647 sized, and it is
   two one-line declarations.

**The design call that carries the assembly**: the descent quantifies its
multiplier as `Int.ofNat n` over a `Nat` index, not as an `Int m` with a
`natAbs m = n` bridge hypothesis. `Int.le`/`Int.lt` at two `ofNat`s is
*definitionally* the corresponding `Nat` relation, so `0 < m`, `m < p` and
`1 < m` are all the `Nat` hypotheses themselves (`Int.lt_ofNat_of_lt` is
`fun h => h`), and the whole proof contains **one** transport across
`of_nat_nat_abs_of_nonneg` — at the recursive call, where `q` genuinely
arrives as an `Int`. The bridge spelling would have needed three at every
level and would have had to re-establish the bridge at the recursive call
anyway. It also means no `refl`-generalisation of the motive: unlike
`Nat.Hall.hall_sufficient`, the measure here IS the index.

Three plumbing lemmas that were simply absent also land and are reusable
outside this proof: `Int.dvd_zero` (`shape_search --ns Int --concl Int.dvd
--arity 1` found only `Int.dvd_refl`), `Int.dvd_of_modEq_zero`, and
`Int.mul_modEq_zero`. `dvd_of_modEq_zero` goes through the **unconditional**
`Int.ModEq.dvd_iff` rather than the `0 < n`-scoped `Int.modEq_iff_dvd`: the
latter produces `n ∣ (b − a)` and would have needed a `sub_zero` this prelude
does not have and which `ring::int` declines, ADR-1633's zero-collapse finding
hit from the other side.

`order_squares.rs`'s private `centered_body` and `small_multiple_body` are
**re-derived** here rather than widened to `pub(super)` — that file belongs to
a sibling lane's history and this module adds no edit to it. The *predicates*
(`centered_predicate`, `small_multiple_outer`) are re-used, and they are what
the `Exists.rec`s eliminate, so a drifted body would stop type-checking rather
than pass quietly.

**Partition check**: `descent-and-well-ordering` and
`power-and-square-decompositions` are both held-out families, and their rows
(`Nat.sum_four_squares`, `Nat.Prime.sum_four_squares`,
`Int.lt_of_sum_four_squares_eq_mul`, `Int.exists_least_of_bdd`,
`Int.exists_greatest_of_bdd`, `Nat.sq_add_sq_mul`, `Int.sq_ne_two_mod_four`)
are named in the module doc and NOT declared. Mathlib's `Nat.Prime.sq_add_sq`,
which IS this theorem, is in neither family;
`check-autogenesis-holdout-isolation.py` was run after the proof landed and
verdict=PASS (held_out=206, references=0).

<!-- plan-section: landed-changes -->

| 2026-09-05 | `a065f045c` | `int_prelude/fermat_two_squares.rs`: the descent's next multiplier (`exists_next_multiplier`), its degenerate branch (`dvd_of_degenerate_descent`), the single primality-consuming step (`not_dvd_ofNat_of_prime_of_lt`), and the plumbing each needed — `dvd_zero`, `dvd_of_modEq_zero`, `mul_modEq_zero`, `sq_add_sq_modEq_of_modEq`, `sq_mul_add_sq_mul` (ring::int), and the coercion bridges `lt_ofNat_of_lt` / `le_two_of_nat_le_two`. All ten admitted first try, axiom-free. |
