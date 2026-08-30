# Lane: countrange-bijection — the `countRange` permutation primitive, its Fubini companion, and the block bridge

<!-- plan-section: lane-status -->

**DONE (`countrange-bijection`, 2026-08-30).** Built and kernel-checked the
primitive `docs/plan/status/320-totient-bijection.md` named as the one
genuinely missing piece under `Nat.totient_mul_of_coprime`, plus both of the
other two pieces that lane's step (3) called for. **Five new theorems, no new
`Definition`, all axiom-free.** `nat_prelude::` **187 passed, 0 failed** (183
baseline + 4 new tests).

Of `320`'s three remaining steps toward `totient_mul_of_coprime`, step (2)
and the counting half of step (3) are now closed. What is left is step (1),
the CRT self-map's two hypotheses, and the final assembly — sized at the
bottom, with every ingredient named.

## The primitive

```text
Nat.countRange_permute :
  ∀ (f : Nat → Bool) (σ : Nat → Nat) (n : Nat),
    Nat.InjectiveOn σ n → Nat.MapsInto σ n →
    Eq Nat (countRange f n) (countRange (fun k => f (σ k)) n)
```

**Why this statement.** It is the exact `countRange` mirror of
`Int.prodRange_permute` — same hypotheses, same argument order — so the two
read against each other. It is also precisely what the CRT argument needs and
no more: for coprime `m, n` the map `g x := (x mod m) * n + (x mod n)` is an
injective self-map of `[0, m*n)`, and the coprimality predicate satisfies
`P x = Q (g x)` for **every** `x`, not merely `x < m*n` (checked numerically
for all `x < 60` at every `1 ≤ m,n ≤ 9`). So the consumer gets
`countRange Q (m*n) = countRange (Q ∘ g) (m*n)` from this theorem and closes
the last step with the *unconditional* `Nat.countRange_congr` that already
existed. No `P`/`Q` pair and no bounded pointwise agreement are needed in the
statement, so neither is in it.

## The other four

- **`Nat.countRange_product`** — the block/Fubini factorization, and the one
  step here that is **coprimality-INDEPENDENT**:

  ```text
  ∀ P R S n m,
    (∀ a b, Lt b n → R a = true  → P (add (mul n a) b) = S b) →
    (∀ a b, Lt b n → R a = false → P (add (mul n a) b) = false) →
    countRange P (mul n m) = mul (countRange S n) (countRange R m)
  ```

  Stated over an arbitrary `P` with two hypotheses pinning `R a` to each
  `Bool`, not over a fixed conjunction: this kernel exposes no `Bool`-valued
  `and` (`finite_set.rs`'s `bool_select_bool` is private), and a caller
  supplying its own combination discharges both by reduction. `Lt 0 n` is
  deliberately **not** a hypothesis — at `n = 0` both sides are `zero`, both
  hypotheses are vacuous, and the proof never divides.

Detail moved to [`../notes/344-countrange-bijection.md`](../notes/344-countrange-bijection.md).

