# Lane 373 — the unrestricted least-number principle implies excluded middle

<!-- plan-section: lane-status -->

## Status

**DONE.** ADR-0603 row 2 for the least-number principle over the naturals is
landed, kernel-checked, axiom-free, and registered in the fact ledger with its
converse. This is the first row-2 result in the repository that is not about the
reals, and it is strictly stronger than the two that are.

## What landed

`crates/axeyum-lean-kernel/src/nat_prelude/least_number.rs` — five theorems, all
admitted by `Kernel::add_declaration` on the first attempt, all with an empty
`axiom_footprint`. Rendered types read from
`nat_theorem_inventory` (`--release`), one name per invocation:

```text
Nat.lnp_unrestricted_implies_em :
  (∀ (Q : AxNat → Prop),
     (∃ n, Q n) → ∃ m, And (Q m) (∀ k, AxNat.lt k m → Not (Q k)))
  → ∀ (P : Prop), Or P (Not P)

Nat.em_implies_lnp :
  (∀ (P : Prop), Or P (Not P))
  → ∀ (Q : AxNat → Prop),
      (∃ n, Q n) → ∃ m, And (Q m) (∀ k, AxNat.lt k m → Not (Q k))

Nat.lnp_of_pointwise_decision :
  ∀ (Q : AxNat → Prop), (∀ n, Or (Q n) (Not (Q n)))
  → (∃ n, Q n) → ∃ m, And (Q m) (∀ k, AxNat.lt k m → Not (Q k))

Nat.lnp_bounded_search :
  ∀ (Q : AxNat → Prop), (∀ n, Or (Q n) (Not (Q n))) → ∀ n,
    Or (∀ k, AxNat.lt k n → Not (Q k))
       (∃ m, And (AxNat.lt m n) (And (Q m) (∀ k, AxNat.lt k m → Not (Q k))))

Nat.lnp_decidable :
  ∀ (dec : AxNat → Bool) (n : AxNat), Eq Bool (dec n) Bool.true
  → ∃ m, And (Eq Bool (dec m) Bool.true)
             (∀ k, AxNat.lt k m → Eq Bool (dec k) Bool.false)
```

Facts: `F:nat-lnp-unrestricted-implies-em` (row 2) and `F:nat-lnp-decidable`
(the decidable-fragment exact form). ADR-0725 records the two design decisions
ADR-0716 did not make.

## The three things a reviewer should check first

Detail moved to [`../notes/373-lnp-implies-em.md`](../notes/373-lnp-implies-em.md).

