# Lane: nat-factorization — the computed prime factorization

<!-- plan-section: lane-status -->

**Your lane's block (`IN PROGRESS`, nat-factorization, 2026-09-02).**

Picks up the handoff in `docs/plan/status/nat-multiset.md`: `Nat.Multiset`
landed uniqueness of prime factorization as multiplicity agreement, but not the
COMPUTED form. Targets, in order:

1. `Nat.Multiset.prod_add : ∀ m₁ m₂, prod (add m₁ m₂) = prod m₁ * prod m₂`
   — the named blocker, a product-regrouping law across three bounds.
2. `Nat.factorization : ℕ → Multiset` by fuel-bounded trial division over
   `Nat.minFac`, with evaluation tests at 12, 1 and 7.
3. `Nat.prod_factorization : ∀ n, 0 < n → prod (factorization n) = n` and
   `Nat.factorization_prime`.

<!-- plan-section: landed-changes -->

| 2026-09-02 | nat-factorization | lane opened |
