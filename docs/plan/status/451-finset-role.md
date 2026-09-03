# Lane: finset-role — a computed `Nat.Finset` carrier (predicate + bound)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, finset-role, 2026-09-03).** Opening the lane. The
target is a computed finite-set carrier — a one-constructor inductive bundling
a decidable predicate `ℕ → Bool` with a bound — so that "sum of `f` over the
set `{i < n | p i}`" and cardinality arguments have a first-class object,
rather than every site re-spelling an ad hoc `Nat.countRange (fun k => …) n`.
No quotient, no `propext`, no `List`; ℕ only, exactly as ADR-1520 scoped
`Nat.Multiset`.

<!-- plan-section: landed-changes -->

| 2026-09-03 | finset-role | lane opened; status stub only |
