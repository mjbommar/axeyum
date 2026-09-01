# Lane: aggregates

<!-- plan-section: lane-status -->

**Status:** decided and landed —
[ADR-1310](../../research/09-decisions/adr-1310-the-aggregate-absence-is-an-inventory-and-a-fold-is-not-a-type.md).
**Add no aggregate type.** The absence of `List`/`Finset`/`Prod` is an
inventory rather than a law, but the load-bearing correction is a different
one: **a finite sum does not need its index set to exist as a type — it needs a
FOLD over the index set, and a fold is a function.** `Int.sumMaps` and
`Int.prodRange_sumRange_expand` demonstrate it with a checked, axiom-free
theorem: the generalized distributive law, which is exactly the Cauchy–Binet
expansion step ADR-1135 recorded as inexpressible here.

## The three measurements the decision rests on

1. **The absence is an inventory.** `Nat.Pair` landed 2026-08-29 and
   `Nat.Primrec` 2026-08-31 (an inductive `Prop`, seven constructors).
   `Kernel::add_inductive` is an ordinary gate with an auto-generated,
   `infer`-checked recursor and a Lean-4.30 positivity check.
2. **An inductive costs ZERO axioms.** `Kernel::axiom_footprint`
   (`lean_pp.rs:1297`) filters the dependency closure to
   `Axiom | Opaque | Quotient`; `Inductive`/`Constructor`/`Recursor` are
   traversed and discarded. `check-trust-closure.py:114` and
   `nat_axiom_inventory.rs:202` agree. The real costs are that
   `inductive.rs` is inside the measured trusted CODE core, and that an
   inductive `Prop` admits no evaluation test.
3. **The kernel already ran this experiment and declined.** `Nat.Fin` exists
   (2026-08-23, 4 declarations + recursor) and has **zero non-test
   consumers** — 7 references, all in `nat_prelude_tests.rs`, 6 of them
   inventory-list entries. The pigeonhole apparatus built around it in the
   same file is stated over plain `Nat → Nat` with bounded quantifiers.

## Determinant multiplicativity

Reachable, and the aggregate was never the blocker. What remains, in order:
general-row expansion (ADR-1135's law 3) → the alternating property → the sign
under a row swap → multiplicativity. Three substantial cofactor inductions,
none an aggregate question. ADR-1135's other two bullets are also wrong (the
Leibniz sum is a writable term; a factorization *length* is a `Nat`), and both
corrections are recorded as **arguments, not landed work**.

## Next actions

- `Rat.sumMaps`: needs `Rat.prodRange` (absent) plus the same seven lemmas.
  Ordinary work, deliberately not done here.
- General-row expansion over `Rat.det` is the real next rung for the
  determinant, and it is not this lane's.

<!-- plan-section: landed-changes -->

| 2026-08-31 | `int_prelude/sum_maps.rs` | `Int.sumMaps` — a finite sum indexed by the FUNCTION SPACE `[0,m) → [0,n)`, folded by `Nat.rec` with the higher-order motive `fun _ : Nat => ((Nat → Nat) → Int) → Int` (the device `Rat.det` already uses). Eight axiom-free declarations. The map extension `cons k g` is built INLINE as a `Nat.rec` so both its equations are `Eq.refl` — the `Nat.beq` alternative puts an `i < m` side condition on every proof step. |
| 2026-08-31 | `int_prelude/sum_maps.rs` | **`Int.prodRange_sumRange_expand`** — the generalized distributive law at symbolic `m`, `n`, `c`: `prodRange (fun i => sumRange (c i) n) m = sumMaps m n (fun g => prodRange (fun i => c i (g i)) m)`. This is the Cauchy–Binet expansion step ADR-1135 called inexpressible. Admitted first attempt. The motive quantifies over `c` because the step applies the IH at `fun i => c (succ i)` — the third time this development has needed that shape (`prodRange_permute`'s σ, `det_congr`'s matrices). |
| 2026-08-31 | `int_prelude/sum_maps.rs` | `Int.sumRange_mul_right` / `Int.sumRange_mul_left` — pull a constant factor out of a signed finite sum. Both base cases were wrong in the DIRECTION on the first attempt (at `n = 0` the goal is `zero = mul zero z`, not the natural `mul zero z = zero`), which poisoned the whole prelude: 66 of 67 `int_prelude::` tests failed with one opaque `TypeMismatch` naming neither side. Found by toggling `declare_*` calls one at a time, not by reading the failure. |
| 2026-08-31 | `int_prelude/sum_maps_tests.rs` | Five evaluation tests, in their own file rather than appended to the 6,000-line shared `int_prelude_tests.rs`. Cardinality at seven `(m,n)` pairs including both `n = 0` cases; the full product separated from its DIAGONAL in both directions (9 against 5); both defining equations with the base map pinned; the expansion law at a concrete instance with both sides independently 9. A transposed index is deliberately NOT tested — a sum over every map is invariant under permuting the indices, so any such test is vacuous. |
| 2026-08-31 | `docs/research/09-decisions/adr-1310-…` | The decision: add no aggregate. Records the three measurements, the per-option reasoning (`List` / `Nat.Fin`-indexed / `Prod`), and the corrected sizing for determinant multiplicativity. |
| 2026-08-31 | 9 documents | Dated corrections quoting the stale text: ADR-1135 (the three-route wall), ADR-1120 ("no type in which to write that sum", "the encoding is forced"), `DEPTH-PROPOSAL-…` ("structural rather than a matter of effort"), `03-destinations/number-theory.md` (scoped, still correct), `graded-statement-families-…` (scoped), `spivak.md`, `rat_prelude/matrix_det.rs`, `nat_prelude/permutation.rs`, `docs/plan/status/general-n-determinant.md`. |
| 2026-08-31 | `artifacts/facts/` | `F:int-sum-maps`, `F:int-sum-maps-succ`, `F:int-prod-range-sum-range-expand` — all `proved`, footprint `[]`, statements headered and pinned (`header_exempt=0` holds). |
