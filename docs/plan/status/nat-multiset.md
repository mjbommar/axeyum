# Lane: nat-multiset — the multiplicity carrier that makes prime-factorization uniqueness statable

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for uniqueness`, nat-multiset, 2026-09-02).**

`docs/formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md`
§6 concedes that uniqueness of prime factorization "is not expressible here at
all". **It is now a checked, axiom-free theorem** —
`Nat.Multiset.count_eq_of_prod_eq`. Nothing in the kernel changed; the
concession was about a REPRESENTATION. A multiset over ℕ is a multiplicity
function that is eventually zero, and `Nat.Multiset`
(`crates/axeyum-lean-kernel/src/nat_prelude/multiset.rs`, ADR-1520) is exactly
that: a one-constructor inductive `mk : (Nat → Nat) → Nat → Multiset` whose
`count` truncates at the bound in its own definition. Order is never
represented, so there is nothing to quotient by and no `propext`/`Quot.sound`
appears — `Kernel::axiom_footprint` is `[]` for all ten `Nat.Multiset.*`
theorems, read from the kernel via `theorem_axiom_footprint`.

**Landed:** 24 declarations. The carrier plus `raw`/`bound`/`count`/`zero`/
`singleton`/`add`/`Mem`/`prod`/`card`/`eqBelow`/`beq`; the three `count` laws;
`beq_refl`/`beq_comm`; and the valuation chain
(`Nat.Multiset.pow_count_dvd_prod`, `not_pow_succ_count_dvd_prod`,
`count_eq_of_prod_eq`). Five general `Nat` lemmas fell out and are declared
there because it is their first consumer: `pow_dvd_pow_of_le`,
`dvd_prodRange_of_lt`, `prime_pow_dvd_of_dvd_mul_of_not_dvd`,
`exponent_unique_of_exact_dvd`, `beq_comm`.

**Not attempted, and this is the handoff:** the COMPUTED form — a
`Nat.factorization` by trial division, `prod (factorization n) = n`, and
`0 < count (factorization n) p → prime p`. Uniqueness needs none of it, which
is why it landed first. The blocker for the computed form is
`prod (add m₁ m₂) = prod m₁ * prod m₂`, a product-regrouping law across three
different bounds; `Int.prodRange_split` exists on the Int side and
`Nat.prodRangeIf` on the Nat side, and **whether either transports was not
tested by this lane**. The sibling route (converting
`Nat.exists_prime_factorization`'s `(k, f)` witness into a multiset by
`countRange (fun i => beq (f i) q) k`) needs the same law, so it is not a way
around it. `Nat.minFac`/`Nat.minFacAux` already exist and are the natural
trial-division engine.

**Measurements.** `nat_prelude::` 333 passed, 0 failed (`--release`,
`--test-threads=4`). `python3 scripts/validate-facts.py` 2583 facts, 0 errors.
Nat prelude cold build, `prelude_build_timing`, min of 4 runs on a box at load
13–16: branch point `5c8eaf7b8` **640,693 µs** vs lane HEAD **640,023 µs** — no
measurable change; individual runs ranged to 1.4 s on both sides, so read the
minimum, not the mean. Note the "after" tree also carries everything merged from
`main` today, so this is not a clean isolation of 24 declarations.

<!-- plan-section: landed-changes -->

| 2026-09-02 | nat-multiset | `Nat.Multiset` carrier + 5 evaluation tests (`multiset.rs`, `multiset_tests.rs`) |
| 2026-09-02 | nat-multiset | the three `count` laws + 4 general `Nat` lemmas (`pow_dvd_pow_of_le`, `dvd_prodRange_of_lt`, `prime_pow_dvd_of_dvd_mul_of_not_dvd`, `exponent_unique_of_exact_dvd`) |
| 2026-09-02 | nat-multiset | **uniqueness of prime factorization** as multiplicity agreement (`Nat.Multiset.count_eq_of_prod_eq`), axiom-free |
| 2026-09-02 | nat-multiset | `Nat.Multiset.beq` reflexive and symmetric; `Nat.beq_comm` |
| 2026-09-02 | nat-multiset | ADR-1520 and seven facts, each checker verified to fail when the theorem is absent |
