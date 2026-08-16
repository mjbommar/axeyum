# Lane: int-keystone — constructing ℤ over the proved ℕ development

<!-- plan-section: lane-status -->

**Lane state (`WIP`, int-keystone, 2026-08-14).** ℤ is now *constructed*, not
asserted: `Int` is an inductive over `Nat` (`Int.ofNat` / `Int.negSucc`), every
operation is a checked definition, and `integer` went **34 axioms → 6**
(`opaque=0 quotient=0` throughout). 20 laws are theorems with an **empty**
`Kernel::axiom_footprint`, including the headline `Int.no_int_between` —
discreteness, which the integer-cut route previously assumed — and `Int.eq_em`,
ADR-0106's decidable integer equality, which is now derived from constructor
injectivity and discrimination plus `Nat.beq` rather than assumed. Controls held:
`nat_theorem_inventory` still prints 119 theorems with byte-identical types and
`nat: axiom=0 opaque=0 quotient=0`. Five integer facts landed in
`artifacts/facts/`, the first this ledger has carried.

Next is the `Int.subNatNat` **borrow** sub-development
(`subNatNat m n = subNatNat (m+k) (n+k)`, and a characterization of when it
returns `ofNat`). That single missing piece is the blocker on four of the six
remaining: `add_assoc`, `left_distrib`, `add_le_add` and
`add_lt_add_of_le_of_lt`. `mul_assoc` needs the sign bookkeeping of
`negOfNat (m*n)` across eight branches. Hardest and last:
`euclidean_decomposition`, which needs integer division.

Unchecked and flagged rather than assumed: **no independent Lean binary read the
exported module.** No `lean` is installed here, so
`diophantine_module_checks_in_real_lean` and its siblings take the skip path and
report `ok`. The module grew 1,004,665 → 1,047,668 bytes because `Int` is now an
inductive and now carries proof terms for the derived laws. Anyone with Lean
should run those suites with `AXEYUM_REQUIRE_LEAN=1`.

Cost recorded: `build_int_prelude` now builds the `Nat` prelude first, so
`IntReconstructCtx::new` is ~52 ms slower per fresh context. Splitting `Nat` so
`Int` pulls only arithmetic and order (not gcd/Bézout) would recover most of it.

Full reasoning, including why the setoid quotient of ℕ×ℕ loses in this kernel:
[`docs/mathematics-2026-08/diary-int-keystone.md`](../../mathematics-2026-08/diary-int-keystone.md).

<!-- plan-section: landed-changes -->

| 2026-08-14 | `229cceb1e` | ℤ constructed over the proved ℕ development: `Int` inductive + operations as checked definitions, 20 laws derived with empty axiom footprints — including ADR-0106's decidable integer equality. `integer: axiom=34 → 6`. |
