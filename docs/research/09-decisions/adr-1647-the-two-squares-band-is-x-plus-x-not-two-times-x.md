# ADR-1647: The two-squares band is `x + x`, not `2 * x`, and the descent's termination certificate reads the factorisation

Status: accepted
Date: 2026-09-05
Index-summary: The Z order shelf Fermat's two-squares descent was blocked on lands as 25 axiom-free laws in `int_prelude/order_squares.rs`. Two design calls: every bound is spelled `Int.add c c` and never `Int.mul (ofNat 2) c`, which removes every numeral from the halving step (the only division in the argument); and the termination lemma `Int.descentMultiplierBounds` takes the FACTORISATION `m*q = c^2 + e^2` rather than the measure, so it composes with `Int.descentStep` without either half constructing a quotient. Two thirds of the obstruction ADR-1633 recorded was already stale: `Int.nat_abs_le_iff_mul_self_le` and `Int.mul_le_mul_of_nonneg_left` both existed. The descent's ENTRY POINT also lands (`Int.exists_small_multiple_of_sq_add_one`), which `two_squares.rs`'s module doc wrongly claims already existed -- that declaration does not exist. Fermat's theorem itself still did NOT land; the three remaining pieces plus one Nat bridge are sized in `F:int-fermat-two-squares`.
Index-status: accepted

- **Lane**: `int-order-two-squares` (W3-10, second slice)
- **Supersedes**: nothing. **Amends**: the sized obstruction recorded in
  [ADR-1633](adr-1633-the-two-squares-descent-splits-into-algebra-that-is-free-and-an-order-that-does-not-exist.md)
  and in `F:int-fermat-two-squares`.

## Context

W3-10's first slice landed the algebraic half of Euler's descent — the
Brahmagupta–Fibonacci identity, `Int.modEq_descent_cross_terms`, and
`Int.descentStep` — and recorded the remaining obstruction as an ordering
argument over ℤ:

> this prelude has no `Int` absolute-value order lemmas at all: `natAbs` exists
> and `Int.le`/`Int.lt` exist, but `natAbs_le_iff`, `mul_le_mul` over ℤ and
> `sq_le_sq` do not.

**Two thirds of that was already false when it was written.** Measured
2026-09-05 with a freshly built `shape_search` (`declarations=3236`, positive
control `Int.descentStep` FOUND, so the index post-dates the merge that added
it):

- `Int.nat_abs_le_iff_mul_self_le : natAbs a ≤ natAbs b ↔ a*a ≤ b*b` landed on
  2026-09-01 in `nat_abs_mirrors.rs`, together with its `<` and `=` siblings —
  the `integer-absolute-value` held-out family was drawn and scored that day;
- `Int.mul_le_mul_of_nonneg_left`, `Int.add_le_add`, `Int.add_le_add_iff_left`
  /`_right`, `Int.le_total`, `Int.le_antisymm`, `Int.lt_of_le_of_ne`,
  `Int.mul_pos`, `Int.sq_nonneg`, `Int.emod_nonneg` and `Int.emod_lt_of_pos`
  were all already declared.

Only `sq_le_sq` was genuinely absent, and the real gap was not any of those
names: it was the **shape** of the bound. Nothing turned a two-sided band
`−m ≤ x ≤ m` into `x² ≤ m²`, nothing produced a representative of `a mod m`
inside that band, and nothing halved an inequality.

This is another instance of a lane nearly re-deriving what exists, the failure
mode `docs/contributor-guide/finding-existing-lemmas.md` exists for. The lesson
that generalises: **an obstruction note in a fact or a module doc is a
claim with a timestamp, and a repository where other lanes land declarations
daily invalidates such claims silently.** Re-measure before you build; the
authority of the note is exactly what makes a stale one expensive.

## Decision

### 1. Every bound is spelled `Int.add c c`, never `Int.mul (ofNat 2) c`

`2·|c| ≤ m` and `−m ≤ c + c ≤ m` are the same statement about `c`. The second
is the one the existing shelf can **move**:

- doubling an inequality is literally `Int.add_le_add h h` — no `0 ≤ 2` side
  condition, no numeral;
- `ring::int` never has to normalise a numeral coefficient;
- the halving step `Int.le_of_add_le_add_self : a + a ≤ b + b → a ≤ b` is
  provable by `Int.le_total` plus `add_le_add_iff_left`, with **no cancellation
  of a constant** anywhere.

That last point is the one that pays. In the `mul (ofNat 2)` spelling the
strict decrease needs `4·(c²+e²) ≤ 2m² ⟹ 2·(c²+e²) ≤ m²`, i.e. cancelling the
constant `2` from both sides, which needs `0 < 2` as an `Int.lt` at a numeral
plus a `le_of_mul_le_mul_left`. In the `add` spelling the same step is
`(S+S)+(S+S) ≤ (m·m)+(m·m) ⟹ (S+S) ≤ m·m` — one application of a lemma with no
numerals in it at all.

**This is not a weakening**, and the trade is explicit: the statement reads
slightly further from the textbook so that the proof reads much closer to the
shelf.

### 2. The termination lemma takes the FACTORISATION, not the measure

`Int.descentMultiplierBounds : ∀ m q c e, 0 < m → m*q = c*c + e*e →`
`(the four band hypotheses) → 0 ≤ q ∧ q < m`.

The obvious alternative is a lemma about the measure alone
(`c² + e² < m²`, which is also declared, as
`Int.sq_add_sq_lt_sq_of_bounds`) and to let the caller divide by `m`. We do not
do that, for the same reason `Int.descentStep` takes its quotients `u`, `w` as
**hypotheses** rather than constructing them (ADR-1633): this prelude has no
division that returns a witness, and every construction that would produce one
has to be built from `Int.dvd`'s existential anyway. Taking `q` as a hypothesis
means the two halves of the descent compose without either one constructing a
quotient, and the caller supplies `q` once from the divisibility fact it
already has.

### 3. The centered representative is an existential, not a `bmod` definition

Lean core defines `Int.bmod` as a function with a decidable `if`. This prelude
has no `Decidable` instance for `Int.le`, so a function would have needed one
built first. `Int.le_total` supplies the split as an `Or` and **both branches
build a witness**, so `Int.exists_centered_representative` is a plain
`Or.elim` into `Exists.intro`. A function can be added later if a caller needs
to compute with it; nothing in the descent does.

### 4. Held-out rows are named and not declared

`Int.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg` and its three sign siblings,
and `Int.mul_le_mul_of_natAbs_le`, are rows of the **held-out**
`integer-natcast` family; `Int.lt_of_sum_four_squares_eq_mul`,
`Nat.sum_four_squares` and `Nat.Prime.sum_four_squares` are rows of the
held-out `descent-and-well-ordering` family; `Nat.sq_add_sq_mul` is a row of
the held-out `power-and-square-decompositions` family
(`artifacts/autogenesis/nursery-v2-extension.json` carries the partition, and
it — not any fact file — is the split authority). **None of them is declared**,
and no lemma here is stated in their shape:
`Int.sq_le_sq_of_neg_le_of_le` takes `−b ≤ a ≤ b` in one variable pair, which
is a different proposition from any four-variable product bound.

`Int.natAbs_le_iff_mul_self_le` IS a held-out row, but its family was drawn and
scored on 2026-09-01, so it is already in the environment and is *used*, not
re-proved.

## Consequences

Twenty-five laws land in `crates/axeyum-lean-kernel/src/int_prelude/order_squares.rs`,
all axiom-free, all registered in `int_prelude_tests::derived_laws`
(294 → 319) so the environment-derived every-declaration sweep covers them.

The ordering half of Fermat's two-square theorem is **done**, and so is the
descent's **entry point**: `Int.exists_small_multiple_of_sq_add_one` turns
`x·x ≡ −1 (mod p)` into a `k` and `c` with `k·p = c² + 1²` and `0 < k < p`.
Centering `x` first is what makes that available — the uncentered `x` has no
bound at all, which is precisely why the previous slice could not close it.
Primality is deliberately not a hypothesis of it: everything on that leg needs
only `0 < p` and `1 + 1 ≤ p`.

What remains for `Int.fermatTwoSquares` is three unbuilt pieces plus one
bridge, none blocked on a missing capability, all sized in the notes of
`F:int-fermat-two-squares`: the `Nat` bridge from a prime `p = 2m+1` with
`Nat.Even m` to `0 < p` and `1 + 1 ≤ p`; the divisibility `m ∣ c² + e²` that
produces the NEXT multiplier; the `q ≠ 0` argument (the only step that
consumes primality); and the `Nat.strongInduction` assembly.

**One correction this ADR records for the record**: `two_squares.rs`'s module
doc states that `declare_exists_mul_isSumOfTwoSquares_of_residue` — the entry
point — already landed. It does not exist. The name occurs exactly once in the
file, inside that doc comment, and is not in `declare_two_squares_all`. That
file is left untouched by this lane (a sibling lane may be editing it); the
correction lives here, in this module's own doc, and in the fact.

## The guard, and why the mutation table is coarse

Every statement mutation of a *proved* declaration in this codebase is caught
by the kernel rather than by a test, because the proof term is built to match
the statement exactly. Both mutants this lane was asked to run behave that way:

| mutant | outcome | kills |
| --- | --- | --- |
| `centered_body`'s upper bound `le (c+c) m` → `lt (c+c) m` (the boundary case) | prelude REJECTED | 119 of 122 |
| `sq_add_sq_lt_sq_of_bounds`' conclusion `lt S (m*m)` → `lt S m` | prelude REJECTED | 119 of 122 |

A kill count of 119/122 is a real observation but a coarse one, and it says
nothing about the case that actually worries us: a mutation that changes the
statement AND the proof consistently, leaving the build green. That is what
`order_squares_tests::order_squares_declarations_state_the_intended_types` is
for — it rebuilds all 25 `∀`-telescoped types independently and compares each
against the type the **environment** stores, and asserts `checked == 25` so a
deleted row fails rather than passing quietly.

**That guard was mutation-measured, and it is the informative row.** Changing
the pin's own expected conclusion for `sq_add_sq_lt_sq_of_bounds` from
`lt S (m*m)` to `lt S m` — leaving the declaration alone, so the prelude still
builds — kills **exactly one** test, that one: 121 passed, 1 failed.
