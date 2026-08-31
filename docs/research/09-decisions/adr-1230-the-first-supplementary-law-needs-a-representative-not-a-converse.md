# ADR-1230: the first supplementary law's non-residue half needs a natural representative, not the converse of Euler's criterion

Status: accepted
Date: 2026-08-31
Index-summary: The `p = 3 (mod 4)` half of the first supplementary law was
reachable today; the `p = 1 (mod 4)` half needs a witness, and Wilson's theorem
supplies one without the converse of Euler's criterion.

## Context

The **first supplementary law of quadratic reciprocity** says that for an odd
prime `p`, `-1` is a quadratic residue mod `p` exactly when `p = 1 (mod 4)`.

Two things that already existed made it worth attempting:

- `Int.euler_criterion_neg_one_imp_not_residue` (`qr_criterion.rs`): for an odd
  prime, a half-power `= -1` rules out residue-hood. This is the NECESSARY
  direction of Euler's criterion and it is proved, axiom-free.
- `Int.wilson` (`wilson.rs`): `(p-1)! = -1 [p]`, proved, axiom-free.

And one thing that did not: the CONVERSE of Euler's criterion
(`a^((p-1)/2) = 1 => a is a residue`), which `qr_criterion.rs`'s module doc
records as needing a primitive root or a root-counting argument over a
polynomial ring this kernel has no `List`/`Finset` to state.

## Decision

Land the **non-residue half** — `p = 3 (mod 4) => -1 is not a residue` — and
do NOT claim the other half. Both new declarations are axiom-free:

| declaration | statement |
| --- | --- |
| `Int.isQuadraticResidue_of_modEq` | `∀ n a b, ModEq n a b → IsQuadraticResidue n a → IsQuadraticResidue n b` |
| `Int.firstSupplementaryLawNotResidue` | `∀ m, PrimeCond (succ (mul 2 m)) → Nat.Odd m → Not (IsQuadraticResidue (ofNat (succ (mul 2 m))) (neg one))` |

`int_prelude/first_supplementary.rs`.

### The obstruction that turned out not to be one

The blocker in the way was not the converse. It was that **every
quadratic-residue theorem in `qr_criterion.rs` is stated over a NATURAL
representative** `ofNat aa` with `0 < aa < pp`, and `-1` is not a natural. The
supplementary laws are about `-1`.

The fix is one small lemma nobody had written: `IsQuadraticResidue` respects
`ModEq` in its second argument. The witness is unchanged, so it is
`Int.ModEq.trans` and an `Exists` re-introduction, about 25 lines. With it, the
detector is applied at `aa := 2*m` — `-1`'s canonical representative mod
`p = 2m+1` — and the conclusion transported back.

This is the "blocked on X" pattern CLAUDE.md warns about, in a mild form: the
handoff said the converse was needed for the biconditional, which is true, and
a reader can slide from there into thinking neither half is reachable.

### `Nat.Odd m`, not `p mod 4 = 3`

`Nat.div` and `Nat.mod` are stuck at symbolic arguments, so a hypothesis
`p mod 4 = 3` is a liability — a proof handed it has to reconstruct `p`'s
constructor shape from it. `Nat.Odd m` runs the other way: its witness is an
EQUATION `m = succ (k+k)`, which hands over the shape directly.

That is not cosmetic. `Le 1 m` — which the statement needs twice — is
`succ_le_succ (zero_le (k+k))` transported backwards along that witness, with no
arithmetic and no division. This is the same lever that closed the second
supplementary law (ADR-1150).

### The side conditions come from oddness, not primality

`Int.euler_criterion_neg_one_imp_not_residue` needs four side conditions at
`aa := 2*m`, and where each comes from matters at the `m = 0` boundary:

| condition | source | holds at `m = 0`? |
| --- | --- | --- |
| `0 < 2*m` | `Le 1 m` from `Odd m` | **no** |
| `2 < p` | `Le 1 m` from `Odd m`, then `add_le_add` | **no** |
| `2*m < p` | `Nat.lt_succ_self` — `p` is literally `succ (mul 2 m)` | yes (`0 < 1`) |
| `p - 1 = m + m` | `two_mul_eq_add_self`, no rewrite needed | yes |

`p - 1 = m + m` needs no bridging step at all: `Nat.sub` recurses on its SECOND
argument (`sub x (succ j) = pred (sub x j)`), so `sub (succ (mul 2 m)) 1`
iota-reduces to `mul 2 m`, and `two_mul_eq_add_self` — which
`second_supplementary.rs` already had, private — is accepted at the stated type
by def_eq.

**The first draft of this ADR said all three of the first three fail at
`m = 0`.** That is wrong: `2*m < p` is `0 < 1` and holds. The C4 row of the
checks script below is what caught it, and the module doc has been corrected.
Recording it because it is the third time this session a "verified" claim in a
plan was not.

## Numeric verification

Re-runnable, and it fails when the thing it checks is false:

```sh
python3 docs/research/09-decisions/adr-1230-first-supplementary-checks.py
```

Six claims over the 94 odd primes below 500, each paired with a mutated form
that MUST be refuted; the script exits 1 if a mutation survives. Current run:

```
  [ok ] C1  -1 is a residue mod p  <=>  p = 1 (mod 4): 0 failures of 94
  [ok ] C2  p = 2m+1:  m odd  <=>  p = 3 (mod 4): 0 failures of 94
  [ok ] C3  (2m)^m = (-1)^m (mod p): 0 failures of 94
  [ok ] C4  0 < 2m < p and 2 < p; two of the three fail at m = 0: 0 failures of 97
  [ok ] C5a (p-1)! = (-1)^m (m!)^2 (mod p): 0 failures of 94
  [ok ] C5b m even  =>  (m!)^2 = -1 (mod p), witness m!: 0 failures of 44
  ... every control refuted
```

C5b's control is the one that matters most, because it is the claim that would
make the unproved half look free: extending `(m!)^2 = -1` to ODD `m` fails at
all 50 such primes.

## What was measured

Eight mutations, in the two columns the mutation standard asks for. Every one
was caught, and the two columns are populated by genuinely different mechanisms.

| mutation | outcome |
| --- | --- |
| M1 sign lemma `pow_neg_one_of_odd` -> `_of_even` | **A**: kernel rejected |
| M2 conclusion `-1` -> `+1` | **A**: kernel rejected |
| M3 Euler detector applied at `aa := m` | **A**: kernel rejected |
| M4 `one_le_of_odd` weakened to `0 <= m` | **A**: kernel rejected |
| M5 conclude at `ofNat (2m)`, skip the transport | **B**: kernel ADMITTED, the test failed |
| T1 parity row `p = 5` expectation flipped | **B**: the test failed |
| T2 negative control re-aimed at `-1` | **B**: the test failed |
| T3 refutability control re-aimed at `-1` | **B**: the test failed |

M5 is the one worth designing for. It produces a statement the kernel is
perfectly happy with, and which is **true** — it is exactly what the Euler
detector hands back — but it is not the first supplementary law, because that
law is about `-1`. Nothing in the axiom footprint, the prelude build, or the
`every_int_declaration_is_checked_and_axiom_free` inventory can see the
difference. Only the test's symbolic shape check can.

### What the controls do NOT catch

- **Satisfiability of the hypotheses.** The test never constructs a
  `PrimeCond` proof, so a mutation making `PrimeCond p ∧ Odd m` unsatisfiable
  would leave a vacuously-true theorem the test would still pass. It is not
  unsatisfiable (`m = 1` gives `p = 3`), and the numeric script's C1/C2 rows
  exercise exactly those primes, but that is evidence from outside the kernel.
- **Hiding place 2.** `one_le_of_odd`, `two_le_two_mul` and
  `neg_one_modeq_two_mul` are private helpers with no declarations of their
  own, so `check-shape-duplicates.py` cannot see them and nothing would report
  it if a later lane re-derived any of them. This is not hypothetical here:
  `transposition.rs`'s `injective_of_involutive`, named in the handoff below,
  is exactly such a helper and would have been re-derived by anyone searching
  for a reflection lemma by name.

## The half that is NOT proved, and the route to it

`p = 1 (mod 4) => -1 IS a residue` needs a **witness**, and this is where the
converse of Euler's criterion would normally be used. It can be avoided
entirely, and the route is worth writing down because the pieces are almost all
present:

`(p-1)! = m! · ∏_{j=m+1}^{2m} j`, and each `j` in the upper half is `= -(p-j)`
with `p-j` running over `1..m`, so `(p-1)! = (-1)^m (m!)^2`. Wilson's theorem
makes the left side `-1`, so at EVEN `m` — that is, `p = 1 (mod 4)` —
`(m!)^2 = -1 [p]` and **`m!` is the residue witness outright.** C5a and C5b
above verify both steps at 94 and 44 primes respectively.

What exists already:

- `Int.wilson` — proved, axiom-free.
- `Int.prodRange_permute` — the reversal `k -> m-1-k` on `[0,m)`, given
  `InjectiveOn`/`MapsInto`.
- `Int.modEq_prodRange_lt` — the pointwise congruence, bounded-index form.
- `Int.prodRange_scaledIndexEqPowMulFactorial` at `a := -1` — collapses
  `∏_{k<m} ((-1)·(k+1))` to `(-1)^m · m!` in one step, no induction.

What does **not** exist, and is the single blocker:

> **a `prodRange` SPLIT** —
> `prodRange f (add a b) = mul (prodRange f a) (prodRange (fun k => f (add a k)) b)`

`prod.rs` has `prodRange_shiftFront` (peels one FRONT term) and
`prodRange_succ` (peels one BACK term); neither splits at a symbolic point.
It is an induction on `b` with `prodRange_succ`, and `add a (succ b)` reduces to
`succ (add a b)` definitionally because `Nat.add` recurses on its right
argument, so no `add_assoc` is needed.

For the reflection's `InjectiveOn`, one thing WAS checked and is worth the next
lane's attention: `nat_prelude/transposition.rs` carries a private
`injective_of_involutive` — "any involution is injective", three lines, generic
over the map. The reflection `k -> pred m - k` is an involution on `[0,m)`, so
that argument applies verbatim; it needs promoting to `pub(super)`, not
rebuilding. `Nat.conjugate_injective` in the same file is the already-public
form if the involution law can be supplied. The reflection's `MapsInto` was NOT
checked and should not be assumed — `Nat.sub`'s truncation is exactly where that
kind of bound gets fiddly.

This lane did not attempt the split. The claim here is only that the route
avoids the converse, and C5a/C5b are the evidence for that.

## Consequences

- The first supplementary law is HALF landed. Say "the non-residue half", never
  "the first supplementary law", and never that `-1`'s residue-hood is decided.
- `Int.isQuadraticResidue_of_modEq` is general and reusable: any future
  quadratic-residue theorem stated over a natural representative can be carried
  to the `Int` value it represents by it.
- `second_supplementary::two_mul_eq_add_self` and `odd_predicate`, and
  `euler::int_exists_intro`, are now `pub(super)`. They were private and
  identical to what this module needed; extracting beat re-deriving.
