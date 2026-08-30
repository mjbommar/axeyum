# Notes: 374-euler-theorem

Detail moved out of [`../status/374-euler-theorem.md`](../status/374-euler-theorem.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

The statement is a congruence (`ModEq`), and every piece of infrastructure
this proof needs — `Int.ModEq`, `Int.prodRange`, `Int.prodRange_permute`,
`Int.prodRange_congr_lt`, `Int.euler_unit_coprime`/`_injective` — already
lives in `int_prelude`. The decisive fact: **`Int.prodRange_permute`
(full-range permutation invariance) already exists, built for Wilson's
theorem**, while the equivalent lemma over `Nat.prodRange` does not exist
at all — `subset_product.rs`'s own doc names this exact absence as the
blocker and sizes the swap induction needed to build it at ~650 lines.

So: build `Int.prodRangeIf` (the `Int` counterpart of `Nat.prodRangeIf`,
same construction, `bool_select_int` in place of `bool_select_nat`) and
derive its permutation-invariance corollary FROM the already-proved
full-range `Int.prodRange_permute`, entirely avoiding the swap induction.
This is the lever ADR-0716's framing missed, and it is real: it converts a
~650-line missing induction into a corollary of two already-proved lemmas.

## What this lane built (landed, kernel-checked, axiom-free)

New file `crates/axeyum-lean-kernel/src/int_prelude/euler_theorem.rs`:

- `Int.prodRangeIf : (Nat → Bool) → (Nat → Int) → Nat → Int` — definition,
  mirrors `Nat.prodRangeIf` exactly (`Int.prodRange` folded over a
  `bool_select_int`-selected value, `Int.one` off the subset).
- `Int.prodRangeIf_zero`, `Int.prodRangeIf_succ` — defining equations, both
  `Eq.refl`.
- `Int.prodRangeIf_permute` — the headline: for `σ : Nat → Nat` an
  `InjectiveOn`/`MapsInto` self-map of `[0,n)` that additionally
  **preserves the predicate** on that range (`∀ i, Lt i n → Eq Bool
  (pred (σ i)) (pred i)`), `prodRangeIf pred f n = prodRangeIf pred (f ∘ σ)
  n`. Proved by one application each of `Int.prodRange_permute` (at the
  unrestricted selector) and `Int.prodRange_congr_lt` (rewriting the
  permuted selector's condition using the preservation hypothesis), bridged
  by a small `bool_select_int` congruence-in-the-condition helper. No
  subset-specific pigeonhole or swap induction needed anywhere.

All four declarations were **admitted by the kernel on the first attempt**
(no `TypeMismatch` iteration needed) — verified via
`cargo test -p axeyum-lean-kernel --lib int_prelude::` (52 passed, was 51,
before the evaluation test below; 52 total after). Coverage-checked by
`every_int_declaration_is_checked_and_axiom_free` (added to `derived_laws`
214→217 and `definition_names` 27→28, both **recounted** with
`scripts/recount-pinned-inventory.py`, not incremented by hand).

Registered in the fact ledger (`scripts/gen-kernel-facts.py --prelude
integer --date 2026-08-30`): `F:int-prodrangeif-zero`,
`F:int-prodrangeif-succ`, `F:int-prodrangeif-permute`. (The generator also
found 5 unrelated pre-existing unregistered integer theorems from other
lanes' work — `ediv_emod_unique_general`, `emod_eq_zero_iff_dvd_general`,
`emod_natabs_bound`, `emod_two_eq_zero_or_one`, `even_add` — deliberately
NOT emitted here; out of scope, and emitting them would risk colliding
with whichever lane owns them.)

### Evaluation test — the trusted gate cannot tell you a Definition is wrong

`Kernel::add_declaration` accepting `Int.prodRangeIf` proves it is
well-typed, not that it computes the right value (CLAUDE.md's own
standing lesson: a `Definition` with the right type can still compute
nonsense, e.g. `Nat.lor`'s absorbing-zero mistake). Added
`prod_range_if_computes_and_rejects_a_false_value` to
`int_prelude_tests.rs`:

- `pred i := Nat.beq i 2`, `f i := Int.ofNat (Nat.succ i)`, `n := 4` — a
  predicate that is genuinely **mixed** (true at exactly one of four
  indices), so a definition that silently ignored the predicate (folding
  the full product, or always excluding) would not survive it.
  `prodRangeIf pred f 4` reduces to `3` (only `i=2` contributes, `f 2 = 3`;
  the other three indices contribute the identity `1`).
- Paired with a discriminating negative control (mirrors
  `prod_range_computes_and_rejects_a_false_product`'s pattern exactly): the
  trusted gate must REFUSE the false claim that the same product is `2`.
  Verified it does (a `Declaration::Theorem` with a mismatched `Eq.refl`
  proof is rejected — `result.is_err()` asserted).

**Free-variable check**: `Int.prodRangeIf_permute` itself is fully
symbolic — every argument (`pred`, `f`, `σ`, `n`) is a genuinely free
kernel variable throughout its construction and proof, not a concrete
instantiation, so it is not subject to the "numerals hide defeq gaps"
failure mode. The evaluation test above is the separate, complementary
check (concrete instantiation, to catch a wrong `Definition`), per the
standing rule that a declaration needs BOTH checks — they fail on disjoint
defect classes.

**Largest numeral formed**: `4` (the evaluation test's range bound). All
proof construction elsewhere in this lane is symbolic (no concrete
magnitudes at all), so the "keep formed magnitudes small" hazard
(`gcd 512 1875` costing 25.6s, etc.) does not apply here.

## Numeric checks (re-executable)

No Python numeric pre-check was needed for this slice: the mathematical
content (a full-range permutation lemma implies a predicate-restricted one
when the predicate transports along the permutation) is a direct algebraic
identity, not a numerically-fragile claim like the CRT block-Fubini one
this session's other totient work had to re-verify. The Rust-level
evaluation test above (`4` numeral) is the executable check that stands in
for it here; re-run with:

```sh
cargo test -p axeyum-lean-kernel --lib \
  int_prelude::int_prelude_tests::prod_range_if_computes_and_rejects_a_false_value
```

## What does NOT land here — the precise remaining gap

Three more pieces, all real work, all documented in `euler_theorem.rs`'s
own module doc (read it before starting any of these):

1. **Bridging `Int.euler_unit_injective`'s bounded-`Int` hypotheses to the
   `Nat`-typed self-map `Int.prodRangeIf_permute` (and `Int.prodRange_permute`
   beneath it) quantifies over.** The unit-permutation map is
   `k ↦ emod (a*k) n : Int`; using it here needs a `Nat.ofNat`/`Int.natAbs`
   round trip to a genuine `Nat → Nat` function, plus re-deriving
   `Nat.InjectiveOn`/`Nat.MapsInto` in that shape from
   `Int.euler_unit_injective`'s `0 ≤ i → i < n → …` hypotheses (which are
   about `Int`-sorted `i`, `j`, not `Nat`-sorted indices).
2. **The predicate-preservation hypothesis is an IFF, and only one direction
   is proved.** `Int.euler_unit_coprime` gives `Coprime a n → Coprime k n →
   Coprime (emod (a*k) n) n` — one direction. The converse ("if the image
   is coprime, so was `k`") needs `a`'s own modular inverse (available
   *inside* `euler_unit_coprime`'s own proof via `Int.modEq_inverse_exists`,
   but not exposed standalone) applied a second time: `emod (a' * emod
   (a*k) n) n = emod (a'*a*k) n = emod k n = k` for `k` already in range.
3. **The final assembly**: `prodRangeIf pred (fun _ => a) n = pow a
   (countRange pred n)` (a new induction pairing `Int.pow`/`Nat.countRange`);
   pointwise-factoring `prodRangeIf pred (fun k => a * f k) n = mul
   (prodRangeIf pred (fun _ => a) n) (prodRangeIf pred f n)` (cheap —
   `Int.prodRange_mul` plus a case-split on the predicate); termwise `ModEq`
   transport from `emod (a*k) n` back to `a*k` (`Int.modEq_prodRange`-shaped
   machinery already in `prod.rs`); and cancellation of `prodRangeIf pred id
   n` via `Int.modEq_cancel` (needs that product coprime to `n`, itself a
   short argument: every factor is coprime to `n` by construction, and a
   product of things coprime to `n` is coprime to `n`).

None of items 1–3 touches `Nat`; all belong in `int_prelude`, most likely a
sibling file to `euler_theorem.rs` (or extending it). Per the standing
"a handoff's blocked-on-X is a claim about one route, not the target"
lesson: verify each of these in-tree before treating it as real work, and
consider whether a different route avoids one of them (in particular, item
1's `Nat`/`Int` bridging might already exist somewhere for a different
purpose — check `nat_abs`/`of_nat` lemma files before building it).

## Commands run

```sh
cargo check -p axeyum-lean-kernel                          # ok
cargo test -p axeyum-lean-kernel --lib int_prelude::        # 52 passed, 0 failed
cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings  # clean
rustfmt --edition 2024 <the three touched files>
python3 scripts/recount-pinned-inventory.py crates/axeyum-lean-kernel/src/int_prelude/int_prelude_tests.rs   # 217/28/28/0, all matched
python3 scripts/validate-facts.py                           # 0 errors, 2268 facts (was 2265)
python3 scripts/check-fact-depends-derived.py --fix          # nothing to fix
```

Not run (out of scope / no `nat_prelude` or `Nat.prodRangeIf` edits made):
`cargo test -p axeyum-lean-kernel --lib nat_prelude::`.
