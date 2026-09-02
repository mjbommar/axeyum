# Lane: countrange-bij-cross-bound — the cross-bound `countRange` law ADR-1558 sized

<!-- plan-section: lane-status -->

**DONE (`countrange-bij-cross-bound`, 2026-09-02).** Built and kernel-checked
the ℕ lemma ADR-1558 named as the one genuinely missing piece under the
`Rat.rank = Rat.rankCols` bridge, plus its base case and the four-hypothesis
specialization a consumer usually wants. **Three new theorems, no new
`Definition`, all axiom-free.** `nat_prelude::` **400 passed, 0 failed** (395
baseline + 5 new tests). Clippy clean on `axeyum-lean-kernel --all-targets`.

Note on the name: lane **344** (`countrange-bijection`, 2026-08-30) already
owns that file, so this lane took its own number and a distinguishing suffix.
The two are unrelated: 344 landed `countRange_permute`, the SAME-bound
permutation law; this lane landed the CROSS-bound one.

## What landed

```text
Nat.countRange_bij :
  ∀ (p q : Nat → Bool) (σ τ : Nat → Nat) (n m : Nat),
    (∀ i j, Lt i n → p i = true → Lt j n → p j = true →
       Eq Nat (σ i) (σ j) → Eq Nat i j) →
    (∀ i, Lt i n → p i = true → And (Lt (σ i) m) (q (σ i) = true)) →
    (∀ j, Lt j m → q j = true → And (Lt (τ j) n) (p (τ j) = true)) →
    (∀ i, Lt i n → p i = true → Eq Nat (τ (σ i)) i) →
    (∀ j, Lt j m → q j = true → Eq Nat (σ (τ j)) j) →
    Eq Nat (countRange p n) (countRange q m)
```

- **`Nat.countRange_eq_zero_of_all_false`** — `(∀ k, Lt k n → f k = false) →
  countRange f n = 0`. The base case's collapse, and the `false` twin
  `Nat.countRange_const_true` never had. Three-line induction. The route
  through `countRange_compl` also works but needs an `add`-cancellation this
  one does not.
- **`Nat.countRange_bij`** — the headline, above.
- **`Nat.countRange_bij_of_inverse`** — `σ` and `τ` mutually inverse
  EVERYWHERE, four hypotheses, **no injectivity** (it follows: `σ i = σ j` ⇒
  `τ (σ i) = τ (σ j)`). Derived from the headline in one application, not
  re-proved. This is the shape a consumer usually has, because a mutually
  inverse pair is normally exhibited by a formula whose inverse property is
  unconditional.

All in `crates/axeyum-lean-kernel/src/nat_prelude/count_range_bij.rs`; tests in
the sibling `count_range_bij_tests.rs`.

## Why the statement has this shape

`Nat.injectiveOn` and `Nat.mapsInto` (`finite.rs`) are **self-map notions on
one shared bound** and structurally cannot express a map from `{i < n | p i}`
into `{j < m | q j}`. So the hypotheses are their selected-set relativizations,
written out inline — no new `Definition`, which is why nothing here can be
well-typed and mean something else.

**Surjectivity is constructive and never an `Exists`.** This is not a style
preference. The induction removes one point from `q`'s selected set at each
step and hands the smaller predicate to the induction hypothesis; an
existential witness at `succ n` carries no computational relationship to the
one at `n`, so the induction could not carry a coherent inverse downward. The
explicit `τ` can be reused unchanged at every step, and is.

## The route (for whoever generalizes it next)

Induction on `n`, with `p` and `m` held OUTSIDE the recursion and the motive
generalized over `q`, `σ`, `τ`. The step moves `q`, not `p` — generalizing over
`p` instead does not close.

- **`n = 0`** — `τ`'s `MapsInto` sends every selected `j < m` into `[0,0)`,
  refuted by `not_lt_zero`, so `q` is false on `[0,m)`.
- **`succ n`, `p n = false`** — same `q, σ, τ`; the only real step is that
  `τ j = n` would force `p n = true`.
- **`succ n`, `p n = true`** — `j0 := σ n` is removed from `q`. The removal is
  the **`Bool`-valued analogue of `finite.rs`'s `point_override`**: the same
  cascaded-`Nat.ble` order comparison, never `Nat.beq`, substituting
  `Bool.false` at `j0`. `Nat.countRange_point_change` then pays for it in ONE
  step (`countRange q' m + 1 = countRange q m`), which is why this file needs
  no counting apparatus of its own — the same reason `count_range_permute.rs`
  is far shorter than its `Int` counterpart.

`Nat` has no packaged three-way trichotomy; `lt_or_ge` composed with
`lt_or_eq_of_le` is the split, and this file has a local `split_against`
helper for it.

## Evidence, and what the negative control actually shows

Five tests, on disjoint defect classes. The two worth naming:

- **The concrete instance discharges all five hypotheses**, from the prelude's
  own `le_succ_succ` / `le_of_ble_eq_true` / `ble_eq_true_of_le` /
  `le_of_succ_le_succ` / `succ_pred_of_pos` — not assumed. `p := (1 ≤ ·)` on
  `[0,3)` selects `{1,2}`, `q := (2 ≤ ·)` on `[0,4)` selects `{2,3}`, `σ :=
  succ`, `τ := pred`. The test also asserts `countRange (1 ≤ ·) 4 = 3 ≠ 2`, so
  "cross-bound" is not decoration over an instance where the bound never
  mattered.
- **The negative control refutes rather than merely disagreeing.** At
  `σ := fun _ => 3` the conclusion is false by evaluation (2 against 1), and a
  closed term of type `H1(σ) → False` type-checks — so the injectivity
  hypothesis is UNINHABITED and cannot be discharged at all. The same
  refutation is then required to FAIL at an injective `σ`; without that
  assertion the control would pass for a perfectly injective map and would be
  measuring nothing.

Facts: `F:nat-countrange-eq-zero-of-all-false`, `F:nat-countrange-bij`,
`F:nat-countrange-bij-of-inverse`. Each checker greps the RENDERED TYPE and
pins the row count at 8 (one per prelude building the naturals) — the name
alone does not discriminate, because `Nat.countRange_bij` is a prefix of
`Nat.countRange_bij_of_inverse`, and the two share a conclusion.

## What is NOT done, precisely

**The `Rat.rank = Rat.rankCols` bridge is still open, and this lane did not
narrow it beyond the ℕ half.** ADR-1558's verdict was that the bridge needed
(a) a cross-bound counting law and (b) the pivot-row ↔ pivot-column bijection
(ADR-1554 obligation 4). This lane closed (a) only. With it, the bridge becomes
"supply the bijection and its inverse, and show each maps selected to
selected" — four obligations in the `countRange_bij_of_inverse` shape if the
row↔column correspondence is exhibited by a formula, five otherwise. Nothing
about matrices was touched here, deliberately.

Two things a consumer should know before reaching for the derived form:
`succ`/`pred` do **not** satisfy its totality hypothesis (`succ (pred 0) = 1`),
so that pair needs the general law; and the general law's hypotheses constrain
`σ` and `τ` **only** on the selected sets, so a consumer owes nothing about
either map elsewhere.

<!-- plan-section: landed-changes -->

| 2026-09-02 | countrange-bij-cross-bound | `Nat.countRange_bij`, the cross-bound counting law: a constructive bijection between two selected sets at two different bounds equates their counts |
| 2026-09-02 | countrange-bij-cross-bound | `Nat.countRange_eq_zero_of_all_false`, the base case's collapse and the `false` twin `countRange_const_true` never had |
| 2026-09-02 | countrange-bij-cross-bound | `Nat.countRange_bij_of_inverse`, the four-hypothesis specialization with a total inverse and no injectivity hypothesis |
| 2026-09-02 | countrange-bij-cross-bound | five tests including a negative control that shows the injectivity hypothesis UNINHABITED at a non-injective `σ`, plus the not-inverted guard |
| 2026-09-02 | countrange-bij-cross-bound | three facts, all `proved` / `kernel-lean` / footprint `[]`, each checker anchored on the rendered type at 8 preludes |
