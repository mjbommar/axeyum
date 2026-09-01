# ADR-1470: The selection lemma's literal target is false; the corrected statement needs `MapsInto`, and only its free (non-injective) half is landed

Status: accepted
Date: 2026-09-01
Index-summary: ADR-1440 named the selection lemma
`det (B∘g) n = det (matId∘g) n * det B n` as the last obstruction to
determinant multiplicativity and described it with no hypothesis on `g`.
That statement is FALSE — counterexample `n=1, g 0 = 5, B 5 0 = 7` — because
an injective-but-not-`MapsInto` `g` breaks it. The corrected statement needs
`MapsInto g n`; `InjectiveOn` is not an extra hypothesis, since the
non-injective case is free via `det_alternating` regardless of `MapsInto`.
This lane landed exactly that free half, `Rat.det_row_selection_of_duplicate`
(axiom-free), and designed but did not build the injective half: a cursor
induction over "how many trailing positions are already fixed", using
pigeonhole (`Nat.injective_on_imp_surjective_on`), a fresh 2-point swap
function (composed with `g` via `Nat.injective_on_comp`, NOT
`Nat.transposition` — its pointwise lemmas are tied to a concrete `NatDev`
and unusable from `IntDev`), and `Rat.det_row_swap`. A bounded-search
decidability construction for `InjectiveOn g n \/ (a duplicate)` is also
needed and does not exist in-tree.
Index-status: accepted

## Context

[ADR-1440](adr-1440-multiplicativity-needs-a-selection-lemma-not-a-leibniz-agreement.md)
reframed determinant multiplicativity's remaining gap as two obligations and
named the second, "the selection lemma", as the hard one:

```text
∀ (n : Nat) (B : Nat → Nat → Rat) (g : Nat → Nat),
  det (fun r c => B (g r) c) n
    = det (fun r c => matId (g r) c) n * det B n
```

with `g` completely unrestricted — no `InjectiveOn`, no `MapsInto`. This
lane (`det-selection-lemma`) was briefed to prove exactly that statement.

## The statement is false

Take `n = 1`, `g 0 = 5`, and any `B` with `B 5 0 = 7`. Then:

- `det (fun r c => B (g r) c) 1 = B (g 0) 0 = B 5 0 = 7` (`Rat.det_one`).
- `det (fun r c => matId (g r) c) 1 = matId (g 0) 0 = matId 5 0 = 0`, since
  `matId i j := bool_select_rat (beq i j) one zero` and `beq 5 0 = false`.
- The right side is therefore `0 * det B 1 = 0`.

`7 ≠ 0`. The obstruction is exactly the case ADR-1440's own proof sketch
never covers: `g` is injective on `[0,1)` (vacuously — one element, nothing
to collide with) but does not map into `[0,1)`. ADR-1440's cursor-induction
sketch (`P(k)`) already required `MapsInto σ n` as a hypothesis for the
*injective* half; what it did not say is that this hypothesis is load-bearing
on the theorem's STATEMENT, not only on the proof technique used to reach it.

## The corrected statement

```text
∀ (n : Nat) (B : Nat → Nat → Rat) (g : Nat → Nat),
  MapsInto g n →
  det (fun r c => B (g r) c) n
    = det (fun r c => matId (g r) c) n * det B n
```

`InjectiveOn g n` is deliberately absent from this list. When `g` is NOT
injective on `[0,n)` — some `i ≠ j`, both `< n`, with `g i = g j` — row `i`
and row `j` of `B∘g` coincide (`B (g i) c = B (g j) c` pointwise), and
likewise for `matId∘g`, so both determinants are `0` by `Rat.det_alternating`
regardless of what `g i` (`= g j`) actually is. **This half needs no
`MapsInto` at all** — the duplicate argument goes through even if `g i` is
`5,000,000`. `MapsInto` is needed only to rule out the counterexample shape
above, which requires `g` injective (no duplicate to fall back on) but able
to point somewhere the determinant machinery cannot use to build a
compensating zero row.

## What landed: the free half

`Rat.det_row_selection_of_duplicate`
(`crates/axeyum-lean-kernel/src/rat_prelude/matrix_det_selection.rs`),
stated at dimension `succ m` to match `Rat.det_alternating`'s own convention
(so its Boolean hypotheses pass straight through with no bridging):

```text
∀ m B g i j,
  Nat.beq i j = false → Nat.ble i m = true → Nat.ble j m = true →
  Eq Nat (g i) (g j) →
  det (fun r c => B (g r) c) (succ m)
    = det (fun r c => matId (g r) c) (succ m) * det B (succ m)
```

Rendered by the kernel (`Kernel::render_lean`, confirmed by re-running the
declaration and printing the admitted type, not read from source text):

```text
(x0 : AxNat) -> (x1 : AxNat -> AxNat -> Rat) -> (x2 : AxNat -> AxNat) ->
(x3 : AxNat) -> (x4 : AxNat) ->
(x5 : Eq Bool (AxNat.beq x3 x4) Bool.false) ->
(x6 : Eq Bool (AxNat.ble x3 x0) Bool.true) ->
(x7 : Eq Bool (AxNat.ble x4 x0) Bool.true) ->
(x8 : Eq AxNat (x2 x3) (x2 x4)) ->
  Eq Rat
    (Rat.det (fun x9 x10 => x1 (x2 x9) x10) (AxNat.succ x0))
    (Rat.mul (Rat.det (fun x9 x10 => Rat.matId (x2 x9) x10) (AxNat.succ x0))
             (Rat.det x1 (AxNat.succ x0)))
```

`Kernel::axiom_footprint` on this declaration is empty (measured directly,
not inferred) — axiom-free, consistent with every prelude but `axreal`.

**Proof.** `Rat.det_alternating` applied to `fun r c => B (g r) c` at rows
`i, j`, and separately to `fun r c => matId (g r) c` at the same rows, each
needs the pointwise row-equality `∀c, mat (g i) c = mat (g j) c`; this is
built by bridging the `Nat` hypothesis `g i = g j` into a `Rat` equality via
`nat_eq_to_rat` (`Rat`'s `ℕ → ℚ` congruence bridge) applied to `fun t => mat t
c` — **not** `NatOps::congr`, whose conclusion is hard-wired to `Eq Nat`
(the "dev-helper hardcodes a carrier" trap this repository's own gotchas
warn about: the first attempt produced `TypeMismatch { expected: AxNat, got:
Rat }`, from exactly this substitution). Both determinants collapse to `0`;
the goal becomes `0 = 0 * det B (succ m)`, closed via `mul_comm` then
`mul_zero` (this prelude has no `zero_mul`).

Registered in `rat_prelude_tests.rs`'s `named()` (the environment-derived
coverage assertion, `every_rat_declaration_is_checked_and_axiom_free`) and in
`the_determinant_toolkit_is_axiom_free`'s targeted list. Full `rat_prelude::`
sweep: 156 passed, 0 failed.

## What did not land: the injective half

The route, fully designed, not built. State it as a cursor induction for
FIXED `n := succ n'`, `B` (never recreated across the induction — mirroring
`Int.prodRange_permute`'s own `f` staying outside its motive):

```text
P(k) : ∀ g,
  InjectiveOn g n → MapsInto g n →
  (∀ i, Le k i → Lt i n → Eq Nat (g i) i) →
  det (B∘g) n = det (matId∘g) n * det B n
```

- `P(0)`: the hypothesis forces `g` to be the identity on all of `[0,n)`
  (`Le 0 i` holds for every `i`); `Rat.det_congr` identifies `B∘g` with `B`
  and `matId∘g` with `matId`, then `Rat.det_matId` plus `mul_comm`/`mul_one`
  close it.
- `P(k) → P(succ k)`: split `Lt k n` vs `Le n k` (`Nat.lt_or_ge`). In the
  `Le n k` branch, `P(k)`'s own fixed-point hypothesis is derivable by
  contradiction from `P(succ k)`'s (both ranges are empty when `k ≥ n`), so
  the IH applies to the SAME `g` with no swap. In the `Lt k n` branch:
  pigeonhole (`Nat.injective_on_imp_surjective_on` applied to `g` at target
  `k`) gives `j < n` with `g j = k`. `j > k` is impossible (`g`'s own
  fixed-point hypothesis would force `g j = j`, contradicting `g j = k` under
  `j ≠ k`). `j = k` means `g` already fixes `k`; apply the IH to `g`
  directly. `j < k` is the real case: let `swap(x) := if x=j then k else if
  x=k then j else x` (a fresh, private, `Nat.beq`-based 2-point swap — see
  below for why not `Nat.transposition`), and `σ' := comp g swap` (i.e.
  `g ∘ swap`). Then `σ'(j) = g(k)`, `σ'(k) = g(j) = k`, and `σ'` agrees with
  `g` elsewhere. `InjectiveOn σ' n` / `MapsInto σ' n` follow from
  `Nat.injective_on_comp` plus `swap`'s own injectivity (from an involution
  argument: `swap(swap(x)) = x` by a 3-way case split, then the standard
  "apply `swap` to both sides" trick) and `MapsInto` (direct case split,
  bounded by `Lt j n`/`Lt k n`). `σ'` satisfies `P(k)`'s fixed-point
  hypothesis (`σ'(k) = k`, and `σ'(i) = g(i) = i` for `i > k` via the swap's
  "elsewhere" case plus `g`'s own hypothesis), so the IH gives
  `det(B∘σ') n = det(matId∘σ') n * det B n`. Since `(B∘σ')` is exactly
  `(B∘g)` with rows `j, k` exchanged (and likewise for `matId`),
  `Rat.det_row_swap` relates `det(B∘σ') n = neg(det(B∘g) n)` and
  `det(matId∘σ') n = neg(det(matId∘g) n)`; substituting and cancelling the
  double negation (`neg_mul` + `neg_neg`) recovers exactly `P(succ k)`'s
  goal for `g`.
- The published theorem is `P(n)` (fixed-point hypothesis vacuous for
  `k = n`), reached by inducting `k` from `0` to `n` — itself needing the
  `k ≥ n` / `Lt k n` split at every step, since `Nat.rec`'s successor case
  must handle arbitrary `k`, not just `k < n`.

**Why not `Nat.transposition`.** `nat_prelude/transposition.rs` already has
exactly this object — `Nat.transposition`, `transposition_involutive`,
`transposition_injective`, `transposition_maps_into` are all `pub` `NameId`
fields, usable from any prelude. Its five pointwise correctness facts
(`transposition_eq_at_i`, `_eq_lt_i`, `_eq_between`, `_eq_at_j`, `_eq_gt_j`)
are `pub(crate)` — visible crate-wide by ACCESS LEVEL — but their Rust
signatures are hard-wired to `&mut NatDev<'_>`, a different concrete type
than the `&mut IntDev<'_>` this file (and every `rat_prelude` file) uses.
`IntDev` and `NatDev` both implement the shared `NatOps` trait, but Rust
does not let you call a function written against one concrete struct with a
value of the other. The same blocks reuse of `int_prelude/prod.rs`'s
`point_swap` family, which is `pub(super)` (visible only inside
`int_prelude`) on top of the type mismatch. A future lane has two options:
generalize one of those pointwise-lemma sets to `impl NatOps` (a real,
reusable fix — this is at least the third file this repository's own
gotchas record hitting this exact wall), or build the smaller, self-contained
`Nat.beq`-based 2-point swap sketched above (no ordering machinery needed,
unlike `Nat.transposition`'s 4-level `Nat.ble` case tree, since a 2-point
swap only ever needs "is `x` this point or that point", not "which side of
two ordered points is `x` on").

**The missing decidability piece.** The induction above needs
`InjectiveOn g n` as a hypothesis to invoke pigeonhole; the PUBLISHED
theorem should not require it (as established above, the non-injective case
is free). Closing that gap needs:

```text
∀ n g, Or (InjectiveOn g n) (∃ i j, Lt i n ∧ Lt j n ∧ Not (Eq i j) ∧ Eq (g i) (g j))
```

Checked: no `not_injective`/`exists_dup`/decidable-pigeonhole lemma exists
anywhere in `nat_prelude` (grepped `pigeonhole`, `exists_dup`,
`not_injective` across every file in that directory; only doc-comment
mentions of "pigeonhole" as a concept, no such decision procedure). It is
buildable by induction on `n`, using a bounded-search sub-decision ("does
`g`'s value at the new top index collide with any earlier index", itself an
induction on the search bound, deciding `Nat.beq` at each step via
`Bool.rec`) — genuinely new, general-purpose infrastructure, independent of
everything else in this ADR.

## Consequences

- The literal target in every prior brief and in ADR-1440's own "obligation
  2" statement is corrected here to require `MapsInto`. Any future work
  quoting "the selection lemma" should quote the corrected form, not
  ADR-1440's.
- `Rat.det_row_selection_of_duplicate` is public surface and general: it
  does not mention matrix multiplication or `matId` specifically beyond
  being one of its two arguments, so it is available to any argument that
  needs "reindexing by a non-injective map collapses a determinant".
- The next lane on this target should build, in order: (1) the bounded-search
  decidability construction (self-contained, no dependency on the rest), (2)
  the 2-point swap function with its involutive/injective/`MapsInto` facts
  (self-contained), (3) the cursor induction assembling pigeonhole +
  `det_row_swap` + the swap function. None of the three needs `Rat.prodRange`
  or `Rat.sumMaps` (still absent, still unverified whether porting them is
  structural — ADR-1440's finding stands) — this route bypasses obligation 1
  entirely and proves obligation 2 directly.
- Sizing: this lane spent its full budget on route design plus the free half.
  The injective half is comparable in scope to `Int.prodRange_permute` itself
  (the skeleton this ADR's route mirrors), which was a substantial standalone
  effort — budget a full lane for it, not a continuation.

## What this ADR does NOT claim

- The injective case is not proved.
- Full multiplicativity `det (A*B) n = det A n * det B n` is not assembled;
  that still needs obligation 1 (the Cauchy–Binet expansion,
  `Rat.det_row_multilinear` applied once per row) composed with a COMPLETE
  (both halves) selection lemma.
- The bounded-search decidability sketch is a design, not landed code.
