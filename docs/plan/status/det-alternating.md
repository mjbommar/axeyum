# Lane: det-alternating

<!-- plan-section: lane-status -->

**In progress — checkpoint commit, no kernel code landed yet.** Target: the
alternating property of `Rat.det` (`det A n = 0` when two distinct rows of
`A` agree), step 2 of ADR-1310's multiplicativity dependency chain.

## Confirmed against the tree (not taken on faith)

- **`Rat.det_row_expansion` (step 1) is landed on `main`**:
  `declare_det_row_expansion` in `crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs:4413`,
  statement `∀ m A i, Nat.ble i m = true → det A (succ m) = sumRange (fun q =>
  altSign (q+i) * (A i q * det (matMinor A i q) m)) (succ m)`. ADR-1310 lists
  this as unattempted; that line is stale.
- `Rat.det_congr`, `Rat.det_transpose`, `Rat.det_col_expansion`,
  `Rat.det_minor_col_comm`, `Rat.det_minor_row_col_comm`,
  `Rat.det_double_comm_hi`/`_lo`, `Rat.matMinor_double_comm_hi`/`_lo` are all
  landed (`shape_search --include-constructed --name-like det/minor`,
  verified 2026-09-01).
- **No alternating-property, row-swap, or "two rows equal" declaration exists
  anywhere in the tree** (`shape_search --name-like alternat/row_eq/two_row`
  all ABSENT with a working positive control).
- `Rat.sumRange_eq_zero_of_lt : ∀ f n, (∀ i, Lt i n → f i = 0) → sumRange f n
  = 0` exists (`rat_prelude/sum.rs`) — exactly the "every summand vanishes"
  collapse step the proof below needs.
- `Rat.mul_zero`, `Rat.mul_comm`, `Rat.matSkip_zero` (`matSkip 0 x = succ
  x`, unconditional) all exist and are usable as-is.
- **`Rat.matSkip`'s "index below the deleted row/column is unshifted"
  branch has no general lemma** — only the `= 0` branch (`mat_skip_zero`) is
  named. The missing general fact, needed once (see plan below):
  `Rat.matSkip_of_ble : ∀ k x, Nat.ble k x = true → matSkip k x = succ x`
  (the OTHER `bool_select_nat` branch of the same definition). Straightforward
  from the definition via a Bool-hypothesis congr (the `congr_bool_to_nat`
  device already used four times elsewhere in `nat_prelude/`, copied locally
  since it is `pub(crate)` nowhere shared).
- `det2_zero_of_ad_eq_bc` (private in `matrix.rs`, gives `det2 a b c d = 0`
  from `a*d = b*c`) is exactly the base-case (`n=2`) tool; needs `pub(super)`
  or a local re-derivation (it is ~15 lines, either is fine).

## The proof plan (cofactor induction, no permutations, no `Nat.Fin`)

Statement: `Rat.det_alternating : ∀ m A i j, Nat.beq i j = false → Nat.ble i
m = true → Nat.ble j m = true → (∀ c, A i c = A j c) → det A (succ m) = 0`.

Induction on `m`.

- **Base `m=0`**: `ble i 0=true` and `ble j 0=true` force `i=j=0` (own small
  induction: `ble (succ _) 0` is `false` by iota, contradiction via
  `false_true_elim`), contradicting `beq i j=false` (`beq 0 0` reduces to
  `true`). Vacuous.
- **Step `m=succ mp`, `IH=motive(mp)`**: case-split `i` (0 or `succ i'`),
  then `j` similarly. Four branches:
  1. `i=succ i'`, `j=succ j'` (both nonzero): expand along row **k=0**.
     `matSkip 0 x = succ x` unconditionally, so the minor's rows `i'`,`j'`
     are the original rows `i`,`j` **by defeq, no rewriting needed** — and
     because `ble(succ a)(succ b)` iota-reduces to `ble a b`, the ORIGINAL
     hypotheses `hne`/`hbi`/`hbj` are already, up to defeq, exactly the
     hypotheses `IH` wants at `i'`,`j'`. This branch should need almost no
     new term-building beyond assembling the `IH` application and the
     row-equality lambda `fun c => roweq (matSkip q c)`.
  2. `i=0`, `j=succ j'`, `j'=succ j''` (i.e. `j >= 2`): expand along **k=1**.
     `ble 1 (succ mp)` reduces to `true` unconditionally (no case split on
     `mp` needed). Row `i=0 < 1`: unshifted, needs `matSkip 1 0 = 0`
     (fully concrete, `Eq.refl`). Row `j`: shifted, needs `matSkip 1 j' =
     succ j' = j`, via the new `matSkip_of_ble` lemma at the concrete `k=1`
     (hypothesis `ble 1 j' = true` again reduces unconditionally since
     `j'=succ j''`).
  3. `i=0`, `j=1` (`j'=0`), **and `mp=0`**: direct 2x2 case, no minors.
     `det_eq_det2` + `det2_zero_of_ad_eq_bc` from `A00=A10`, `A01=A11`
     (roweq at `c=0,1`) and commutativity.
  4. `i=0`, `j=1`, `mp=succ mp'`: expand along **k=2**. `matSkip 2 0=0`,
     `matSkip 2 1=1` both fully concrete (`Eq.refl`); `ble 2 (succ(succ
     mp'))=true` reduces unconditionally.
  5. `i=succ i'`, `j=0`: symmetric to branches 2-4 with `i`,`j` swapped and
     the row-equality hypothesis flipped by `rsymm` pointwise. Plan: factor
     branches 2-4 into a Rust closure parameterized by "which row is the
     literal zero" so this case reuses the same code rather than
     duplicating it.

A shared helper `zero_sum_via_expansion(mat, k, hk, n1, minor_zero_fn)`
covers "expand along row `k`, then collapse the sum because every summand's
cofactor determinant is `0`" — used by branches 1, 2, 4, and (via the
symmetric closure) their branch-5 counterparts. `minor_zero_fn` differs per
branch only in how it derives `det(matMinor A k q) n1 = 0` (via `IH`, with
different index-shift bookkeeping per branch).

No new aggregate, no `Rat.det_congr` needed (the induction hypothesis is
applied directly to the concrete minor, never to a separately-named matrix
related by congruence) — contrary to ADR-1310's expectation that this step
"will need `Rat.det_congr`". That may be worth a documented correction if
the proof lands this way.

## Risk / fallback

This is genuinely the "substantial theorem" ADR-1310 calls it. If the general
induction does not close cleanly, the fallback (already scoped, sanctioned by
the brief): land `Rat.det2`/`Rat.det3` "two equal rows ⇒ 0" as standalone
symbolic theorems (small, since `det2_zero_of_ad_eq_bc` already exists and
`det3`'s six-term expansion is ordinary algebra), plus this document's
induction skeleton and the precise rendered type of whichever obligation
could not be discharged.

## Checks run so far

None yet — no kernel code written. This commit is a checkpoint per the
coordinator's course-correction (branch had zero commits after the research
phase). Next: implement `matSkip_of_ble`, then `det_alternating`, then
`cargo-serialized.sh test -p axeyum-lean-kernel --lib rat_prelude::` with a
confirmed nonzero pass count before reporting anything as done.
