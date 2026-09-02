# Lane: det-mul-general-n

<!-- plan-section: lane-status -->

**Status:** landed, target NOT reached. `Rat.det_mul` at symbolic `n` did not
land. What landed is ADR-1440's **obligation 2 — the selection lemma —
closed**, plus the two bounded determinant congruences the remaining
obligation needs. Ten axiom-free declarations, five `Nat` and five `Rat`.
Decision recorded in
[ADR-1541](../../research/09-decisions/adr-1541-both-blockers-on-the-selection-lemma-were-stale.md).

Target from the lane brief: `Rat.det_mul : ∀ n A B, det (matMul A B n) n =
det A n * det B n`, axiom-free at symbolic `n`, over
[ADR-1120](../../research/09-decisions/adr-1120-the-general-n-determinant-is-a-function-plus-a-bound.md)'s
`Rat.det`. Route (a) — multilinearity plus alternating, expanding over a sum
indexed by a function space. Route (b), Leibniz via permutations, was not
attempted and should not be: this kernel has no `Finset`/`List`.

## What landed

`crates/axeyum-lean-kernel/src/nat_prelude/transposition.rs` (four new
theorems) and `nat_prelude/injective_decide.rs` (new module):

| declaration | what it is |
| --- | --- |
| `Nat.transposition_at_i` | `∀ i j, transposition i j i = j` — unconditional |
| `Nat.transposition_at_j` | `∀ i j, Lt i j → transposition i j j = i` |
| `Nat.transposition_gt_j` | `∀ i j k, Lt i j → Lt j k → transposition i j k = k` |
| `Nat.transposition_eq_of_ne` | a transposition fixes every point that is neither of the two it exchanges |
| `Nat.injective_on_or_duplicate` | `∀ g n, Or (InjectiveOn g n) (∃ a b, Lt a n ∧ Lt b n ∧ Lt a b ∧ g a = g b)`, constructively |

`crates/axeyum-lean-kernel/src/rat_prelude/matrix_det_mul.rs` (new module):

| declaration | what it is |
| --- | --- |
| `Rat.det_congr_lt` | the ROW-bounded determinant congruence |
| `Rat.matSkip_lt_succ` | `Lt c m → Lt (matSkip p c) (succ m)` |
| `Rat.det_congr_entry_lt` | the congruence bounded on BOTH indices |
| `Rat.det_row_selection_injective` | the selection lemma's injective half — the cursor induction ADR-1470 designed and did not build |
| `Rat.det_row_selection` | **obligation 2, closed**: `∀ m B g, MapsInto g (succ m) → det (B∘g) (succ m) = det (matId∘g) (succ m) * det B (succ m)` |

Facts: `F:rat-det-row-selection`, `F:rat-det-row-selection-injective`,
`F:nat-injective-on-or-duplicate`. Every `formal.statement` is
`Kernel::render_lean` of the admitted type, read from
`kernel_declaration_projection`'s `canonical_type` column (`Rat`) and
`nat_theorem_inventory` (`Nat`).

## Both blockers ADR-1470 named were stale

That ADR sized the injective half as a full lane and named two prerequisites.
Neither survived contact. Details in ADR-1541; in one line each:

- **The `NatDev`/`IntDev` wall.** `Nat.transposition`'s pointwise facts are
  Rust helpers taking `&mut NatDev<'_>`, unreachable from `rat_prelude`. A
  `NameId` has no such restriction — declaring four of them as THEOREMS
  removes the wall for every prelude permanently, and only one of the four is
  new work.
- **The "missing" decision procedure.** `Nat.lnp_bounded_search`
  (`least_number.rs`) IS the bounded search for a pointwise-decided predicate.
  ADR-1470 grepped `pigeonhole` / `exists_dup` / `not_injective`; the tool is
  filed under the least-number principle. Two nested instances of it give the
  whole disjunction.

The retrieval lesson is a new one and is recorded in ADR-1541: the step WAS
searched for, under the vocabulary of the mathematical situation, while the
tool is named for the TECHNIQUE. Ask what general principle your specific
search is an instance of.

## The two bounded congruences are different lemmas

`det_congr_lt` is bounded on the ROW only and is what a REINDEXING map needs —
the cursor induction's base case controls `g` on `[0,n)` and nowhere else.
`det_congr_entry_lt` is bounded on BOTH and is what an IDENTITY LAW needs —
`Rat.matMul_id_right` is bounded in the COLUMN and holds at every row, so the
row-bounded form cannot consume it. Obligation 1's final step (turning the
expansion back into `det A n`) needs the entry-bounded one specifically.

## Verification run in this lane

Every command foreground, through `scripts/cargo-serialized.sh`.

- `cargo test --release -p axeyum-lean-kernel --lib -- rat_prelude:: --test-threads=4`
  — **156 passed, 0 failed**, 140.71 s.
- `cargo test --release -p axeyum-lean-kernel --lib -- nat_prelude:: --test-threads=4`
  — **325 passed, 0 failed**, 11.97 s.
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — clean.
- `rustfmt --edition 2024` on every touched file.
- `python3 scripts/validate-facts.py` — **2579 facts checked, 0 errors**.
  `depends_on` completed by `check-fact-depends-derived.py --fix` (26 edges
  read out of the proof terms).
- `kernel_declaration_projection` — every one of the ten new declarations is a
  `theorem` with footprint `0`, read from the environment.
- Rat prelude build cost, from the test harness's own timing on the same host:
  **3.12 s** for two tests before this lane's `rat` work, **3.85 s** after all
  five `Rat` declarations. No regression in character; every magnitude these
  declarations form is an index, not a numeral.

## Nothing did not run

No check in this lane was deferred, backgrounded or left unfinished.

## What is still open, and what it costs

`Rat.det_mul` needs **only** ADR-1440's obligation 1 now: expand
`det (A·B) n` in the rows of `A·B`, each of which is a `Rat.sumRange` of rows
of `B` with coefficients `A r k`, by `Rat.det_row_multilinear` once per row.
Measured, not estimated:

- `Rat.sumMaps` does not exist. `Int.sumMaps` is the template at **1,003
  lines** plus a **354-line** evaluation-test module.
- `Rat.prodRange` does not exist either (`grep prodRange rat_prelude.rs`
  returns nothing; only `Int.prodRange` exists). The coefficient of each index
  map is a PRODUCT over rows, so it is needed too.
- The expansion itself is a cursor induction over rows whose intermediate
  matrix is "the first `k` rows replaced by rows of `B` chosen by `g`", and
  `Int.sumMaps`'s successor equation conses at the FRONT, so the peeling order
  is forced.

That is a full lane on its own, and it is the whole remainder — every other
piece of route (a) now exists.

**The dominance document's §2.2 row cannot be re-scored.** Its "not comparable
(2×2 vs general n)" entry is about the product law, and the product law still
does not exist at general `n`. Do not read obligation 2 as the theorem.

<!-- plan-section: landed-changes -->

| 2026-09-02 | `nat_prelude/transposition.rs` | four pointwise transposition facts as kernel THEOREMS. ADR-1470 recorded the `NatDev`/`IntDev` Rust wall as forcing a second, private two-point swap; a `NameId` has no such restriction, so the facts every other prelude needs are declared instead. Only `transposition_eq_of_ne` is new work — the five-region nested-`trichotomy` split, with the two equality regions discharged by `Not` hypotheses instead of transported. ADR-1541. |
| 2026-09-02 | `nat_prelude/injective_decide.rs` | `Nat.injective_on_or_duplicate` — a self-map of `[0,n)` is either injective there or has an explicit `a < b < n` with `g a = g b`, CONSTRUCTIVELY. Two nested instances of `Nat.lnp_bounded_search`, which ADR-1470 recorded as absent because it grepped for `pigeonhole`/`exists_dup`/`not_injective` and the tool is filed under the least-number principle. Searching strictly below each index is what makes the pair distinct with no negated equality anywhere. ADR-1541. |
| 2026-09-02 | `rat_prelude/matrix_det_mul.rs` | `Rat.det_row_selection` — **ADR-1440's obligation 2, closed**: the selection lemma with `MapsInto` and no injectivity hypothesis, at symbolic `n`. Its injective half is ADR-1470's cursor induction, with three things that ADR did not predict: the dimension and the matrix stay OUTSIDE the induction and the map goes inside it; the base case needs a ROW-bounded congruence (`Rat.det_congr_lt`, also new) because `g` is the identity only on `[0,n)`; and the two-point swap is `Nat.transposition` itself. Also `Rat.det_congr_entry_lt` + `Rat.matSkip_lt_succ`, the BOTH-bounded congruence obligation 1's final step needs, which the row-bounded one cannot supply because `Rat.matMul_id_right` is bounded in the column. `rat_prelude::` 156 passed / 0 failed; `nat_prelude::` 325 passed / 0 failed. `Rat.det_mul` did NOT land — obligation 1 (a `Rat` analogue of `Int.sumMaps`, 1,003 lines, plus a `Rat.prodRange`) is the whole remainder. ADR-1541. |
