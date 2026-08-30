# Lane: nat-rec-agreement — prove two `Nat.rec`-defined functions agree

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-rec-agreement, 2026-08-29).** The boundary two
lanes stopped at is crossed. Six declarations landed, kernel-admitted on the
FIRST attempt, `nat` still `axiom=0 opaque=0 quotient=0`.

Machinery, in `nat_prelude/ops.rs` beside the other eliminators:

- `cases_mod_two` — the `Nat.mod _ 2 ∈ {0,1}` split `bitwise.rs` named as
  absent, as an eliminator over a motive that VARIES with the remainder. It is
  `cases_lt_bound` at `bound = 2` fed `mod_lt`'s witness. **It genuinely did
  not exist**: `powsq.rs`'s *private* `mod_two_eq_one_of_ne_zero` gives only
  the `= 1` half and needs `r ≠ 0` already in hand, and `Nat.even_or_odd` is
  `div`-shaped and never mentions `Nat.mod`.
- `agree_by_fuel_induction` — induction on a shared fuel counter with **both**
  value arguments generalized in the motive. The brief predicted this
  generalization would be the entire difficulty. It was.

Declarations, in a new `nat_prelude/rec_agreement.rs` (the theorems mention
`Nat.bitwise` *and* a sibling, so neither module owns them):

| name | statement |
| --- | --- |
| `Nat.lt_two_cases` | `∀ r, Lt r 2 → Or (Eq r 0) (Eq r 1)` |
| `Nat.mod_two_eq_zero_or_one` | `∀ n, Or (Eq (mod n 2) 0) (Eq (mod n 2) 1)` |
| `Nat.bitwise_aux_eq_land_aux` | `∀ fuel m n, Eq (bitwiseAux and_fn fuel m n) (landAux fuel m n)` |
| `Nat.bitwise_aux_eq_lor_aux` | `∀ fuel m n, Eq (bitwiseAux or_fn fuel m n) (lorAux fuel m n)` |
| `Nat.bitwise_and_eq_land` | `∀ m n, Eq (bitwise and_fn m n) (land m n)` |
| `Nat.bitwise_or_eq_lor` | `∀ m n, Eq (bitwise or_fn m n) (lor m n)` |

Facts: `F:nat-mod-two-eq-zero-or-one`, `F:nat-bitwise-and-eq-land`,
`F:nat-bitwise-or-eq-lor`. The two `_three_five` predecessors are kept (they
are *reduction*-based, independent of the induction) with their now-stale
"was NOT attempted" notes corrected in place rather than deleted, and
`bitwise.rs`'s module doc likewise.

Detail moved to [`../notes/233-nat-rec-agreement.md`](../notes/233-nat-rec-agreement.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-rec-agreement | `mod 2 ∈ {0,1}` split + fuel-generalized agreement induction; `bitwise and_fn = land` and `bitwise or_fn = lor` proved universally |
