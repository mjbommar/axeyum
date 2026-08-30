# Lane: int-order-coercion — four `Int` order-coercion mirrors, plus one `Nat` straggler

<!-- plan-section: lane-status -->

**Closed all five dispatched facts** (`DONE`, int-order-coercion, 2026-08-30).

## Step 0 finding: none already existed

`python3 scripts/brief-step0.py` (after a `--refresh --build` — the shared
snapshot was 41.9h stale against the current kernel tree) reported all five
targets `ABSENT` at >=0.75. `Int.le.elim`/`Int.lt.elim` scored high false
positives against `Nat.le_intro` (constant-multiset collision, no argument
order) — read, and confirmed genuinely absent by shape as well
(`shape_search --concl P --hyp Int.le --hyp Eq` came back `UNANSWERABLE`
because `P` is not itself a declared name; the CPS shape has no name to
search for and none was found by grep across `order.rs`).

## What was already there: `le_dest`/`lt_dest`

`Int.le_dest : le a b → ∃ i, b = a + ofNat i` and
`Int.lt_dest : lt a b → ∃ i, b = a + ofNat (i+1)` already existed
(`int_prelude/order.rs::declare_difference_lemmas`, both tracked as their own
proved facts, `F:int-le-dest` / `F:int-lt-dest`). Mathlib's `Int.le.elim` /
`Int.lt.elim` are the CPS elimination form of exactly this existential —
**the brief's "does not exist" call for `le_elim`/`lt_elim` was right about
the CPS shape and wrong to imply nothing related existed**: the
`Exists`-flavoured cousin was sitting right there and the whole task reduced
to `Exists.elim` plus one `isymm` to flip the equation's direction (Mathlib:
`a + n = b`; `le_dest`/`lt_dest`: `b = a + n`).

## `crates/axeyum-lean-kernel/src/int_prelude/order_coercion.rs` (new)

- `Int.le_of_ofNat_le_ofNat` / `Int.lt_of_ofNat_lt_ofNat` — **purely
  definitional, no lemma needed**. `Int.le`/`Int.lt` are `define_binary_int`
  (`defs.rs`), whose `ofNat`/`ofNat` branch is literally `NatOps::le`/
  `NatOps::lt` on the two `Nat` fields, so `Int.le (ofNat m) (ofNat n)` is
  definitionally `Nat.le m n`. The proof is the hypothesis itself; the
  kernel's own defeq check bridges the two sides.
- `Int.le.elim` / `Int.lt.elim` — built via `ops::exists_elim` over
  `le_dest`/`lt_dest`'s witness. The predicate lambda is re-derived locally
  (matching `order.rs`'s private `shift_predicate` exactly) rather than
  widening that module's visibility for one caller — the same choice
  `euclid.rs::declare_decomposition` already makes for the same reason.
  `Int.le.elim`/`Int.lt.elim` are declared as children of `le`/`lt`
  themselves (`kernel.name_str(le_name, "elim")`), the same namespacing
  `Nat.le.step` uses under an unrelated head — required computing `le`/`lt`'s
  `NameId`s as locals in `intern_names` before the struct literal, since two
  fields now need to be children of them.

Detail moved to [`../notes/312-int-order-coercion.md`](../notes/312-int-order-coercion.md).

