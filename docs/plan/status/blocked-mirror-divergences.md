# Lane: blocked-mirror-divergences — the 4 structurally-blocked `ml430` causes

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, blocked-mirror-divergences, 2026-08-30).**

Resolved as much of each of the four `check-dispatchable-frontier.py`
"structurally blocked by a divergence" causes as is honest, landing two new
kernel theorems and correcting one stale sizing (ADR-0840). No mirror was
flipped (none of the four should be).

## `Nat.testBit` (codomain) — 5 facts, 2 already done, 2 landed this lane, 1 stays deeply blocked

- `F:ml430-nat-lt-of-testbit-72f64ab8`, `F:ml430-nat-zero-of-testbit-eq-false-e244c9a1`:
  **already resolved by prior lanes** (`F:nat-lt-of-testbit`,
  `F:nat-zero-of-testbit-eq-zero`, both `proved`, axiom-free). Verified in
  tree, nothing further needed.
- `F:ml430-nat-testbit-land-dfef7ca4`, `F:ml430-nat-testbit-lor-7644e067`:
  **landed this lane** as `F:nat-testbit-land` and `F:nat-testbit-lor`
  (`crates/axeyum-lean-kernel/src/nat_prelude/testbit_bitwise.rs`), both
  admitted axiom-free, each with a concrete discriminating instance (3
  bits) plus a symbolic check. Transported `testbit_bitwise.rs`'s existing
  `Nat.testBit_xor` technique (induction on the bit index, reduced to a
  low-bit lemma and a div-by-2 lemma per level) to `landAux`/`lorAux`
  directly. One real bug found via a temporary `render_lean` debug probe:
  `land_div_two`'s `at_n_zero` branch assumed `land_zero_right(m) : Eq
  (land m 0) m` (copying `lor`'s shape); `land`'s absorbing zero means it is
  actually `Eq (land m 0) 0` on BOTH sides. Fixed; `lor`'s construction
  (byte-for-byte from `xor`'s shape, since `lor`'s boundary behavior is
  identical to `xor`'s) was admitted on the first attempt.
- `F:ml430-nat-testbit-eq-inth-ffa07392`: **stays open, genuinely deeper
  blocked than the other four.** Needs `n.bits : List Bool` +
  `List.getI`; this kernel has **no `List` type at all**, on top of the
  Bool/Nat codomain mismatch. No local analogue attempted — there is no
  honest Nat-valued restatement of "the i-th element of a list this kernel
  cannot construct."

Detail moved to [`../notes/blocked-mirror-divergences.md`](../notes/blocked-mirror-divergences.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | blocked-mirror-divergences | Verified multichoose/minFac divergences against pinned Mathlib source (already resolved by prior lanes, confirmed not re-derived); landed `Nat.testBit_land`/`Nat.testBit_lor` (`F:nat-testbit-land`, `F:nat-testbit-lor`, both axiom-free, transported from the existing `Nat.testBit_xor` technique); wrote ADR-0840 correcting `Nat.fastFib`'s sizing (Mathlib's `fastFibAux` uses a non-dependent `binaryRec` motive, so the existing fuel-based `binaryRec` suffices, but `Nat.fib`'s own divergent construction independently keeps the mirror unflippable regardless) |
