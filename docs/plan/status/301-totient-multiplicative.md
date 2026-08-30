# Lane: totient-multiplicative — `coprime_div_left` closed, `gcd_comm` landed, the multiplicative-formula plan traced and numerically checked

<!-- plan-section: lane-status -->

**DONE for this dispatch (`totient-multiplicative`, 2026-08-29).**

## Part 1 — the quick one, closed

**`F:ml430-nat-coprime-coprime-div-left-6f7082bd`** is `proved`,
`proof_route: kernel-lean`, `axiom_footprint: []`. `Nat.coprime_div_left`
(`nat_prelude/coprime_lemmas.rs::declare_coprime_div_left`) is the exact
mirror image of the already-closed `Nat.coprime_div_right`: the divided
argument moves from `n` to `m`, and the succ-branch shrink step uses
`coprime_of_dvd_left` (shrinking the LEFT `gcd` argument) instead of
`coprime_of_dvd_right`. (Lean core actually proves `coprime_div_right` FROM
`coprime_div_left` via `.symm` — this kernel has no `gcd_comm` at the time
this mirror was built, so it went the other way, building `coprime_div_left`
directly instead of transporting through `.symm`; see Part 2 below, which
lands `gcd_comm` anyway for unrelated reasons.) Pinned by a
concrete-instantiation test exercising both branches
(`coprime_div_left_applies_at_both_branches_of_its_case_split`), checking the
residue lands in the FIRST argument (`Coprime (div 10 2) 3`, not `Coprime 3
(div 10 2)`).

`depends_on` completed via `scripts/check-fact-depends-derived.py`
(`missing_edges=0`). Both evidence `checker_command`s verified to pass on the
real name (count 1) and fail on a fabricated one (count 0, exit 1).

## Part 2 — `Nat.gcd_comm`, landed as unplanned but necessary infrastructure

Detail moved to [`../notes/301-totient-multiplicative.md`](../notes/301-totient-multiplicative.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | totient-multiplicative | `Nat.coprime_div_left` (1 of the family's remaining mirrors, closed) and `Nat.gcd_comm` (new, zero-induction, unblocks both this family's `totient_even` plan and the multiplicative-formula plan below) landed and verified. The multiplicative formula `totient(mn) = totient(m)*totient(n)` itself: fully traced and numerically checked (bijection, mod-gcd invariance, pointwise coprimality iff, Bézout-multiplication algebra, the row-major double-counting target statement), with the two genuinely novel pieces identified and marked (`coprime_mul_of_coprime`, the coprimality-combine number theory; `count_range_row_major`, the totient-independent double-counting induction) — NOT built in Rust, per this task's own sizing guidance. `nat_prelude/crt.rs` (Nat-native, not the `int_prelude` one) was found to transport directly for the injectivity/pigeonhole half, correcting all three prior triages, which did not find it. |
