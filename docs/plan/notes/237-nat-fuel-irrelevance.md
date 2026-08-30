# Notes: 237-nat-fuel-irrelevance

Detail moved out of [`../status/237-nat-fuel-irrelevance.md`](../status/237-nat-fuel-irrelevance.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

```
Nat.land_aux_agree_of_fuel :
  ∀ fuel1 m n fuel2, Le m fuel1 → Le m fuel2 →
    Eq (landAux fuel1 m n) (landAux fuel2 m n)
```

This is symmetric in which fuel is "the" canonical one, so it NEVER needs
`landAux`'s own canonical instance to unfold. `land_aux_eq_land_of_le` is a
one-line corollary at `fuel2 := m` via `le_refl` — `land m n` and
`landAux m m n` are the SAME term by definition, so the kernel accepts the
double-fuel proof directly against the `land`-headed statement via defeq,
with no extra proof step.

**New reusable machinery, in `ops.rs`:**

- `agree_by_double_fuel_induction` — `agree_by_fuel_induction`'s three-value
  sibling; entirely generic, no `land`-specific content.
- `cases_zero_succ` — a motive-general zero/succ case split via `Nat.rec`,
  discarding the induction hypothesis (the reusable form of what
  `land_zero_right`/`lor_zero_right` each inline by hand for one fixed goal).
  Needed because the step case of the double-fuel induction must case-split
  `m` (not just `fuel1`) to expose whether `landAux`'s inner `m = 0` guard
  reduces.
- `bool_select_nat_same` — `Eq (bool_select_nat b x x) x` for ANY `b`. The
  kernel's defeq checker does not special-case "both recursor branches equal
  regardless of the scrutinee", so this is needed wherever a guard stays
  symbolic but both branches happen to coincide (the `m = 0` base case, where
  BOTH of `landAux`'s absorbing-zero rows are the constant `0`).

**Two case splits, and why each is unavoidable.** Induction is on `fuel1`.
The base case (`fuel1 = 0`) needs no split: `landAux 0 m n` is the constant
`0` row for ANY `m`, `n` (`Nat.land_aux_zero_left_any_fuel`, a NEW "any fuel"
lemma — `landAux`'s fuel-exhaustion row is `0` regardless of `m`/`n`, unlike
`Nat.land_zero_left`, which needs no lemma because `Nat.land` supplies fuel
`= m = 0` automatically). The step (`fuel1 = succ k`) case-splits `m`: at
`m = 0` both sides are `0` (same "any fuel" lemma, no hypotheses needed); at
`m = succ predecessor`, `beq (succ predecessor) zero` reduces to `false` on
BOTH sides (the guard only mentions `m`), so `d.congr` reduces the goal to
the recursive sub-terms `landAux k half half'` vs `landAux f2' half half'`
(`f2' := pred fuel2`), closed by the IH at `a := half`, given `Le half k` and
`Le half f2'` from a per-fuel arithmetic helper
(`half_le_predecessor_of_succ`, a direct copy of the derivation inline in
`powsq.rs`'s `declare_powsq_eq_pow` — that copy is not exposed and
`powsq.rs` is out of scope, so this is the FOURTH site with this exact
`e < 2e ⇒ e/2 < e ⇒ e/2 ≤ f` arithmetic in this prelude, after `log.rs`,
`binary.rs`, `powsq.rs`).

**What the kernel REJECTED, and why.** First attempt failed with
`TypeMismatch` on an `Eq` whose two sides were `succ (pred fuel2)`/`fuel2` in
opposite orders from what I'd assumed. Cause: `Nat.succ_pred_of_pos(c, h)`
proves `Eq c (succ (pred c))` — `c` on the LEFT — not
`Eq (succ (pred c)) c` as I misread from a neighbouring doc comment
(`two_divisor_dichotomy`'s OWN `Eq.rec` usage, re-read carefully, confirms
the direction: it transports FROM `c` TO `succ (pred c)` with no `symm`). I
had inserted an extra `d.symm` to "fix" the direction I assumed was needed,
which flipped it the WRONG way. Removed the spurious `symm`, and swapped
which side of the later `d.congr` call plays `a`/`b` to match — kernel
accepted on the second attempt with no other changes needed.

**Negative control at insufficient fuel.** Same pinned witness the
`rec_agreement` lane used for `bitwise_aux_eq_land_aux`:
`(fuel, m, n) = (1, 7, 7)`. `landAux 1 7 7 = 1` (one fuel step) while
`land 7 7 = 7` (the canonical answer) — checked by evaluation alone (`Le 7 1`
has no proof, so the theorem cannot be applied there; the control exists to
confirm the hypothesis is load-bearing, not to exercise the theorem itself).
`nat_prelude_tests.rs`'s
`land_fuel_irrelevance_holds_above_canonical_fuel_with_an_insufficient_fuel_negative_control`
also applies the theorem symbolically and at `(fuel, m, n) = (7, 1, 7)`
(fuel STRICTLY above canonical), where both sides compute to `1`.

**What is still needed to close any of the 7 facts, and why it is NOT free.**
`land_bit`/`lor_bit`/`ldiff_bit` need relating `land`/`lor`/`ldiff` at a
`Nat.bit`-constructed argument to the recursive step — fuel-irrelevance is
the piece that lets the non-canonical fuel `landAux` reaches there be
discharged, but the `Nat.bit` decode/encode bridge itself is separate work
this lane did not attempt. `land_comm`/`lor_comm`/`land_assoc`/`lor_assoc`
need, IN ADDITION to fuel-irrelevance, a SAME-FUEL commutativity lemma
(`∀ fuel m n, Eq (landAux fuel m n) (landAux fuel n m)`) to relate
`land m n = landAux m m n` and `land n m = landAux n n m` through a common
larger fuel (e.g. `m + n`) — this is genuinely separate proof content
(needs `Nat.mul_comm` for the bit term and a guard-reordering argument,
`lor`'s and `land`'s guards check `n` before `m`), not a corollary of what
landed here.

**Transport to `lorAux`/`ldiffAux` — sized, not landed.**
`agree_by_double_fuel_induction`, `half_le_predecessor_of_succ`, and the
private `n_lt_mul_two` copy are ENTIRELY generic and transport UNCHANGED.
What does NOT transport unchanged is `land_aux_zero_left_any_fuel`:
`lorAux`'s fuel-exhaustion row returns `n`, not `0` (`lor.rs`'s module doc),
so its "any fuel" analogue is `Eq (lorAux fuel 0 n) n`, proved the same way
(a `bool_select_nat_same` call in the `succ` branch) but closing to a
different value. The `m = succ predecessor` step's proof body is otherwise a
direct transcription — same case split, same IH application, same congr —
with `lor`'s own `on_n_zero`/`on_m_zero`/`combine` closures dropped in.
`ldiffAux` shares `land`'s absorbing-zero base case exactly (`ldiff.rs`'s
module doc), so its `any_fuel` lemma is a byte-for-byte copy of `land`'s with
the name and `p.ldiff_aux` swapped in. Estimate: each of `lorAux`/`ldiffAux`
costs one new "any fuel" lemma (~20 lines) plus one new `declare_*_aux_agree_of_fuel`
function that is `declare_land_aux_agree_of_fuel` with the absorbing-zero
constants and combine formula swapped (~150 lines, no new proof technique).

**Counts.** `nat_prelude` before: 121 passed. After: 122 passed (added one
instantiation test with the mandated negative control), plus 3 new
declarations (all theorems, `land_aux_zero_left_any_fuel`,
`land_aux_agree_of_fuel`, `land_aux_eq_land_of_le`) — `the_build_is_deterministic`'s
pin moved `85 + 438` → `85 + 441` (counted from the panic message's own
mismatch, not hand-incremented). `nat` trusted surface still
`axiom=0 opaque=0 quotient=0` (`nat_axiom_inventory --require-axiom-free nat`).
New fact `F:nat-land-aux-eq-land-of-le`; `python3 scripts/validate-facts.py`
clean (1922 facts, 0 errors). `cargo fmt --all --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both clean
on the touched files. NOT run: the aggregate `just check` / `./scripts/check.sh`.

Three `testbit` facts remain pinned OPEN by the live
`gen-autogenesis-bitwise-family-projection.py` gate and were not touched.
