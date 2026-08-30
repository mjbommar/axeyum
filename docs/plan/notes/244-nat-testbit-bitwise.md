# Notes: 244-nat-testbit-bitwise

Detail moved out of [`../status/244-nat-testbit-bitwise.md`](../status/244-nat-testbit-bitwise.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Decision:** do not flip any of the four `ml430` facts. Instead, build the
genuine Nat-valued analogues as NEW local facts (the same pattern
`F:nat-land-comm` used alongside `F:ml430-nat-land-comm-...` in
`docs/plan/status/239-nat-fuel-transport.md`), which adds real, checked
kernel content without contradicting the pinned mismatched-type statements
or the live gate.

**What landed: `F:nat-zero-of-testbit-eq-zero`.** The cheapest of the four,
as the brief predicted, and it did NOT need the fuel/index bridge at all —
`Nat.sum_testBit_eq` already existed (`n = sumRange (fun i => testBit n i *
2^i) (size n)`). Two new pieces, both in `nat_prelude/binary.rs`:

- `Nat.testBit_of_zero : ∀ i, testBit 0 i = 0` — induction on `i`; the step
  uses `zero_div` (`div 0 2 = 0`) to keep the recursive call at the SAME `0`
  the induction hypothesis covers.
- `Nat.sumRange_const_zero : ∀ k, sumRange (fun _ => zero) k = zero` — a
  general arithmetic fact (not testBit-specific): the step peels one term via
  `sumRange_succ`, the IH rewrites the first summand to `zero`, and
  `add zero (g j)` is `refl` (`g j` beta-reduces to the literal `zero`, and
  `Nat.add` recurses on its SECOND argument, so `add_zero`'s pattern fires
  directly with no rewrite needed).

`Nat.zero_of_testBit_eq_zero` chains them with `sum_range_congr` (every
summand collapses to `0` via `zero_mul`, given the hypothesis) and
`sum_test_bit_eq`. Kernel-admitted on the FIRST attempt for all three
declarations — the only rework needed was in the TEST file, not the proof:
`k.infer` on a raw un-abstracted `fvar` fails `UnboundFVar` (the kernel's
local context has no entry for an fvar that was never run through
`lam_fv`/`pi_fv`), so the "symbolic" instantiation test had to re-derive the
statement as its own tiny `f.theorem(...)` (mirroring
`land_fuel_irrelevance_holds_...`'s pattern in
`nat_prelude_tests.rs:10830`) rather than applying the theorem directly at a
bare fresh fvar.

**The mandatory concrete-instantiation test for `zero_of_testBit_eq_zero` is
necessarily degenerate, and that is a real property of the statement, not a
gap in the test.** Its hypothesis (`∀ i, testBit n i = 0`) is FALSE for every
`n != 0` in this consistent kernel, so `n := 0` (supplied by
`Nat.testBit_of_zero`) is the ONLY value this fact's own evidence can
concretely instantiate. The negative control instead varies the CONCLUSION
side (checking the residue is not def-eq to `Eq 0 1`), which is the
discriminating check actually available here.

**Counts.** `nat_prelude`: 126 → 128 tests (2 new instantiation tests,
`test_bit_of_zero_holds_symbolically_and_at_concrete_indices`,
`zero_of_test_bit_eq_zero_applies_at_the_only_provable_instance`), all
green. 3 new declarations, all theorems (`test_bit_of_zero`,
`sum_range_const_zero`, `zero_of_test_bit_eq_zero`) —
`the_build_is_deterministic`'s pin moved `88 + 452` → `88 + 455` (counted
from `theorem_names`'s own list length, not hand-incremented).
`every_nat_declaration_is_checked_and_axiom_free` and
`nat_axiom_inventory --require-axiom-free nat` both still report `nat`
axiom-free. `python3 scripts/validate-facts.py`: 1926 facts, 0 errors.
`cargo fmt --all --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both clean
on the touched files. NOT run: the aggregate `just check` / `./scripts/check.sh`.

**What is still needed for `testBit_land`/`_lor`/`_ldiff` — sized in full,
not attempted, and this IS the hard part the brief warned about.** All three
need a genuine bridge between two structurally different recursions:
`testBit`/`testBitAux` recurses on the bit INDEX `i`; `land`/`lor`/`ldiff`
(via `landAux`/`lorAux`/`ldiffAux`) recurse on a FUEL bound. The worked-out
route, checked against the actual machinery in
`nat_prelude/rec_agreement.rs` (fuel-irrelevance, landed by
`nat-fuel-irrelevance`/`nat-fuel-transport`, `docs/plan/status/237`/`239`)
rather than assumed:

1. **A `land_succ_of_pos`-shaped equation is the missing middle piece.**
   Statement: for `m = succ pm`, `n = succ pn`,
   `land m n = add (mul 2 (land (div m 2) (div n 2))) (mul (mod m 2) (mod n
   2))`. This is NOT already available as a theorem about `land` itself
   (only about `landAux` at a fixed fuel) and has to be derived:
   - `land m n := landAux m m n` (defn) unfolds by ONE fuel step via `iota`
     (`m` is a literal `succ pm`, so `Nat.rec`'s succ branch fires,
     regardless of `pm` being symbolic) to
     `guarded(m, n, 0, 0, landAux pm (div m 2) (div n 2), bit_and)` — reuse
     `rec_agreement.rs`'s private `guarded` helper (`rec_agreement.rs:99`)
     verbatim; this step needs NO lemma, only that the theorem's stated LHS
     and this unfolded form are DEFEQ (the same technique
     `declare_land_aux_agree_of_fuel`'s step case already relies on, per its
     own `start`/`final_target` variables never being explicitly related by
     a `refl` call — the kernel's own defeq check bridges it when the whole
     proof term is submitted).
   - The recursive occurrence `landAux pm (div m 2) (div n 2)` is at
     NON-canonical fuel `pm` (canonical for `land (div m 2) (div n 2)` would
     be `div m 2` itself). Bridge it with the EXISTING
     `Nat.land_aux_agree_of_fuel : ∀ fuel1 a b fuel2, Le a fuel1 → Le a fuel2
     → landAux fuel1 a b = landAux fuel2 a b`, instantiated at
     `a := div m 2`, `fuel1 := pm`, `fuel2 := div m 2` (canonical, so
     `landAux fuel2 a b` is DEFEQ to `land (div m 2) (div n 2)` by
     definition). The needed `Le (div m 2) pm` comes DIRECTLY from the
     EXISTING `half_le_predecessor_of_succ(d, &p, pm, pm, le_refl(m))` in
     `rec_agreement.rs:544` (its signature is
     `(predecessor, k, bound: Le (succ predecessor) (succ k)) -> Le (div
     (succ predecessor) 2) k`; instantiate `predecessor := pm`, `k := pm`,
     `bound := le_refl(m)` since `m = succ pm`). **No new arithmetic lemma is
     needed for this step** — it is a direct application of two already-built
     pieces.
2. **The `testBit_land` induction itself**, on `i`, generalizing `m, n`,
   with motive `fun i => ∀ m n, testBit (land m n) i = mul (testBit m i)
   (testBit n i)`:
   - Base (`i = 0`): 3-way case split on `m`/`n` via `cases_zero_succ`
     (`ops.rs:1551`) — `m = 0` (`land_zero_left`, refl), `n = 0`
     (`land_zero_right`, an existing theorem), and `m, n` both `succ` (the
     `land_succ_of_pos` equation above, then `mod (2a+r) 2 = r` for `r < 2` —
     see point 3).
   - Step (`i = succ j`): same 3-way split; the "both succ" case needs
     `div (2a+r) 2 = a` for `r < 2` (point 3) to reduce
     `div (land m n) 2` to `land (div m 2) (div n 2)`, then the INDUCTION
     HYPOTHESIS applied at `(div m 2, div n 2)`, then `testBit_succ`
     (already a theorem, `testBit n (succ i) = testBit (div n 2) i`) run
     BACKWARDS to fold `testBit (div m 2) j` back into `testBit m (succ j)`.
     The `m = 0` / `n = 0` cases need a small helper (`testBit 0 i = 0`,
     **already landed by this lane** as `Nat.testBit_of_zero` — reuse it
     directly, do not re-derive).
3. **A general "div/mod of `2a+r` for `r < 2`" lemma does not exist yet and
   is needed for BOTH the base and step cases above.** Build it the same way
   `binary.rs`'s `declare_mod_two_mul_split` builds its own div/mod identity:
   construct `divMod 2 (add (mul 2 a) r) a r` BY HAND (the equation side is
   `refl`; the bound side is the `r < 2` hypothesis, itself obtained by
   4-way `cases_mod_two` on `mod m 2` and `mod n 2` — `bit_and = mul (mod m
   2) (mod n 2)` is one of `{0, 0, 0, 1}` at those four corners, always
   `< 2`), then force it equal to the EXECUTABLE witness `divMod 2 (2a+r)
   (div (2a+r) 2) (mod (2a+r) 2)` (`p.div_mod_exec`) via `div_mod_unique`.
   This is a GENERAL arithmetic fact, not specific to `land` — worth
   promoting to a shared helper (`ops.rs` or `binary.rs`) rather than
   inlining it three times for `land`/`lor`/`ldiff`.

**Per-operator differences the transport has to account for** (same shape
as the `nat-fuel-transport` lane's own findings, `docs/plan/status/239.md`):
`lor`'s per-bit combine is `max` (via `ble` + `bool_select_nat`, not `mul`),
and its fuel-exhaustion row returns `n` rather than `0`, so its
`lor_succ_of_pos` analogue and its `m = 0`/`n = 0` base/step cases will NOT
match `land`'s shape byte-for-byte (`lor 0 n = n`, not `0` — the base case at
`m = 0` needs `testBit n i` on the RHS, not `0`, so the whole 3-way split's
`m = 0` branch differs in KIND from `land`'s, not just in which lemma
closes it). `ldiff`'s per-bit combine is `beq`-based
(`if mod n 2 = 0 then mod m 2 else 0`) and its base cases are the HYBRID
already documented in `ldiff.rs`'s module doc (`ldiff 0 n = 0` like `land`,
`ldiff m 0 = m` like `lor`). Budget each of `lor`/`ldiff` as a real,
separate proof, not a copy-paste of `land`'s — this project's own bitwise
history (CLAUDE.md's Gotchas) has been wrong about that sizing before.

**Negative controls to build alongside each, per CLAUDE.md's rule that a
control copied from a sibling can be vacuous:** for `land`, use two
bit-differing numerals (e.g. `testBit (land 3 5) 1` vs `testBit 3 1 * testBit
5 1` — `3 = 011`, `5 = 101`, bit 1 differs) — do NOT reuse `land_three_five`'s
own numerals uncritically without checking they discriminate at the
SPECIFIC index chosen. For `lor`/`ldiff`, derive a fresh witness per operator
and verify by hand simulation before committing to a Rust proof (exactly
the discipline `nat-fuel-transport` used for its own fuel-irrelevance
witnesses).

**On the live gate script, for the coordinator:** even after this bridge
lands (for one, two, or all three of `land`/`lor`/`ldiff`),
`testBit_land`/`_lor`/`_ldiff` STILL cannot be closed as `ml430` mirrors
without either (a) building a genuine Bool-valued `Nat.testBit` (this
kernel already has a real two-constructor `Bool` with `Bool.rec`, `Nat.beq`/
`Nat.ble` already return it, so `testBitBool n i := beq (testBit n i) 1`
is a ONE-LINE wrapper — the "new infrastructure" `docs/plan/status/235.md`
sized as substantial may be smaller than it looked, though the AND/OR/NOT
combinators and their equations over that Bool type are still real proof
work), AND (b) updating or retiring
`scripts/gen-autogenesis-bitwise-family-projection.py`'s hard assumption
that these three facts stay `open` forever. Neither is this lane's call to
make unilaterally — flag it for the next session's planning pass.
