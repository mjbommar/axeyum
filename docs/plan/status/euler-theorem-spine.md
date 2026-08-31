# Lane: euler-theorem-spine — complete the Fermat → Euler spine (§2.2)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, euler-theorem-spine, 2026-08-31).** Dispatched to
verify and complete the three-piece handoff in
`docs/plan/status/374-euler-theorem.md` (item 1: bridge `Int.euler_unit_injective`
to `Int.prodRangeIf_permute`'s `Nat -> Nat` self-map; item 2: the converse of
the predicate-preservation hypothesis; item 3: the final product/power
assembly). All three were re-verified in-tree per the standing "a handoff's
report of what REMAINS is a hypothesis" rule, not inherited.

**Item 2 closed, axiom-free.** `int_prelude/euler_unit_preserve.rs` (new)
declares `Int.euler_unit_coprime_iff : n a k, 0 < n -> 0 <= k -> k < n ->
Coprime a n -> (Coprime k n <-> Coprime (emod (a*k) n) n)`. Forward direction
is `Int.euler_unit_coprime` directly; backward applies the same lemma a
second time at `a`'s own modular inverse (`Int.modEq_inverse_exists`,
commuted via `Int.mul_comm`, fed through `euler_totient.rs`'s private
Bézout-extraction step — made `pub(super)` as `coprime_of_modeq_inverse` for
this reuse), then a `ModEq`/ring chain (`emod_modeq_self`, `mod_eq_mul_left`,
`mul_assoc`, `mod_eq_mul_right`, `one_mul`, `mod_eq_trans`) identifies the
resulting residue with `k`, closed by `emod_eq_self_of_in_range`. **No new
induction anywhere in this file.** Admitted by the kernel on the first
attempt. `theorem_axiom_footprint` (via
`cargo run --release -p axeyum-lean-kernel --example theorem_axiom_footprint
-- euler_unit_coprime_iff`) confirms footprint **0**:

```
integer	Int.euler_unit_coprime_iff	0
```

Coverage-checked by `every_int_declaration_is_checked_and_axiom_free`
(`derived_laws` 219 -> 220, recounted with
`scripts/recount-pinned-inventory.py --check`, not incremented by hand).
`cargo test -p axeyum-lean-kernel --lib int_prelude::`: **52 passed, 0
failed** (was 52 passed / 1 failed on the coverage assertion before the
inventory update).

Fact `F:int-euler-unit-coprime-iff` registered via
`python3 scripts/gen-kernel-facts.py --prelude integer --date 2026-08-31
--emit` (the generator surfaced 7 other unregistered `integer`-prelude
theorems belonging to other lanes' work; those 7 were **not** emitted here,
same as `374-euler-theorem.md`'s own precedent). `validate-facts.py`: 0
errors. The fact's discriminating evidence checker
(`theorem_dependency_inventory -- Int.euler_unit_coprime_iff | grep -cE
'^Int\.euler_unit_coprime_iff[[:space:]]'`) re-run and confirmed nonzero.

**Item 1 re-sized, not built.** The handoff called this "an `ofNat`/`natAbs`
round trip and `InjectiveOn`/`MapsInto` re-derived in the other shape."
Verified in-tree: the ORDER half of that round trip is **free by defeq**, not
a lemma to write. `int_prelude/order_coercion.rs`'s
`declare_ofnat_order_coercions` proves `Int.le (ofNat m) (ofNat n) -> Nat.le
m n` with the identity function — `Int.le`/`Int.lt` iota-reduce their
`ofNat`/`ofNat` branch straight to the `Nat` comparison, so the same
hypothesis term type-checks either direction: a `Nat.lt i n` proof already
satisfies `Int.lt (ofNat i) (ofNat n)`, with no lemma application needed.
`Int.of_nat_nat_abs_of_nonneg` (`x = ofNat(natAbs x)` for `0 <= x`, already
in `gcd.rs`) covers the value-side half. What is NOT free, and NOT built
this lane: constructing `Nat.InjectiveOn`/`Nat.MapsInto`
(`nat_prelude/finite.rs`'s bounded-`Nat` definitions,
`∀ i j, i<n -> j<n -> f i=f j -> i=j` / `∀ i, i<n -> f i<n`) for
`sigma(k) := natAbs (emod (a * ofNat k) n)` using `Int.euler_unit_injective`
and these two coercions. Sized at roughly 100-150 lines of proof-term
plumbing (two declarations: `InjectiveOn`, `MapsInto`), no new induction.

**Item 3 untouched.** `prodRangeIf pred (fun _ => a) n = pow a (countRange
pred n)` (new induction pairing `Int.pow`/`Nat.countRange`), pointwise
factoring, termwise `ModEq` transport, and cancellation via
`Int.modEq_cancel`. Confirmed still absent under any name
(`theorem_dependency_inventory -- Int.euler_totient_theorem` /
`-- Int.pow_totient`: no rows). Not attempted this lane; sizing not
re-verified beyond the absence check.

**Full assembly (Euler's theorem itself) is reachable from here, not
proximate.** One honest sentence: with item 2 closed, item 1 re-sized down
to assembly-not-invention, and item 3 the one piece requiring genuinely new
mathematics (an induction this kernel has not built before), Euler's theorem
is a bounded amount of further engineering — plausibly 1-2 more lane
sessions — not a research question; nothing found this lane suggests it is
blocked.

**Corrections made:**
`docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`
§2.2 updated with the per-item verification above (dated 2026-08-31,
superseding the 2026-08-30 three-piece sizing without erasing it).
`docs/research/09-decisions/adr-1025-euler-theorem-item-2-closed-item-1-cheaper-than-sized.md`
is the durable decision-record copy.

**Holdout isolation (never touched `artifacts/autogenesis/`):**
`python3 scripts/check-autogenesis-holdout-isolation.py` — BEFORE:
`AUTOGENESIS_HOLDOUT_ISOLATION|held_out=146|files_scanned=1110|settled=0|references=0|verdict=PASS`.
AFTER (re-run post-changes): same command, same verdict `PASS` (settled=0,
references=0) — unaffected, as expected since this lane's diff never touches
that directory.

**Not run** (per the "run every check in the FOREGROUND, unfinished =
did-not-run" rule and this lane's scope, which is `int_prelude/`,
`artifacts/facts/`, and docs only): the workspace-wide gate,
`nat_prelude::` sweep (no `nat_prelude/` file was touched), `just check`.
Clippy on the whole `axeyum-lean-kernel` crate could not complete cleanly —
it fails on **pre-existing** errors in `nat_prelude/gauss_lemma.rs` and
`nat_prelude_tests.rs` from a sibling lane's committed WIP (commit
`de4cc6d18`, "wip(nat_prelude): Gauss's-lemma..."), unrelated to this lane's
diff and explicitly out of this lane's scope (CLAUDE.md instructs: do not
touch `gauss_lemma.rs`). `cargo check -p axeyum-lean-kernel` is clean.

**Next task for whoever picks this up:** item 1 (`Nat.InjectiveOn`/
`Nat.MapsInto` for the residue-multiplication self-map, ~100-150 lines,
sized above), then item 3 (the assembly induction), then wire
`Int.prodRangeIf_permute` + `Int.euler_unit_coprime_iff` + the item-3
assembly into a single `Int.euler_totient_theorem` declaration.

## Update (`WIP`, euler-spine, 2026-08-31) — item 1 closed, item 3(a) landed

Dispatched to pick up exactly the "next task" above. Both re-verified
in-tree first, per the standing rule.

**Item 1 closed, axiom-free.** New file
`int_prelude/euler_unit_range.rs` declares `Int.euler_unit_perm_injective :
n a, 0 < n -> Coprime a (ofNat n) -> InjectiveOn (fun k => natAbs (emod
(a * ofNat k) (ofNat n))) n` and `Int.euler_unit_perm_maps_into : n a,
0 < n -> MapsInto (fun k => natAbs (emod (a * ofNat k) (ofNat n))) n` (the
second unconditional in `a`). Confirms ADR-1025's finding exactly: the
order-coercion half is free by defeq (`Nat.lt i n`/`Nat.zero_le i` are
used UNCHANGED wherever `Int.lt (ofNat i) (ofNat n)`/`Int.le zero (ofNat
i)` are expected — no `le_of_ofnat_le_ofnat`/`lt_of_ofnat_lt_ofnat` call
anywhere in either proof), and the remaining `natAbs`/`Int.of_nat_nat_abs_of_nonneg`
residue bridging is a direct transplant of `wilson.rs`'s
`declare_inverse_index_injective`/`declare_inverse_index_maps_into`
pattern with the `-1` shift removed. No new induction. Both admitted by
the kernel first attempt.

**Item 3(a) landed — the first slice of the "genuinely new mathematics"
piece.** New file `int_prelude/euler_prod_pow.rs` declares
`Int.prodRangeIf_const_eq_pow_count : pred a n, prodRange (selector pred
(fun _ => a)) n = pow a (countRange pred n)`, by induction on `n` following
`wilson.rs`'s `prod_range_const_one` shape (the unrestricted `a := one`
case, already proved there). The successor step's case split on the
symbolic `pred n : Bool` uses the same "supply the goal at each literal
constructor, apply `Bool.rec` to the symbolic value" idiom
`nat_prelude/totient.rs`'s `count_step_le_one` already uses — no fact about
which branch fires is needed. Fully symbolic proof throughout, admitted
first attempt.

**Still open in item 3:** pointwise factoring (`prodRangeIf pred (fun k =>
a * f k) n = mul (prodRangeIf pred (fun _ => a) n) (prodRangeIf pred f
n)`), termwise `ModEq` transport from `emod (a*k) n` back to `a*k`,
cancellation of `prodRangeIf pred id n` via `Int.modEq_cancel` (needs that
product coprime to `n`), and the final wiring of `prodRangeIf_permute` +
`euler_unit_coprime_iff` + item 3(a) + item 1's `InjectiveOn`/`MapsInto`
into one `Int.euler_totient_theorem` declaration.

Facts registered: `F:int-euler-unit-perm-injective`,
`F:int-euler-unit-perm-maps-into`, `F:int-prodrangeif-const-eq-pow-count`
(`scripts/gen-kernel-facts.py --prelude integer --date 2026-08-31 --emit`;
the generator surfaced 7 other unregistered `integer`-prelude theorems
belonging to other lanes' work, same precedent as this file's own prior
entry — not emitted here). `validate-facts.py`: 0 errors.

Verified: `cargo test -p axeyum-lean-kernel --lib int_prelude::` — 52
passed, 0 failed, both times (after item 1, and again after item 3(a)),
including `every_int_declaration_is_checked_and_axiom_free`. `cargo clippy
-p axeyum-lean-kernel --all-targets --all-features -- -D warnings` — clean
on both new files; the crate still fails on the same pre-existing errors
in `nat_prelude/gauss_lemma.rs` and (newly, since the last update)
`rat_prelude/matrix_invertible.rs`, both unrelated sibling-lane WIP.

**Not run**, same scope reasoning as this file's prior update: the
workspace-wide gate, `nat_prelude::`/`rat_prelude::` sweeps (no file in
either touched), `just check`.

**Next task for whoever picks this up:** item 3's remaining three pieces
(pointwise factoring, termwise `ModEq` transport, cancellation), then the
final `Int.euler_totient_theorem` assembly wiring everything together.

<!-- plan-section: landed-changes -->

| 2026-08-31 | `b12847d90` | `Int.euler_unit_coprime_iff` — the full predicate-preservation iff, axiom-free, no new induction; closes item 2 of the Fermat->Euler handoff. |
| 2026-08-31 | `3545fc120` | `Int.euler_unit_perm_injective`/`_maps_into` — the `Nat`-shaped self-map `Int.prodRangeIf_permute` needs; closes item 1 of the Fermat->Euler handoff. |
| 2026-08-31 | `d71385eeb` | `Int.prodRangeIf_const_eq_pow_count` — a constant-`a` restricted product equals `a` raised to the subset count; item 3(a) of the Fermat->Euler handoff, its first new-induction slice. |
