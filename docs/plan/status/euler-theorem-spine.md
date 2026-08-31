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

<!-- plan-section: landed-changes -->

| 2026-08-31 | `b12847d90` | `Int.euler_unit_coprime_iff` — the full predicate-preservation iff, axiom-free, no new induction; closes item 2 of the Fermat->Euler handoff. |
