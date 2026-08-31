# Lane: euler-assembly — finish item 3 of the Fermat -> Euler handoff

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, euler-assembly, 2026-08-31).** Dispatched to
pick up item 3 of `docs/plan/status/374-euler-theorem.md`/
`docs/plan/status/euler-theorem-spine.md` (the final product/power
assembly the handoff called genuinely new mathematics) after
`euler-theorem-spine` closed item 2 and re-sized item 1. **Closed the whole
handoff: `Int.euler_totient_theorem` is proved, axiom-free, admitted by the
kernel on the first attempt.**

Landed in order, each verified against `cargo test -p axeyum-lean-kernel
--lib int_prelude::` (56 passed, 0 failed throughout, including
`every_int_declaration_is_checked_and_axiom_free` and
`derived_laws_have_no_axiom_footprint`) before moving to the next:

1. `Int.prodRangeIf_coprime` (`euler_prod_coprime.rs`) — a restricted
   product of `m`-coprime factors stays coprime to `m`. The one piece
   needing a genuine new induction; a hypothesis-carrying `Bool` case split
   (`bool_case_int`, ported from `nat_prelude/subset_product.rs::bool_case`)
   was needed because the goal genuinely needs `pred k`'s truth value as a
   real premise. Extracted `coprime_mul`/`coprime_one` as reusable
   `pub(super)` helpers in `euler_totient.rs` along the way.
2. `Int.prodRangeIf_factor_const_left` (`euler_prod_factor.rs`) — pointwise
   factoring of a constant out of a restricted product. Not a fresh
   induction: feeds `Int.prodRange_congr` into `Int.prodRange_mul` (both
   already proved).
3. `Int.prodRangeIf_modeq` (`euler_prod_modeq.rs`) — a restricted product
   reduces mod `n` factor by factor. Also not a fresh induction: feeds
   `Int.modEq_prodRange` (already proved) directly.
4. `Int.euler_totient_theorem` (`euler_assembly.rs`) — the nine-step
   assembly wiring all of the above plus `Int.prodRangeIf_permute`,
   `Int.euler_unit_coprime_iff`, `Int.euler_unit_perm_injective`/
   `_maps_into`, `Int.prodRangeIf_const_eq_pow_count`, and
   `Int.modEq_cancel` into one declaration. Admitted first attempt.
   Independently confirmed axiom-free via `theorem_axiom_footprint`:
   `integer  Int.euler_totient_theorem  0`.

Full derivation and the one Rust-level hazard worth remembering (`d.foo(d.bar(...))`
— nested mutable borrows of the same `IntDev` do not compile, `E0499`; every
sub-expression needed its own `let` binding) are in
[ADR-1110](../../research/09-decisions/adr-1110-euler-totient-theorem-lands-axiom-free-first-attempt.md).

**Route taken vs. handoff's sizing:** the handoff (ADR-1025) called item 3
"an induction this kernel has not built before" and left it unsized beyond
that. Verified in-tree at each step per the standing "a handoff's report of
what REMAINS is a hypothesis" rule — three of the four new declarations
needed NO new induction (only the coprimality one did), because the
already-landed unrestricted `Int.prodRange_congr`/`Int.prodRange_mul`/
`Int.modEq_prodRange` lemmas (built for Wilson's theorem and Gauss's lemma)
transported to the restricted (`prodRangeIf`) setting via a pointwise
selector-level lift, with no induction of their own.

**Nothing nearly rebuilt.** `sigma_term`/`nat_abs`
(`euler_unit_range.rs`) were reused unchanged (made `pub(super)`, no
behavior change) rather than reconstructed — matches the "search for the
STEP, not the NAME" discipline this handoff's own docs insist on.

Facts registered: `F:int-prodrangeif-coprime`,
`F:int-prodrangeif-factor-const-left`, `F:int-prodrangeif-modeq`,
`F:int-euler-totient-theorem` (`scripts/gen-kernel-facts.py --prelude
integer --date 2026-08-31 --emit`; 7 other unregistered integer-prelude
theorems belonging to other lanes' work were surfaced and deliberately NOT
emitted, same precedent as every prior update to this handoff).
`validate-facts.py`: 0 errors. `check-settled-fact-statements.py --write`
then bare: PASS. `check-fact-depends-derived.py --fix`: nothing to fix.
`check-autogenesis-holdout-isolation.py`: PASS, unaffected (this lane's
diff never touches `artifacts/autogenesis/`).

`cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D
warnings`: clean, exit 0 (no pre-existing sibling-lane errors blocked this
run, unlike earlier updates to this handoff).

**Not run** (out of scope / no file outside `int_prelude/`,
`artifacts/facts/`, and docs touched): the workspace-wide gate,
`nat_prelude::`/`rat_prelude::` sweeps, `just check`.

**Nothing remains open in the Fermat -> Euler handoff.** Whoever reads
`docs/plan/status/374-euler-theorem.md`/`euler-theorem-spine.md` next should
treat both as historical (superseded by this file and ADR-1110), not as a
live queue entry.

<!-- plan-section: landed-changes -->

| 2026-08-31 | `87c089f59` | `Int.prodRangeIf_coprime` — restricted product of coprime factors stays coprime, axiom-free, item 3's one new induction. |
| 2026-08-31 | `82bfc203c` | `Int.prodRangeIf_factor_const_left` — pointwise factoring of a restricted product, axiom-free, no new induction. |
| 2026-08-31 | `1f6d69245` | `Int.prodRangeIf_modeq` — termwise `ModEq` transport for a restricted product, axiom-free, no new induction. |
| 2026-08-31 | `85614e422` | `Int.euler_totient_theorem` — Euler's totient theorem, axiom-free, admitted first attempt. Closes the Fermat -> Euler handoff. |
| 2026-08-31 | `d79424aa3` | Fact ledger: register the four theorems above. |
| 2026-08-31 | `191b1c23d` | ADR-1110: records the derivation and closes the handoff. |
