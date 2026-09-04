# Lane: universal-properties — name the universal properties already proved (W1-3, W3-13)

<!-- plan-section: lane-status -->

**Your lane's block (`done`, universal-properties, 2026-09-04).** Landed
`Nat.Peano.initial` and `Int.Characterization.initial` in a new
`crates/axeyum-lean-kernel/src/characterization/universal_property.rs`,
naming the initial-object / natural-numbers-object universal property that
`Nat.Peano.categorical` and `Int.Characterization.categorical` already prove
but never state under that name. Both are built entirely from already-proved
theorems (`iter_zero`/`iter_succ`/`iter_pred`/`iter_unique`/`rec_unique`) —
no new induction, no new axioms. `entries.len()` is now 34 (was 32);
`Weakening::defects()` now 24 (was 22), two new mutation-verified negative
controls (`NatInitialDropUniqueZero`, `IntInitialDropUniqueZero`) confirmed
rejected by the kernel, each targeting the packaged theorem's own uniqueness
clause rather than an upstream dependency. Non-vacuity test instantiates
both at their own carrier (`Nat`, `Int`), the latter discharging the two
inverse-law hypotheses via the ring laws exactly as `categorical_at_int`
does. Curated facts `F:nat-peano-initial` / `F:int-characterization-initial`
added; ADR-1610 records the vocabulary and why `Category`/`Functor` stays
out (roadmap W3-3, separate and not unblocked by this lane). A
`docs/research/08-planning/universal-property-template.md` records the
four-part shape for a future carrier (e.g. a second ℝ construction).

Gates run: `cargo fmt --all --check` clean; full-workspace
`check-clippy-complete.sh` 769/769 targets, 0 diagnostics; `int_prelude::`
87 passed, `nat_prelude::` 473 passed (both via `cargo-serialized.sh test -p
axeyum-lean-kernel`, since the repo-wide `check-workspace-tests.sh` hits a
pre-existing, unrelated host gap: `axeyum-py` fails to link for
`-lpython3.14`, not present on this host); `validate-facts.py` 2781 checked,
0 errors; `frontier-shape-census.py` exit 0; `check-shape-duplicates.py`
15 allowlisted groups, no new unadjudicated one; `gen-adr-index.py` and
`gen-plan.py` regenerated and committed; `check-merge-hygiene.sh` clean
after regenerating PLAN.md and the production-provenance ledger.

<!-- plan-section: landed-changes -->

| 2026-09-04 | universal-properties | `Nat.Peano.initial` / `Int.Characterization.initial` added, 34 axiom-free entries, 24 mutation-verified defects, ADR-1610, template doc, 2 curated facts |
