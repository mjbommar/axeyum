# Lane: int-gcd-2 — three more `integer-gcd` targets off `gauss_lemma`/`dvd_gcd`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, int-gcd-2, 2026-08-28).** Closed three of the
`integer-gcd` family's remaining open facts, all axiom-free:
`Int.dvd_of_dvd_mul_right_of_gcd_one`, `Int.dvd_of_dvd_mul_left_of_gcd_one`
(both direct corollaries of the already-proved `Int.gauss_lemma`), and
`Int.gcd_greatest` (from the universal property `dvd_gcd`/`gcd_dvd_left`/
`gcd_dvd_right` plus the private `nat_dvd_antisymm` engine `gcd_comm` already
uses). Declarations in `int_prelude/gcd.rs`, wired into `int_prelude.rs`;
`derived_laws` in `int_prelude_tests.rs` recounted 143 -> 146.

**The hand-off claim about `F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e` was
NOT attempted this lane** -- it needs genuine `Int`/`Nat` mod-arithmetic
bridging (reduce a Bezout coefficient mod `k` and show the residue lands in
range), a different shape of work than the three closed here, which are all
direct consequences of already-proved divisibility/universal-property lemmas.
Still open, still `train`, no HELD-OUT/MUTATION marker. The remaining
`integer-gcd` open facts (`F:ml430-int-gcd-div-5e01872f`,
`F:ml430-int-gcd-div-gcd-div-gcd-2db608dc`, and the exists-mul-mod-eq-gcd fact
above) are unclaimed for the next lane.

`F:ml430-int-gcd-div-5e01872f` carries a ⚠ NAMED BY
`check-autogenesis-semantic-contract-target-census.py` marker -- checked
before starting: that script pins the fact's `fact_id` only as a label inside
a static Mathlib-source census (`EXPECTED_NARROWEST`), keyed off
`source_content_sha256`/`missing_dependency`/etc., never off this fact's
`epistemic_status`. Closing the fact does not touch what that script checks.

`cargo test -p axeyum-lean-kernel --lib int_prelude` (`--release` for the
`theorem_axiom_footprint` checkers): before this lane 35 passed (per the prior
lane's status note); after, **38 passed, 0 failed**, ~157s. `clippy --all-targets
--all-features -D warnings` and `cargo fmt --check` both clean on the touched
files. `python3 scripts/validate-facts.py`: 0 errors.

<!-- plan-section: landed-changes -->

| 2026-08-28 | int-gcd-2 | `Int.dvd_of_dvd_mul_right_of_gcd_one`/`Int.dvd_of_dvd_mul_left_of_gcd_one` -- `gauss_lemma` corollaries, axiom-free; closes `F:ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0`/`F:ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b` |
| 2026-08-28 | int-gcd-2 | `Int.gcd_greatest` -- the universal-property characterization of `gcd`, axiom-free; closes `F:ml430-int-gcd-greatest-5b31c5fe` |
