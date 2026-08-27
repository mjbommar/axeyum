# Lane: bridge-ivt — CAS -> kernel bridge, exact polynomial IVT sign bracket

<!-- plan-section: lane-status -->

**Done for this session (bridge-ivt, 2026-08-27).** Moved
`cas-certificate: kernel-reconstructed` off zero (`scripts/validate-facts.py`
read `24 total -- kernel-reconstructed 0, cas-internal 24` at session start;
now `25 total -- kernel-reconstructed 1, cas-internal 24`).

Built `crates/axeyum-lean-kernel/src/rat_prelude/cas_ivt_bridge_tests.rs`: a
translator from `axeyum-cas::real_algebraic::IvtCertificate` to a kernel-checked
`Rat.polyEval`-based sign-bracket theorem, mirroring
`complex/cas_bridge_tests.rs`'s bridge-slice-1 pattern (untrusted CAS search ->
`Kernel::add_declaration` as sole judge, paired accept/reject). Scoped
DELIBERATELY to the sign bracket only (`p(a) < 0`, `0 < p(b)`) — root
containment (exact division) and the Sturm uniqueness count stay
`cas-internal`, per the module's own doc comment and the new fact's `notes`
(sizing both as future slices).

New fact: `F:cas-ivt-sign-bracket-cbrt2-kernel-checked`
(`artifacts/facts/F-cas-ivt-sign-bracket-cbrt2-kernel-checked.json`), a
SIBLING to `F:cas-ivt-cbrt2-in-1-2` (that fact is untouched — its full
IvtCertificate claim, including the Sturm count, remains honestly
`cas-internal`).

No new `rat_prelude` lemma was needed: `Rat.ofInt`/`Rat.ofInt_add`/
`Rat.ofInt_mul` (already landed for `Rat.det2_fib`/Cramer's rule in
`matrix.rs`) were exactly the missing piece.

Tests: `cargo test -p axeyum-lean-kernel --lib
rat_prelude::cas_ivt_bridge_tests::` — 2 passed (degree-3 `x^3-2` cost-curve
instance + one degree-4 `x^4-2` instance), ~5.5s combined in-process; ~8.4s /
~9.4s each when run alone via `--exact` (includes the ~5.3s one-time `Rat`
prelude build, measured separately). Full `rat_prelude::` regression: 94
passed (92 pre-existing + these 2), unaffected.

Mutation-tested in an isolated snapshot (`scripts/lane-snapshot.sh`): a
CAS-input mutation (wrong polynomial) and a kernel-side mutation (wrong
`Nat.le` bound, `6 -> 8`) each independently killed the test with a distinct
failure mode (CAS declines vs. `Kernel::add_declaration` `TypeMismatch`); an
unmutated control passed in the same snapshot both times.

**What's next, not attempted this session:** root containment (exact `Rat`
polynomial division reconstructed in the kernel — a moderate lift, same
`Rat.ofInt_*` machinery generalized from evaluation to division) and the Sturm
count itself (needs a Sturm chain, which needs root-containment's division as
a prerequisite, plus a sign-variation count proved equal to the real-root
count — a substantially larger lift, no partial-credit shortcut). See the new
fact's `notes` field for the full sizing.

<!-- plan-section: landed-changes -->

| 2026-08-27 | `8eb74e605` | `rat_prelude/cas_ivt_bridge_tests.rs`: CAS IVT sign-bracket sign bracket kernel-reconstruction, 2 passing tests, paired accept/reject. |
