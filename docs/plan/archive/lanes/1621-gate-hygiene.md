# Lane: gate-hygiene — bring check-absence-claims.py toward budget, correct stale sqrt-absence comments

<!-- plan-section: lane-status -->

**Your lane's block (`DONE this pass`, gate-hygiene, 2026-09-04).**

**(A) `check-absence-claims.py`.** Measured RED on main: 206 bare
named claims (budget 122), 2 EXPIRED (`Rat.prodRange` landed `68f452c23`
2026-09-02, `Nat.factorization` landed `8b5fbe799` 2026-08-25) — both
retired-as-present with the landing commit named in the surrounding prose
and the marker flipped `absent:` -> `was-absent:`. Both live in files this
lane does not own (`277-cas-multivariate.md`, `316-queue-sweep.md`).

Bare count brought from 206 to 150 (56 sites annotated: 37 `was-absent:`
retired-because-present, 17 `absent:` still-genuinely-absent, and 2 sites
carrying BOTH — one name resolved present, one still absent, in the same
unit — see the report for the full per-site list) by hand-verifying each candidate
against a fresh `kernel_declaration_projection` (32,935 rows) rather than
bulk-annotating. Two markers were caught and corrected mid-pass: `Nat.ModEq`
resolves present only via SPELLING NORMALIZATION to the kernel's lowercase
`Nat.modEq` — a naming-convention mismatch, not a landing event — so those
two sites carry `was-absent:` with that note rather than `absent:`, which
would have gone EXPIRED. <!-- was-absent: Nat.ModEq --> **Still 28 over budget (150 vs 122).** The
remaining bare sites are, by sampling, dominated by three unfixable-by-marker
shapes: (1) a THREE-segment name (a member under a namespace member) where
`DECL_RE` truncates to a present two-segment prefix, so the harvested
candidate is present even though the real, longer subject is not; (2) a
claim scoped to one BUILD-ORDER POSITION or to a FOREIGN import stream,
where the kernel-wide declaration is present today and a marker would
misattribute the claim; (3) sentence-level candidate harvest citing a
PRESENT declaration as evidence next to an unrelated gap elsewhere in the
same sentence. Gate is registered in `scripts/check.sh:384`
(`step absence-claims`); it is NOT in `hooks/pre-push` — recommend against
adding it there un-gated, since it needs a fresh `--release`
`kernel_declaration_projection` build (multi-minute) on every push, and
`check.sh`/`just check` already run it once per aggregate pass.

**(B) Stale `creal_point.rs`/`creal_point_tests.rs` sqrt-absence
comments.** Corrected 9 doc-comment sites (Rust comments only, no code, no
declarations) claiming "this kernel has no `CReal.sqrt`" or "the norm form
is not expressible/unreachable here" — false since `CReal.sqrt` landed
`b10f4ccb1` 2026-08-26 and the unsquared Cauchy-Schwarz/triangle inequality
now exist as `Metric.CPoint.dotLeSqrtMul`/`distTriangle` in `metric.rs`
(`b34e2dbd7`, 2026-09-04). `crates/axeyum-lean-kernel/src/creal_point.rs`
already carried one self-correcting note (`CPointPrelude::norm`'s own doc:
"several doc comments above still say it does not [exist], and they are
stale") — this pass is that correction. `cargo check -p axeyum-lean-kernel`,
`cargo fmt --all --check`, and `RUSTDOCFLAGS="-D warnings" cargo doc -p
axeyum-lean-kernel --no-deps` (pre-existing unrelated failures in
`ring/nat.rs`/`tactic.rs`, confirmed via `git diff --stat` those files are
untouched) all green on the touched files.

<!-- plan-section: landed-changes -->

| 2026-09-04 | gate-hygiene | resolved 2 EXPIRED absence claims (`Rat.prodRange`, `Nat.factorization`, both landed) and annotated 56 more bare-named absence-claim sites (37 `was-absent:` retired-as-present, 17 `absent:` still-live, 2 carrying both), bringing `check-absence-claims.py`'s bare count from 206 to 150 against a budget of 122 — not yet green, remaining sites are dominated by 3+-segment names and build-order/foreign-stream-scoped claims the marker grammar cannot honestly express |
| 2026-09-04 | gate-hygiene | corrected 9 stale "no `CReal.sqrt`" / "not expressible here" doc comments in `creal_point.rs` and `creal_point_tests.rs`, false since `CReal.sqrt` (`b10f4ccb1`, 2026-08-26) and `Metric.CPoint.dotLeSqrtMul`/`distTriangle` (`b34e2dbd7`, 2026-09-04) landed; doc comments only, no code or declarations touched |
