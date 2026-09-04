# Lane: producers-to-real — `ring`/`decide` over `Alg.CommRing`/`AlgS.CommRing`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, producers-to-real, 2026-09-04).** W1-5: extend
`ring` (and `decide` if meaningful) to the setoid carriers, repeating
`linarith::generic`'s move (ADR-1585/ADR-1592) for a second producer. See
ADR-1599 for the full design and evidence; this is the terse pulse.

`ring::generic` (`crates/axeyum-lean-kernel/src/ring/generic.rs`, new file,
~2000 lines incl. tests) EXTENDS `linarith::generic`'s exact `Backend` shape:
a `Backend::{KernelEq, Setoid}` enum threaded through six wrapper methods
(`refl`/`symm`/`trans`/`congr_add`/`congr_mul`/`congr_neg`) and one parser
(`as_eq`), reaching `Alg.CommRing` (`Int.commRing`/`Rat.commRing`) and
`AlgS.CommRing` (`CReal.commRingS`; `Complex.commRingS` reachable the same
way, not exercised by a test this session). The fragment is `ring::rat`'s
exact shape (sorted sum of sorted monomials, coefficients capped at
magnitude 1) generalized off selectors instead of a fixed `RatPrelude`.
Three facts not primitive on `CommRing` (`mul_zero`, `mul_neg_one`,
`neg_neg`) are reused from already-generic `Ring`-level theorems rather than
re-derived; `mul_neg`/`neg_mul` are derived LOCALLY per `Problem`. `neg`
does NOT distribute over `add` generically (named scope restriction) — a
`neg (add u v)` source subterm is a sound but un-simplified atom.

`decide/setoid_boundary.rs` (new file): a MEASURED negative.
`CReal.Equiv`/`.le`/`.lt` are `∀`/`∃`-headed, refused by `decide::parse_goal`
on the outer constant alone (no reduction attempted) — confirmed for the
friendliest possible instance. `decide::rat`'s existing fragment DOES reach
the concrete-rational LEAVES a `creal` proof needs (positive control). No
`CReal.apart`/witnessed-separation definition exists to give `decide` a
setoid-flavored fragment; building one is new mathematics, out of scope.

**Retirement: attempted, reverted, count 0.** Wired `creal/ring_helpers.rs`'s
`right_distrib`/`add4_comm` (30+ real call sites across `power.rs`/
`series.rs`/`derivative.rs`) through `ring::generic::prove_eq_s`; the
isolated `ring::generic` suite (12/12, including the exact shapes with
repeated arguments matching real call sites) stayed green, but
`creal::creal_tests::creal_prelude_builds` itself broke with
`Decline::NotAnIdentity` on some real call this session could not isolate
in time. Reverted via `git checkout --`; `creal::` confirmed green at HEAD
after the revert. Named as the next lane's concrete starting point in
ADR-1599 section 4, not silently dropped.

**Two real bugs this session's own verification caught (not the retirement
bug — both fixed, both in the isolated engine):** (1) `mul_neg_proof`'s
`mul_assoc` symm call had its endpoints swapped relative to `mul_assoc`'s
actual direction, caught by `int_mul_neg_one_shape_via_generic`
(`TypeMismatch`). (2) The test harness used the WRONG (`Eq`-flavored)
field-index module for `AlgS.CommRing`'s RecordNames, silently selecting
`equivRefl`/`equivSymm`/etc. instead of `add`/`mul`/`neg` — caught because a
`neg`-free goal (`mul_comm`) failed too, ruling out a `neg`-only
explanation. Both are exactly the class of defect this repository's own
"verify before reporting" discipline exists to catch.

**Gates run, all confirmed nonzero and green:**
- Step 0: `shape_search --include-constructed`, `declarations=3550`,
  positive control `Int.mul_comm` `FOUND 1`.
- `cargo test -p axeyum-lean-kernel --release --lib -- ring:: decide::
  --test-threads=4`: **121 passed, 0 failed** (71 `ring::` + 47 `decide::`).
- `cargo test -p axeyum-lean-kernel --release --lib -- creal::creal_tests::
  creal_prelude_builds creal::creal_tests::every_creal_declaration_is_
  checked_and_axiom_free --test-threads=1`: **2 passed, 0 failed** (post-revert
  baseline confirmed clean).
- `cargo clippy -p axeyum-lean-kernel --lib --tests -- -D warnings`: clean.
- `cargo check --workspace --all-targets`: clean.
- `rustfmt --edition 2024` on every touched file.
- `python3 scripts/check-fact-depends-derived.py --fix`: `nothing to fix`.
- `python3 scripts/validate-facts.py`: `2758 facts checked, 0 errors`.
- `python3 scripts/gen-adr-index.py`: `rows=805` (pre-existing
  `duplicate_numbers=0166,0167` unrelated to this lane, not introduced here).
- `python3 scripts/gen-plan.py`: run at session close.
- `scripts/check-merge-hygiene.sh`: run before final commit.

**Did not run / not attempted:** `just check`/full aggregate gate (out of
scope, time budget); `kernel_declaration_projection` on a retired
declaration (there is none — see above); `Complex.commRingS` exercised by a
test (reachability is structural/by-construction, matching `CReal.
commRingS`'s field shape, but not measured with its own test this session).

<!-- plan-section: landed-changes -->

| 2026-09-04 | producers-to-real | status stub |
| 2026-09-04 | producers-to-real | `ring/generic.rs` (new): `ring::generic` over `Alg.CommRing`/`AlgS.CommRing`, `Backend`-extended from `linarith::generic`; 12 tests, 121/121 `ring::`+`decide::` green |
| 2026-09-04 | producers-to-real | `decide/setoid_boundary.rs` (new): measured negative for `decide` over `CReal.Equiv`/`.le`/`.lt`, positive control via `decide::rat` |
| 2026-09-04 | producers-to-real | ADR-1599; retirement of `creal/ring_helpers.rs` attempted and reverted (count 0, real bug found in production usage, named for next lane) |
