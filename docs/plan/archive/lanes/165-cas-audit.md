# Lane: cas-audit — census `crates/axeyum-cas/` for untested-but-load-bearing capability

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this pass`, cas-audit, 2026-08-27).** Censused
709 pub/pub(crate) fns across `crates/axeyum-cas/` (57 src files, excluding
test bodies) against ALL test evidence in the crate — in-file `#[cfg(test)]`
blocks, `tests/*.rs`, `examples/*.rs`, and (checked separately, by hand)
subprocess-driven `bin/*` CLI tests and the `scripts/check-sos-negative-controls.sh`
shell-fixture suite, none of which a plain grep sees. A naive per-file
`#[cfg(test)]`-presence check flags ~72 candidates; cross-referencing every
file's test block (not just its own) against every name drops that to 45; manually
resolving each of those 45 found that nearly all are exercised indirectly
(mvpoly's Groebner primitives via Buchberger's-criterion self-checks in
`groebner.rs`, `ratint.rs`'s `rothstein_trager_resultant` via `log_terms`'s
tests, the SOS checkers via 36 assertions over 21 negative-control fixtures —
confirmed still green this session, `21 negative control fixture(s), 36
assertion(s) run, 0 failure(s)`).

**The real findings, after that reduction:**
- **Untested and load-bearing, now fixed with mutation-verified tests:**
  `MvPoly::derivative_in` and `Monomial::exponent_of` (`src/mvpoly.rs`) — the
  power-rule primitive underlying the SOS Lie-derivative checker, WZ/Gosper
  summation, and telescoping's ratio derivation, with *no* direct unit test
  anywhere despite being load-bearing through several self-checking layers
  that were not GUARANTEED to catch a bug here (only certain to catch one that
  breaks a downstream identity rather than happening to cancel). Also
  `geometry_certify::same_point` — not dead code, it is exposed to Python
  callers via `crates/axeyum-py/src/cas/certify/geometry.rs` with zero test
  coverage on either side of the binding.
- **Untested and unreachable (dead code):** `geometry_json::condition_of` and
  `boolean_anf::BooleanPoly::variable_count` — zero call sites anywhere in the
  workspace, including `axeyum-py`. Reported, not deleted (out of scope for
  this pass; deletion needs its own review of whether either is meant as
  public surface for an as-yet-unwritten caller).
- **No vacuous-checker finding this pass** — unlike the ch19 rational-integration
  precedent this lane's brief was modeled on, every "checker" function found
  untested-by-name (`sos::check::check_lyapunov`/`check_barrier`/
  `check_psd_not_sos`, `gf2_shard::check_shard_directory`,
  `telescoping_check::check_certificate`) turned out to have genuine
  negative-fixture coverage once the non-`cargo test` harnesses were checked.

10 new tests added (6 in `mvpoly.rs`, 4 in `geometry_certify.rs`), each
mutation-verified in this isolated worktree (mutated, confirmed red, reverted,
confirmed byte-identical to the pre-mutation file via `diff`) before being left
in. `cargo test -p axeyum-cas`: 824 lib tests -> 834 (0 failed), full crate
suite (unit + doctests + 6 `tests/*.rs` integration files + 7 `bin/*`
targets) green. `cargo clippy -p axeyum-cas --all-targets -- -D warnings`
clean.

**What was deliberately left**: the remaining ~40 of the original 45 resolved
as adequately (if indirectly) tested and were not touched — adding a direct
unit test to each would be low-marginal-value busywork given the existing
end-to-end coverage (e.g. `groebner.rs`'s Buchberger's-criterion check already
exercises every monomial primitive on every basis it builds). Full per-item
disposition is in this session's report, not filed to a separate doc per
scope (`docs/plan/status/` only).

<!-- plan-section: landed-changes -->

| 2026-08-27 | cas-audit | mutation-verified tests for `MvPoly::derivative_in`, `Monomial::exponent_of` (mvpoly.rs) and `geometry_certify::same_point`, found untested despite being reachable from Python bindings; census of 709 pub items found the crate's apparent test gaps mostly resolve via non-`cargo-test` coverage (CLI subprocess tests, `scripts/check-sos-negative-controls.sh`), with `geometry_json::condition_of` and `boolean_anf::variable_count` confirmed genuinely dead |
