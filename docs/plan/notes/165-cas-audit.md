# Notes: 165-cas-audit

Detail moved out of [`../status/165-cas-audit.md`](../status/165-cas-audit.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
