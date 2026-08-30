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

Detail moved to [`../notes/165-cas-audit.md`](../notes/165-cas-audit.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | cas-audit | mutation-verified tests for `MvPoly::derivative_in`, `Monomial::exponent_of` (mvpoly.rs) and `geometry_certify::same_point`, found untested despite being reachable from Python bindings; census of 709 pub items found the crate's apparent test gaps mostly resolve via non-`cargo-test` coverage (CLI subprocess tests, `scripts/check-sos-negative-controls.sh`), with `geometry_json::condition_of` and `boolean_anf::variable_count` confirmed genuinely dead |
