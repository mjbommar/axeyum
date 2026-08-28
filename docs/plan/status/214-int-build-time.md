# Lane: int-build-time — is the `int_prelude` test-suite regression real, and what causes it

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, int-build-time, 2026-08-28).** Investigating a
reported `cargo test -p axeyum-lean-kernel --lib int_prelude` regression from
8.65 s (34 tests) to 148.28 s (38 tests) after `bezout_witnesses` landed. Both
reported numbers were taken while up to six lanes were building concurrently,
so the first question is whether the regression survives an uncontended
measurement. Method: time the prebuilt `target/debug/deps/` test binary
directly (no cargo lock), read the harness's own `finished in` line, and use
`--exact` per-test runs to attribute cost.

<!-- plan-section: landed-changes -->

| 2026-08-28 | int-build-time | investigation opened: measure the `int_prelude` suite uncontended before treating the regression as real |
