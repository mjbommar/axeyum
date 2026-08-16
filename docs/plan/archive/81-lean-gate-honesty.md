# Lane: lean-gate-honesty — the real-Lean gate, and what it can prove Lean read

<!-- plan-section: lane-status -->

**The real-Lean gate now counts what it checked (`WIP`, lean-gate-honesty,
2026-08-14).** Landed: ten suites that hand generated modules to an external
`lean` binary used to print `ok` on a machine where Lean 4.30.0 was installed —
`elan` keeps toolchains under `~/.elan/toolchains/*/bin/lean` and puts nothing on
`PATH`, so every private `lean_bin()` concluded Lean was absent and skipped.
Discovery now lives in one place
(`crates/axeyum-lean-kernel/tests/support/lean_probe.rs`, shared by `#[path]`
into both crates), an unresolvable `AXEYUM_LEAN_BIN` is an error rather than a
fall-through (or the `/nonexistent` control proves nothing), a skip prints
`AXEYUM-LEAN-SKIPPED <tag> not_checked=<n>` with where discovery looked, and
`scripts/check-lean-gate.sh` sums the `AXEYUM-LEAN-CHECKED` markers and enforces
a floor. On this box, with no environment variables set at all: **10 suites, 33
tests, 40 real-Lean checks**, up from zero. Reverting `a5975725f`'s export fix
makes it fail with the pre-fix signature (11 passed / 3 FAILED).

Next, in priority order: (1) the defect this gate found on its first honest run —
`lean_crosscheck`'s `quant_bv_source_instance_set` family emits proof shares Lean
reads as `Prop`-valued statements where proof terms are required, plus
undeclared share names; 69 of 70 families pass, and the suite is excluded from
the gate by name until it is fixed; (2) fold `lean_crosscheck` into
`scripts/check-lean-gate.sh` once it is (~60 s); (3) nothing yet enforces that a
NEW suite shelling out to `lean` is added to the gate's manifest — the same
class of hole one level up.

<!-- plan-section: landed-changes -->

| 2026-08-14 | `27d91fa12` | Real-Lean gate: elan toolchain discovery, skips that cannot read as passes, and a counted `scripts/check-lean-gate.sh` in both aggregate gates. |
