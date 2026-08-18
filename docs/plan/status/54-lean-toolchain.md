# Lane: agent-lean-toolchain — which Lean checked it, and saying so

<!-- plan-section: lane-status -->

**The real-Lean gate now names its checker, and there is only one rule for
picking it (`DONE`, agent-lean-toolchain, 2026-08-17).** Two Lean toolchains are
installed on this box (4.30.0, the pin, and 4.34.0-rc1) and **two discovery
implementations disagreed about which to use**: `scripts/check-lean-gate.sh`
tried `command -v lean` and found elan's default, while `lean_probe.rs` sorted
elan's toolchain directories newest-name-first and took the release candidate.
Under 4.34, 21 of 77 `lean_crosscheck` families were rejected and
`scripts/lean/replay-lean4export.lean` did not elaborate at all — so the gate's
verdict depended on which toolchain happened to be installed and on which entry
point ran, and nothing in the output said which one produced it.
[ADR-0470](../../research/09-decisions/adr-0470-the-pinned-lean-toolchain-is-the-one-that-runs.md)
decides **the pin runs**: `lean-toolchain` is the single source, `PATH` and other
elan toolchains are candidates only if `--version` matches it, there is no
"newest wins" step, and a non-pinned toolchain is a refusal naming both versions
rather than a substitution. Not newest, because
`real_lean_strict_positivity_crosscheck` asserts an exact commit and
`real_lean_wire_differential` is a differential against the reference
implementation; "whatever was installed" makes both meaningless.

Every suite now prints `AXEYUM-LEAN-TOOLCHAIN … bin=… version=… matches_pin=…`
and the gate **fails** if any suite reports a different binary than it resolved,
or reports none — a result that does not name its checker is not evidence.
Measured after the change: 17 suites, 57 tests, **223 real-Lean checks** (floor
208), 37 theory families (floor 37), every suite confirming the same binary.

**The guard is exercised, not asserted.** `scripts/tests/test-lean-toolchain-policy.sh`
(now in `just check` and `check.sh`, ahead of the gate) points both entry points
at the non-pinned 4.34.0-rc1 and requires the refusal by name, checks that the
shell gate and the Rust probe resolve the *same* binary, and — control 5c —
requires the same suite to **pass** once the deviation is stated, so 5b's failure
cannot be dismissed as "4.34 is broken here". Three separate one-guard deletions
each killed **exactly one** control. It also fails rather than passing when no
second toolchain is installed to exercise the wrong-toolchain case.

**4.34 breakage fixed, not merely diagnosed.** `Environment.addDeclCore` gained a
`maxRecDepth : USize` parameter in 4.34, so the replay script died before reading
a byte of the stream; the call is now resolved at elaboration time and
`real_lean_kernel_replay` passes under **both** toolchains (positive replay and
tampered negative control alike).

**Next:** `real_lean_wire_differential`'s own `pinned_lean()` is now a redundant
assertion of the same policy rather than a competing one — collapse it onto
`lean_probe::lean_bin()` when that file is next touched. Unrelated finding for
whoever owns it: `cargo clippy -p axeyum-lean-import --tests -- -D warnings`
fails on `real_lean_wire_differential.rs:458` (`too_many_lines`, 121/100) on
unmodified `HEAD` content.

<!-- plan-section: landed-changes -->

| 2026-08-17 | `b15debdfa` | One Lean resolution policy (the `lean-toolchain` pin) shared by `check-lean-gate.sh` and `lean_probe.rs`; every suite names the binary and version it used and the gate cross-checks them; `replay-lean4export.lean` elaborates under 4.30 and 4.34; exercised negative controls in `scripts/tests/test-lean-toolchain-policy.sh` (ADR-0470) |
