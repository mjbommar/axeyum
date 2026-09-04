# ADR-1594: the crosscheck pin moves to Lean 4.34.0-rc1, and the suites follow the pin file instead of carrying literals

Date: 2026-09-03
Status: Accepted
Lane: `coordinator`

Index-summary: `lean-toolchain` moves from `leanprover/lean4:v4.30.0` to
`leanprover/lean4:v4.34.0-rc1` for the real-Lean crosscheck, replay and
golden suites; seven suites that asserted the version as a literal now read
it from the pin file; the Mathlib import toolchain stays at its own v4.30.0
snapshot because the ml430 corpus is keyed to it.

## Context

The repository pins the official Lean it cross-checks against in
`lean-toolchain`, and `tests/support/lean_probe.rs` resolves exactly that
toolchain (ADR-0514's "which binary" rule). Two toolchains have been
installed on the dev host since 2026-08-17 (4.30.0 and 4.34.0-rc1), and the
module banner already carries the compiler-internal constants 4.34 needs
(`lcErased`, measured 2026-08-17: 21 of 77 crosscheck families died on
4.34.0-rc1 without them). On 2026-09-03 the user asked for the target to move
to 4.34.0-rc1.

## Decision

1. `lean-toolchain` names `leanprover/lean4:v4.34.0-rc1`. CI installs
   whatever the pin file says (`scripts/install-pinned-lean.sh`), so no
   workflow edit is needed.
2. The seven suites that asserted `version_text.contains("4.30.0")` (six
   kernel crosschecks and `real_lean_wire_differential`) call
   `lean_probe::assert_pinned_version`, which reads the pin file. The
   strict-positivity suite's exact-commit assertion is replaced by the version
   assertion: a released toolchain version names one commit, and the pin file
   is the single authority. Moving the pin again is one line.
3. **The import toolchain does not move.**
   `scripts/provision-lean-import-toolchain.sh` builds Mathlib at
   `c5ea0035` with `lean4export` at `a3e35a58`, and that Mathlib snapshot's
   own `lean-toolchain` is v4.30.0; every `F:ml430-*` fact and every
   `mathlib-v4.30.0-*` stream is keyed to it. The `Lean4ExportMetadata::axeyum("4.30.0")`
   labels on exported streams describe that corpus dialect and stay.

## Measurement

Full `scripts/check-lean-gate.sh` under the new pin, before the suite edits:
8 of 27 suites failed. Seven failed on the literal version assertion and
nothing else. The eighth, `real_lean_wellfounded_elaborator_divergence`,
failed on its own step 3 under BOTH toolchains, which is a defect in the
suite's 2026-08-18 claim rather than in either Lean; ADR-0517 carries the
amendment and the suite now pins the measured behaviour.

## Consequences

- Every real-Lean verdict in the tree is now "against 4.34.0-rc1" and any
  claim quoting "Lean 4.30.0 refuses/accepts X" in a doc comment is a
  historical measurement, not the current gate.
- A host with only 4.30.0 installed resolves NOTHING for the crosschecks and
  says so (`lean_probe` has no "nearest version" fallback by design); run
  `elan toolchain install leanprover/lean4:v4.34.0-rc1`.
- The next pin move edits `lean-toolchain` and nothing else in the suites.
