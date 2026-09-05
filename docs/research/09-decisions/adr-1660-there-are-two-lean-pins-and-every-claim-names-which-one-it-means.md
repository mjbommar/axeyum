# ADR-1660: there are two Lean pins, and every claim names which one it means

Status: accepted
Date: 2026-09-05
Lane: `lean-pin-gates`

Index-summary: `lean-toolchain` (the cross-check pin, ADR-1594) and the
Mathlib corpus/audit pin (Lean 4.30.0, mathlib `c5ea0035`, lean4export
`a3e35a58`) are two different pins that are allowed to disagree; ADR-1594's
"no workflow edit is needed" was false, `install-pinned-lean.sh` and
`check-lean-official-construct-matrix.py` both hardcoded an equality between
them, and both were fixed to accept the cross-check pin moving independently
of the corpus pin.

## Context

ADR-1594 (2026-09-03, commit `792224e73`) moved `lean-toolchain` from
`leanprover/lean4:v4.30.0` to `leanprover/lean4:v4.34.0-rc1` for the
real-Lean cross-check, replay and golden suites, while explicitly keeping
the Mathlib import toolchain at its own pinned `v4.30.0` snapshot (Lean
`d024af09`, mathlib4 `c5ea0035`, `lean4export` `a3e35a58`) because every
`F:ml430-*` fact is keyed to it. Its consequences section said: "The next
pin move edits `lean-toolchain` and nothing else in the suites."

That claim covered the seven Rust suites (`lean_probe::assert_pinned_version`
now reads the pin file) but was false for two other places that had encoded
the same value as a literal, on the unstated assumption that the corpus pin
and the cross-check pin were always equal:

1. `scripts/install-pinned-lean.sh`'s toolchain-value regex,
   `^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+$`, has no alternative for a
   release-candidate suffix. CI's "real Lean kernel + solver-proof
   cross-check" job died at "install pinned official Lean toolchain" with
   `unexpected lean-toolchain value: leanprover/lean4:v4.34.0-rc1`,
   red since `792224e73`.
2. `scripts/check-lean-official-construct-matrix.py`'s `validate_manifest`
   asserted `lean-toolchain`'s file content equals
   `EXPECTED_PINS["lean"]["toolchain"]` — but `EXPECTED_PINS` is the
   construct matrix's registered CORPUS/AUDIT pin (the exact Lean +
   lean4export snapshot its fixtures and computations were generated and
   checked against), a permanent property of already-recorded evidence that
   does not move with the cross-check toolchain. This check conflated two
   pins that happened to be equal before ADR-1594 and diverged after it.
   `python3 scripts/check-lean-official-construct-matrix.py --check` and
   (through `derive_matrix_rows`) `python3 scripts/gen-lean-complete-parity.py
   --check` both exited 1 on a clean tree as a result.

Both defects trace to the same root cause: nothing in the tree had ever
named these as two separate pins, so two independent call sites each
hardcoded the assumption that they were one.

## Decision

There are, and remain, **two Lean pins** in this repository, and any surface
citing "Lean 4.30" or "the Lean pin" must say which one it means:

1. **The cross-check pin** (`lean-toolchain` at the repo root). It names the
   official Lean the kernel differential, replay and golden suites check
   against, follows ADR-0514's "which binary" resolution rule, and is
   expected to move over time — currently `leanprover/lean4:v4.34.0-rc1`
   per ADR-1594. Nothing about it is permanent evidence; it is a live
   dependency version.
2. **The corpus pin** (Lean `4.30.0`, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`;
   mathlib4 `c5ea0035`; `lean4export` `v4.30.0`, commit
   `a3e35a584f59b390667db7269cd37fca8575e4bf`, export format `3.1.0`). It
   names the exact Mathlib/Lean snapshot a fixed body of already-generated
   evidence was produced and audited against, and it is a property of that
   evidence, not a live dependency — it does not move when the cross-check
   pin moves, and it does not need to equal it.

Every `F:ml430-*` fact, the Lean compatibility matrix
(`docs/plan/lean-compatibility-v1.json`, `docs/plan/generated/lean-compatibility.md`),
the official construct matrix
(`docs/plan/lean-official-construct-matrix-v1.json`), the complete-parity
registry (`docs/plan/lean-complete-parity-v1.json`,
`docs/plan/generated/lean-complete-parity.{md,json}`), and the thin Lean
adapter's goal pack (`artifacts/lean-adapter/goal-pack/thin-adapter-v1.json`)
are keyed to the **corpus pin**. The real-Lean kernel differential, replay
and golden suites, and `scripts/install-pinned-lean.sh`, resolve the
**cross-check pin**.

Concretely, two checks were fixed to stop asserting equality between them:

- `scripts/install-pinned-lean.sh` now validates the pin file's value
  against `^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$` — this
  accepts both pins' shapes (a plain release and a release candidate) and
  still rejects anything else. The regex is exercised bare, with no
  download, via a new `--validate-only PIN` mode and
  `scripts/tests/test-lean-toolchain-pin-regex.sh` (registered in
  `scripts/check.sh` beside `lean-toolchain-policy`).
- `scripts/check-lean-official-construct-matrix.py` keeps its existing
  `EXPECTED_PINS` equality check (`data.get("pins") != EXPECTED_PINS`) as
  the corpus-pin registration guard — that pin is real, audited, and must
  not silently drift. It no longer compares the repo's `lean-toolchain`
  file against `EXPECTED_PINS`; instead a new `crosscheck_pin_failures`
  helper checks only that the file is a **well-formed** toolchain pin
  (same shape as the bash regex above), independent of the corpus pin's
  value. `scripts.tests.test_lean_official_construct_matrix` gained three
  tests: a well-formed pin that differs from the corpus pin is accepted, a
  malformed value is rejected by name, and corpus-pin drift is still
  caught independently of the cross-check pin's value.

No change was needed in `scripts/gen-lean-compatibility.py` or
`docs/plan/lean-compatibility-v1.json`: that manifest's `target.lean_version`
field already names the corpus pin (4.30.0) and is never compared against
`lean-toolchain`. It also has no free-text notes field to annotate.

## Evidence

Measured 2026-09-05 on a clean tree at the merge base for this ADR:

- Before: `python3 scripts/check-lean-official-construct-matrix.py --check`
  exits 1 (`lean-toolchain does not match the registered pin`);
  `python3 scripts/gen-lean-complete-parity.py --check` raises
  `ValueError: invalid registration: lean-toolchain does not match the
  registered pin` from `derive_matrix_rows`;
  `./scripts/install-pinned-lean.sh --validate-only leanprover/lean4:v4.34.0-rc1`
  (added by this change to demonstrate the prior behavior) would have
  reported the value invalid under the old regex.
- After: all three exit 0. `python3 -m unittest
  scripts.tests.test_lean_official_construct_matrix` runs 20 tests (17
  prior + 3 new), `python3 -m unittest scripts.tests.test_lean_complete_parity`
  passes, and `scripts/tests/test-lean-toolchain-pin-regex.sh` passes 8
  controls with no network access.
- Mutation control: reverting `crosscheck_pin_failures` to the old
  equality-with-`EXPECTED_PINS` form makes 8 of the 20 construct-matrix unit
  tests fail (`test_committed_product_registration_is_valid` plus the three
  new tests plus four others whose fixtures build on a valid manifest),
  reproducing the exact original defect. Reverting
  `TOOLCHAIN_PIN_REGEX`/`TOOLCHAIN_PIN_PATTERN` to drop the `-rcN`
  alternative makes exactly the two `-rc1`-dependent controls in
  `test-lean-toolchain-pin-regex.sh` fail (controls 1 and 3; the plain
  `v4.30.0` control and every malformed-value control are unaffected).

## Alternatives

- **Make the corpus pin float with the cross-check pin.** Rejected: the
  construct matrix's fixtures, hashes and recorded computations were
  generated against the 4.30.0/`c5ea0035`/`a3e35a58` snapshot specifically;
  re-registering it to 4.34.0-rc1 would either be a lie (the evidence was
  not regenerated) or require regenerating hundreds of fixture hashes for
  no capability gain.
- **Make the cross-check pin equal the corpus pin permanently (revert
  ADR-1594).** Rejected: the compiler-internal constants the 4.34 line
  needs for the kernel differential to work at all
  (`lcErased`, ADR-1594's own motivation) are not present in 4.30.0, and
  the corpus pin's Mathlib snapshot is independently frozen for its own
  reasons (a `mathlib4` clone at `c5ea0035`) that have nothing to do with
  which Lean the kernel differential targets.
- **Assert exact equality between the cross-check pin and a second
  registered literal for "the current cross-check pin".** Rejected: that
  literal would need editing on every future cross-check pin move (exactly
  the maintenance ADR-1594 tried to eliminate for the seven Rust suites),
  recreating a third place a mover could forget. Well-formedness is the
  weakest check that still rejects a genuinely broken pin file.

## Consequences

- A future cross-check pin move (another `-rcN`, or a full release) needs
  no edit to `install-pinned-lean.sh` or
  `check-lean-official-construct-matrix.py` as long as the new value is a
  well-formed Lean toolchain pin — which is now true independent of the
  corpus pin, closing the gap ADR-1594 claimed but did not deliver.
- A future corpus pin move (a fresh Mathlib draw) is a deliberate,
  audited act that edits `EXPECTED_PINS` in
  `check-lean-official-construct-matrix.py`,
  `docs/plan/lean-compatibility-v1.json`'s `target`, and
  `docs/plan/lean-complete-parity-v1.json`, and is expected to require
  regenerating fixture hashes — that check remains strict equality on
  purpose.
- Any doc, ADR, or dashboard that says "the Lean pin is 4.30" or "4.34"
  without saying cross-check or corpus is now an incomplete claim; this
  ADR is the one to cite when disambiguating it.
