# Lane: lean-pin-gates — one pin, and every Lean gate green under it

<!-- plan-section: lane-status -->

**Next Ten item 1 is `DONE` (lean-pin-gates, 2026-09-05).** ADR-1594
(2026-09-03, `792224e73`) moved `lean-toolchain` to
`leanprover/lean4:v4.34.0-rc1` and claimed "no workflow edit is needed."
That was false: two checkers had hardcoded an equality between this
**cross-check pin** and the Mathlib **corpus pin** (Lean 4.30.0, mathlib
`c5ea0035`, `lean4export` `a3e35a58`) that ADR-1594 broke.

1. `scripts/install-pinned-lean.sh`'s toolchain regex had no `-rcN`
   alternative — CI's real-Lean cross-check job died at the install step,
   red since `792224e73`. Fixed: factored into `toolchain_pin_is_valid()`,
   accepts `^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$`, exposed
   via a `--validate-only PIN` mode that downloads nothing. New
   `scripts/tests/test-lean-toolchain-pin-regex.sh` (8 controls, registered
   in `scripts/check.sh` beside `lean-toolchain-policy`) exercises the
   regex bare; reverting the `-rcN` alternative fails exactly its two
   `-rc1`-dependent controls.
2. `scripts/check-lean-official-construct-matrix.py` asserted
   `lean-toolchain`'s content equals the construct matrix's registered
   corpus/audit pin — a category error once the two pins could disagree.
   Fixed: a new `crosscheck_pin_failures()` requires only that the file is
   a **well-formed** pin (same shape as the bash regex), independent of the
   corpus pin's `EXPECTED_PINS` equality check, which is unchanged and
   still fails closed on real corpus-pin drift. `--check` and (through
   `derive_matrix_rows`) `gen-lean-complete-parity.py --check` both went
   from exit 1 to exit 0. Three new unit tests
   (`scripts.tests.test_lean_official_construct_matrix`, 20 total, was 17)
   cover: a well-formed pin differing from the corpus pin is accepted; a
   malformed pin is rejected by name; corpus-pin drift is still caught
   independent of the cross-check pin. Mutation-verified: reverting
   `crosscheck_pin_failures` to the old equality form fails 8 of 20 tests.
3. [ADR-1660](../../research/09-decisions/adr-1660-there-are-two-lean-pins-and-every-claim-names-which-one-it-means.md)
   names the two pins, records which existing surface (the fact ledger,
   compatibility matrix, construct matrix, parity registry, thin Lean
   adapter goal pack) is keyed to which, and is the ADR to cite for "which
   Lean pin" going forward. ADR-1594 gained a dated correction block
   (appended, not rewritten) recording that its "no workflow edit" claim
   was false for these two files.

**Measured 2026-09-05, all three exit 0 on the merged tree:**
`python3 scripts/check-lean-official-construct-matrix.py --check`,
`python3 scripts/gen-lean-complete-parity.py --check`,
`./scripts/tests/test-lean-toolchain-pin-regex.sh` (new). Also confirmed
green and unaffected: `python3 scripts/gen-lean-compatibility.py --check`
(13 rows, unchanged); `python3 -m unittest
scripts.tests.test_lean_official_construct_matrix` (20 tests);
`python3 -m unittest scripts.tests.test_lean_complete_parity` (25 tests);
`./scripts/check-merge-hygiene.sh` (PASS; the pre-existing
`0166`/`0167` duplicate ADR numbers are unrelated to this lane and were not
touched).

Not run: `just check` / the full `./scripts/check.sh` aggregate (out of
scope for this lane's time budget; the specific Lean gates above were run
directly and bare, per the task's discipline). The real-Lean suites
(`scripts/check-lean-gate.sh`, `test-lean-toolchain-policy.sh`) that
require an installed pinned toolchain were not run on this host — did not
run, not claimed green.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `f02c8d530` | `install-pinned-lean.sh` accepts the `-rcN` pin shape via a factored `toolchain_pin_is_valid()` + `--validate-only` mode; new `scripts/tests/test-lean-toolchain-pin-regex.sh` (8 controls, no network) registered in `scripts/check.sh` |
| 2026-09-05 | `9752b4416` | `check-lean-official-construct-matrix.py`'s `crosscheck_pin_failures()` checks well-formedness of `lean-toolchain` instead of equality to the corpus pin; 3 new unit tests; `docs/plan/generated/lean-complete-parity.json` refreshed (unrelated stale `ci.yml` hash) |
| 2026-09-05 | `e2218738c` | ADR-1660 names the two Lean pins and which surface is keyed to which; dated correction block appended to ADR-1594; ADR index regenerated |
