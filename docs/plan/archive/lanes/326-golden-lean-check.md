# Lane: golden-lean-check — real-Lean crosscheck for the four unverified golden-pin suites

<!-- plan-section: lane-status -->

**Done (`golden-lean-check`, 2026-08-30).** Of the five golden-pin suites
(`diophantine_lean_reconstruct`, `quant_affine_growth_lean`,
`quant_counterexample_cover`, `quant_eq_partition_lean`, `quant_residue_lean`),
only diophantine's had a real-Lean check before this session; the other four
only asserted the rendered bytes matched a blessed `(length, fnv1a64)` hash — a
byte pin says nothing about whether Lean still accepts the module. Added a
`*_module_checks_in_real_lean` test to each of the four, following
diophantine's existing pattern (`lean_probe::lean_bin_or_skip` /
`report_checked`) exactly.

Verified in the foreground, one suite at a time, against the pinned Lean
4.30.0 (`AXEYUM_LEAN_BIN=~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean`,
`AXEYUM_REQUIRE_LEAN=1`):

- `quant_affine_growth_lean`: 5 tests, 1 real-Lean check, 49.9 s wall (cold
  build; ~5.1 s of that is the suite itself).
- `quant_counterexample_cover`: 8 passed / 1 ignored, 1 real-Lean check,
  30.2 s wall (24.8 s suite; this suite's public-corpus reconstruction test
  is separately `#[ignore]`d, unrelated to this change).
- `quant_eq_partition_lean`: 7 tests, 1 real-Lean check, 6.1 s wall.
- `quant_residue_lean`: 4 tests, 1 real-Lean check, 5.7 s wall.
- `diophantine_lean_reconstruct` (unmodified, re-run as a control): 5 tests,
  1 real-Lean check, 6.4 s wall.

Total: **5 `[lean ok]` lines**, one per suite, all passing, none of them
`AXEYUM-LEAN-SKIPPED`. None of the added modules is disproportionately slow —
the four new checks each cost roughly the same single Lean invocation the
existing diophantine check already pays (order of 1-5 s of the suite's own
wall time; the affine-growth suite's larger wall time is a cold `cargo`
rebuild, not the Lean check itself).

Doctored-module negative control, run manually per suite (not committed as a
permanent test — same as diophantine's own check has none): copied each
suite's already-written `.lean` module, flipped the theorem's stated type from
`theorem axeyum_refutation : False :=` to `... : True :=`, and re-ran the
pinned `lean` binary directly. All five (including diophantine, as the
existing-shape control) rejected with `exit 1` and a type-mismatch error
(`... but is expected to have type True`). So each new check can fail.

Also wired the four new suites into `scripts/check-lean-gate.sh`'s suite list
(next to `diophantine_lean_reconstruct`) and raised `CHECK_FLOOR` 219 -> 223 —
without this, a plain `cargo test` on these suites just prints
`AXEYUM-LEAN-SKIPPED` and passes when no Lean is found, which is the exact
"skip reads as a pass" failure this whole family exists to close.
`check-lean-gate.sh` is already registered in both `scripts/check.sh`
(`step lean-gate`) and the justfile's `check` recipe, so no further
registration was needed.

Did not run: `scripts/check-lean-gate.sh` itself (21 suites, well beyond the
task's scope — instructed to run only the five suites, `cargo fmt --all
--check`, and clippy on this crate), `just check` / `./scripts/check.sh`
(explicitly out of scope; the dispatching lane re-verifies before merging).
`bash scripts/check-merge-hygiene.sh` run at the end of this session — see its
output in the commit history / session report.

No pin constants were changed; `diophantine`'s existing test is untouched
except that it was re-run (unmodified) as a control.

<!-- plan-section: landed-changes -->

| 2026-08-30 | golden-lean-check | Added `*_module_checks_in_real_lean` to `quant_affine_growth_lean`, `quant_counterexample_cover`, `quant_eq_partition_lean`, `quant_residue_lean` (real Lean 4.30.0 crosscheck via `lean_probe`, matching `diophantine_lean_reconstruct`'s existing pattern); no pin constants touched. |
| 2026-08-30 | golden-lean-check | Wired the four new suites into `scripts/check-lean-gate.sh`'s suite list and raised `CHECK_FLOOR` 219 -> 223. |
