# Official-Lean CI gate audit and repair — 2026-07-21

Status: **local 71/71 acceptance measured; remote CI acceptance pending**

## Why this audit exists

The parity plan described the representative solver-proof sweep as mandatory in
CI, but the latest inspected job never ran either repository cross-check. It
installed Lean 4.30 and then failed inside `leanprover/lean-action@v1` because
the Axeyum repository has no `lake-manifest.json`.

This was not a transient runner problem. The action's
[`scripts/config.sh`](https://github.com/leanprover/lean-action/blob/v1/scripts/config.sh)
unconditionally checks for `lake-manifest.json` before considering the
`auto-config`, `build`, `test`, or `lint` settings. The action targets Lake
projects. Axeyum is a Rust project that emits standalone Lean modules, so using
the action only as a toolchain installer was structurally wrong.

The failed setup had hidden a second problem: the solver harness mentioned
`AXEYUM_REQUIRE_LEAN` in planning commands, but `run_lean_checks` still returned
success when no Lean binary existed. The separate inductive integration test
was fail-closed; the 71-family solver-proof gate was not.

## Installer correction

`.github/workflows/ci.yml` now calls `scripts/install-pinned-lean.sh`. The script:

- supports only the CI's explicit Linux x86-64 platform;
- downloads the official `leanprover/elan` **v4.2.3** release asset;
- verifies SHA-256
  `df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2`
  before extraction;
- reads the Lean version from the repository's `lean-toolchain` file
  (`leanprover/lean4:v4.30.0`); and
- installs into a caller-provided isolated root without requiring or inventing
  a Lake manifest.

The checksum is the digest published by the official
[`elan` v4.2.3 release](https://github.com/leanprover/elan/releases/tag/v4.2.3).
The installer is idempotent and emits a structured `LEAN_INSTALL` record.

## First real representative run: 67 accepted, four rejected

With the setup barrier removed, the first bounded local run used official Lean
4.30, one Cargo build job, two Lean workers, and no time-budget skip. It exposed
four genuine external-export failures:

| Family | Official Lean result | Cause |
|---|---|---|
| `quant_bv_negated_existential_witness` | rejected | proof relies on `Bool.rec` iota computation, but Bool was exported as opaque axioms |
| `quant_bv_vacuous_exists_counterexample` | rejected | same missing Bool recursor computation |
| `quant_bv_closed_universal_counterexample` | rejected | proof relies on a generated BV recursor, but the BV family was exported as opaque axioms |
| `quant_bv_source_instance_set` | rejected | generated declaration exceeded Lean's default elaborator `maxRecDepth`; the later theorem name was consequently unavailable |

The exact structured result was:

```text
LEAN_CROSSCHECK|label=representative|families=71|modules=71|checked=67|budget_skipped=0|failed=4
```

This falsifies the earlier inference that in-tree kernel acceptance plus a wired
external command implied 71-family official-Lean acceptance.

## Narrow corrections and rerun

The three computation failures now use
`render_lean_module_with_inductives` for the exact flat Bool/BV families whose
recursors must compute. Official Lean regenerates their constructors and
recursors, retaining iota rules instead of trusting opaque recursor signatures.
The source-instance module already used real inductives; its exported module now
records `set_option maxRecDepth 100000`. A direct control showed that this bound
alone makes the previously rejected module check, so it is an elaboration bound,
not a proof-rule change. The module carries the option itself rather than
requiring an undocumented command-line flag.

The same bounded command then passed:

```text
[lean crosscheck:representative] checked 71 of 71 modules in 6.8s using 2 jobs (no budget); 0 skipped due to budget; 0 FAILED
LEAN_CROSSCHECK|label=representative|families=71|modules=71|checked=71|budget_skipped=0|failed=0
```

A later same-shape confirmation also passed 71/71 but reported 53.3 s in the
Lean-worker phase. The local timings are therefore setup/load observations, not
a performance claim; the first remote job still needs to archive duration and
RSS under a named runner environment.

The standalone real-inductive integration test also passed under Lean 4.30. A
negative control hid Lean from the solver test while setting
`AXEYUM_REQUIRE_LEAN=1`; the test failed with status 101 and the exact diagnostic
`71 modules NOT checked`. Optional local runs may still skip, but required runs
cannot.

```text
MISSING_LEAN_FAIL_CLOSED|status=101
```

## CI acceptance contract

The CI job now has five independently visible gates:

1. checksum-verified elan installation;
2. the repository-pinned `lean --version`;
3. the standalone real-inductive integration test;
4. the representative solver-proof test with `AXEYUM_REQUIRE_LEAN=1`, zero
   budget, and two workers; and
5. an exact grep for the 71-family, 71-module, 71-checked, zero-skipped,
   zero-failed attestation.

Changing the family registry without updating the expected denominator makes
CI fail rather than silently shrinking coverage. Missing Lean, an invalid
binary, reconstruction failure, official-Lean rejection, budget exhaustion, or
an absent summary also fails.

## What this closes—and what it does not

This closes local representative **source acceptance** for 71 registered
solver-proof families and fixes the missing-binary skip. It does not prove:

- that the workflow is remotely green; no run on this branch has yet supplied
  that evidence;
- exhaustive acceptance of every module produced by every family;
- truth of the 64 asserted arithmetic prelude axioms;
- absence of unexpected axioms beyond the existing `sorryAx` rejection; or
- general Lean-core, mathlib, tactic, or ecosystem parity.

The next gate is one successful remote job whose archived log contains the
installer record, Lean version, inductive-test pass, and exact 71/71 attestation.
After that, add a machine-checked expected-axiom inventory and only then size the
scheduled exhaustive sweep. Do not turn 71 representative modules into
“71 complete proof families” or “Lean parity.”
