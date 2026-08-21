# Official-Lean CI gate audit and repair — 2026-07-21

Status: **current post-FP-soundness population accepts locally 70/70; direct
versioned-executable repair is locally verified; remote rerun remains open**

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

## Post-FP soundness boundary: current 70/70

The 2026-07-22 floating-point soundness repair deliberately revoked whole-
reduction certificate credit from `qf_fp_misc` and both registered QF_BVFP
rows. Their `Fpa2Bv` reductions are not independently certified, so they may
still be solver decisions but cannot remain solver-proof/Lean families. The
old harness continued invoking those rows: `qf_fp_misc` spent more than 30
minutes in Rust-side reconstruction, while `qf_bvfp_float_no_simp3` correctly
declined and panicked the representative gate.

The current registry therefore retains the supported QF_FP constant family,
removes `qf_fp_misc` from that builder, and removes the unsupported QF_BVFP
family. This is a trust-boundary correction, not a proof-coverage win. The
historical 71/71 result above remains evidence for its pre-repair revision; it
is not current credit. A fresh fail-closed local run against the exact pinned
Lean 4.30 executable reports:

```text
[lean crosscheck:representative] checked 70 of 70 modules in 5.9s using 2 jobs (no budget); 0 skipped due to budget; 0 FAILED
LEAN_CROSSCHECK|label=representative|families=70|modules=70|checked=70|budget_skipped=0|failed=0
```

### 2026-08-17: 74 families, and how many of them are reasoning

The population grew to 74 (`qf_bv_wide`, added because the existing `qf_bv`
family runs at `BitVec(2)`, a width at which `term_level_enum_certifies` wins
before bit-blasting is ever reached — so the family named for the foundational
bit-blasting path was handing Lean a structural attestation). A fail-closed local
run of `scripts/check-lean-gate.sh` against the pinned Lean 4.30.0 reports:

```text
[lean crosscheck:representative] checked 74 of 74 modules
LEAN_CROSSCHECK|label=representative|families=74|modules=74|checked=74|budget_skipped=0|failed=0
```

**Superseded 2026-08-17 — the block above is the run as it was measured on
2026-07-21 and is left unedited; a dated audit that gets rewritten when a number
moves stops being evidence.** A `qf_rdl_difference` family was added, because the
representative slice is one module per FAMILY and real difference logic scans
into the `Lra` family, so no module from the QF_RDL *logic* had ever been handed
to `lean`. Re-run against the same pinned Lean 4.30.0:

```text
[lean crosscheck:representative] checked 77 of 77 modules
LEAN_CROSSCHECK|label=representative|families=77|modules=77|checked=77|budget_skipped=0|failed=0
```

The added families are theory reconstructions, not attestations. Measured again
on 2026-08-17 after `ProofFragment::IntFarkas` landed: 37 reasoning families
against 40 attestations (33/41 before), the extra movement being a committed
QF_LIA corpus row that stopped attesting and started reasoning.

GitHub Actions run
[`32045171231`](https://github.com/mjbommar/axeyum/actions/runs/32045171231)
printed the same line. That run's step still FAILED — it greps for an exact
`families=73` pin that the new family invalidated — so this is an acceptance
record, not a green-CI record; the pin was corrected in `2c5356679`.

**Read this number the way the gate now prints it.** 41 of the 74 families emit a
structural attestation and 33 a theory reconstruction, so `74/74 accepted` is
74 modules READ by Lean, not 74 propositions proved. The gate reports the split
and floors the reasoning half precisely so this line cannot be quoted as the
stronger claim.

## 2026-08-21: 78 families, and the gate had been red for two days

A `qf_s_string_length` family was added when the string-length certificate
gained a Lean reconstruction over the **constructed** integers (`integer:
axiom=0`). Re-run on this host against the same pinned Lean 4.30.0
(`d024af099ca4bf2c86f649261ebf59565dc8c622`):

```text
LEAN_CROSSCHECK|label=representative|families=78|modules=78|checked=78|budget_skipped=0|failed=0
```

The added family reasons rather than attests: the split moved to **38 theory
reconstructions against 40 structural attestations** (37/40 before), and the
gate floors the reasoning half at 37 so this cannot be quoted as the stronger
claim. Across all suites: 21 suites, 66 tests, **470 real-Lean checks** against
a floor of 219.

**`scripts/check-lean-gate.sh` itself exits 1 on this run**, and has since about
2026-08-19, for a reason unrelated to the count above:
`real_lean_wellfounded_elaborator_divergence` runs 1 test and reports **ZERO**
real-Lean checks. That is not a flaky suite — the test asserts a specific
account of a kernel/elaborator divergence and its failure message says the
account is wrong:

```text
Lean's elaborator refused the module even with every proof spelled `def`, so the
divergence is NOT the opacity of `theorem` and ADR-0517's account of it is wrong
  Eq.refl has type      Eq AxNat axeyum_proof_share_1 axeyum_proof_share_1
  but is expected to be Eq AxNat axeyum_proof_share_1 AxNat.zero.succ.succ
```

So a committed ADR is contradicted by a committed test, the gate that would say
so is the one gate no host runs by default (`lean` is installed here under
`~/.elan/bin` and not on `PATH` — the trap `check-lean-gate.sh`'s own header
documents), and two separate lanes read the absent binary as "no Lean on this
host". Tracked as an open item; the count above is unaffected, because it comes
from `lean_crosscheck`, which passed 15 tests and 78 checks in the same run.

## First corrected remote attempt: executable identity failure

GitHub Actions run
[`29951909263`](https://github.com/mjbommar/axeyum/actions/runs/29951909263)
was the first retained main-branch execution after the local correction. The
job installed the pinned toolchain and passed the repository-root
`lean --version` step. It then reached the third kernel cross-check and failed
before running the then-71-family solver-proof command.

The test used the explicit path
`$RUNNER_TEMP/axeyum-lean/elan-home/bin/lean`. That path is the elan shim, not
the versioned toolchain executable. The earlier command ran in the repository
and resolved `lean-toolchain`; the test invoked Lean from a temporary working
directory and received:

```text
error: no default toolchain configured. run `elan default stable` to install & configure the latest Lean 4 stable release.
```

The exact failing
[job](https://github.com/mjbommar/axeyum/actions/runs/29951909263/job/89031426984)
is retained as operational evidence. It grants no remote source-acceptance
credit and does not invalidate the bounded local pinned-executable result.

The follow-up implementation now resolves Lean with `elan which lean` under the
explicit repository-pinned `ELAN_TOOLCHAIN`, records that direct versioned
executable in `AXEYUM_LEAN_BIN`, and executes it from `$RUNNER_TEMP` before
exporting the environment. The checksum-pinned installer also reports the
resolved path and invokes that path directly for its version record. Local
changed-working-directory verification passes. A full remote rerun is still
required before this repair receives remote acceptance credit.

## CI acceptance contract

The CI job now has five independently visible gates:

1. checksum-verified elan installation;
2. the repository-pinned `lean --version`;
3. the standalone real-inductive integration test;
4. the representative solver-proof test with `AXEYUM_REQUIRE_LEAN=1`, zero
   budget, and two workers; and
5. an exact grep for the 70-family, 70-module, 70-checked, zero-skipped,
   zero-failed attestation.

Changing the family registry without updating the expected denominator makes
CI fail rather than silently shrinking coverage. Missing Lean, an invalid
binary, reconstruction failure, official-Lean rejection, budget exhaustion, or
an absent summary also fails.

## What this closes—and what it does not

This closes current local representative **source acceptance** for 70
registered solver-proof families, fixes the stale FP-family admission plus the
missing-binary skip, and locally fixes working-directory-independent executable
identity. It does not prove:

- that the workflow is remotely green; the first corrected remote attempt
  failed on executable/toolchain resolution before the representative sweep;
- exhaustive acceptance of every module produced by every family;
- truth of the 65 reconstruction-prelude assumptions (64 arithmetic/integer
  plus the opaque string `append` assumption);
- absence of unexpected axioms beyond the existing `sorryAx` rejection; or
- general Lean-core, mathlib, tactic, or ecosystem parity.

The next gate is one successful remote job whose archived log contains the
installer record, versioned executable identity from a non-repository working
directory, Lean version, all kernel differential passes, and exact 70/70
attestation. After that, add a machine-checked expected-axiom inventory and only
then size the scheduled exhaustive sweep. Do not turn 70 representative modules
into “70 complete proof families” or “Lean parity.”
