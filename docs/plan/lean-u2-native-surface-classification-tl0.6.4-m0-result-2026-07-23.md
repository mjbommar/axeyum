# Lean U2 TL0.6.4 M0 result — complete harness-floor classification

Status: **accepted bounded M0; TL0.6.4 remains PARTIAL**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[source-first M0 plan](lean-u2-native-surface-classification-tl0.6.4-m0-plan-2026-07-23.md),
[complete-parity contract](lean4-complete-parity-contract-2026-07-22.md), and
[U2 registration authority](lean-u2-test-authority-2026-07-22.md).

## 1. Verdict

M0 is accepted for its declared boundary. The canonical
[classification authority](lean-u2-native-surface-classification-v1.json)
classifies all 3,723 registered full-Lake U2 cases exactly once by the minimum
native surface implied by the official harness family. It freezes ten stable
surface IDs, their dependency DAG, fourteen exact family/kind rules, three
case overrides, owners, axes, capability states, and decline codes.

This is a denominator and ownership result, not a compatibility result. Every
case remains `harness-floor`; all 3,723 source-content refinements, exact module
dependency closures, and native outcomes are `not-run`. There are zero Axeyum
outcomes, zero official/Axeyum pairs, zero complete populations or axes, zero
satisfied terminal gates, and no Lean parity credit. In particular, a zero FFI
count at the harness floor is not evidence that no case uses FFI; M1 has not
inspected case contents.

## 2. Source-first sequence

The work was committed and pushed in three separately reviewable checkpoints:

1. `84fb4f58` preregistered the complete M0 contract before implementation.
2. `233a0b00` added the generator, canonical authority, generated summaries,
   and focused mutation/contract tests.
3. `99910216` connected the authority to local parity checks and both CI
   workflows, then regenerated the complete-parity scoreboard without adding
   any terminal credit.

The upstream interpretation was checked against the pinned Lean sources:

- [`tests/README.md`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/README.md)
  describes the official test piles and directories;
- [`tests/CMakeLists.txt`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/CMakeLists.txt)
  registers the families and conditional Lake cases;
- the pinned
  [`compile`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/compile/run_test.sh),
  [`elab`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/elab/run_test.sh),
  [`elab_fail`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/elab_fail/run_test.sh), and
  [`server_interactive`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/server_interactive/run_test.sh)
  runners establish the family-level observable floors.

These sources justify only the M0 harness floor. They do not identify every
construct, import, tactic, RPC method, runtime effect, library, or FFI edge in
an individual case.

## 3. Exact denominator

The authority contains 3,723 unique case rows across fifteen families and all
sixteen registered `(family, kind)` pairs:

| Family | Cases |
|---|---:|
| `bench` | 1 |
| `compile` | 60 |
| `compile_bench` | 24 |
| `doc-examples` | 8 |
| `docparse` | 197 |
| `elab` | 2,854 |
| `elab_bench` | 40 |
| `elab_fail` | 316 |
| `lake` | 52 |
| `lint` | 1 |
| `misc` | 5 |
| `misc_dir` | 2 |
| `pkg` | 27 |
| `server` | 4 |
| `server_interactive` | 132 |

Direct and transitive-closure counts are intentionally separate:

| Native surface | Direct cases | Closure cases |
|---|---:|---:|
| `kernel-import` | 0 | 3,717 |
| `parser-macro` | 197 | 3,717 |
| `elaborator` | 3,217 | 3,717 |
| `tactic-meta` | 2 | 2 |
| `modules-lake` | 81 | 217 |
| `editor-rpc` | 137 | 137 |
| `compiler-runtime` | 282 | 282 |
| `ffi` | 0 | 0 |
| `toolchain-cli` | 6 | 6 |
| `adversarial` | 316 | 316 |

There are 4,238 direct-surface occurrences and 12,111 transitive-closure
occurrences. The closure counts are conservative architectural dependencies,
not evidence that Axeyum implements or ran those surfaces.

## 4. Retained artifacts and identities

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| canonical authority | 4,233,104 | `89b29bc6820d1d948d5cd4defdd28eb59ddb55a5924a3cf770c0b21282959959` |
| generated JSON summary | 8,606 | `3f6b8fec2d9bc0c399b80e4b12f4e10e38aadfc95f0c160750329dbdc1063d34` |
| generated Markdown summary | 2,350 | `7338aad7ec63b5f0192b475246eaeb913b20c8c09e4c412c18a17a453ed8797f` |
| generator | — | `4827fc4ed27e729b36f2c0451059e4a4c7e4186ac8650eb54e8e98b1d740ccf6` |
| focused tests | — | `eb88b21ffb7ba99be7d7f62bed01d1895952c42f6430e2a51d2fa517a61ef551` |

The canonical record seal is
`c9ed3213c6a3679c98665131eddf70c0f2ba83990a1d470ee622cd9652419de6`;
the ordered case-row seal is
`f0c4d2cded9c0fb7a681438d6fe0e7b696e118cdafc5a2281bd13af51d9d1cdd`.

## 5. Validation

The accepted implementation passed:

- ten focused M0 contract/mutation tests;
- eighteen combined U2-registration and M0 tests;
- nineteen combined M0 and complete-parity tests;
- both classification and complete-parity generator `--check` modes;
- Python compilation, shell syntax, whitespace, and documentation-link checks.

The complete-parity generator continues to report:

```text
LEAN_COMPLETE_PARITY|populations=10|complete_populations=0|axes=12|complete_axes=0|paired_cells=0|gates_satisfied=0|terminal_ready=false
```

## 6. Nonclaims and required continuation

M0 does not claim source-level construct discovery, exact import closure,
generated-artifact closure, native library or FFI closure, request-method
coverage, runtime-effect coverage, project dependency closure, native support,
native decline, performance, or semantic agreement.

TL0.6.4 remains PARTIAL until:

1. M1 inspects every pinned primary, sidecar, runner, hook, and directory
   support closure and replaces the family floor with content-backed evidence;
2. M2 derives exact module, generated-artifact, runtime, library, FFI, request,
   and project dependency closures; and
3. M3 reviews every row, resolves every provisional field, and accepts the
   complete classification authority.

Only then may TL0.6.5 form matched native official/Axeyum rows, and those rows
still require complete official execution plus retained native evidence.
