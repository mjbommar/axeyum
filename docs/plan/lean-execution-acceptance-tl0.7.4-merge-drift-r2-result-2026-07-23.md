# TL0.7.4 R2 result — historical authority preserved, live input gate repaired

Status: **DONE — offline gate-integrity repair only**

Date: 2026-07-23

Parent:
[accepted TL0.7.4 result](lean-execution-acceptance-tl0.7.4-2026-07-22.md).

Plan:
[R2 merge-drift plan](lean-execution-acceptance-tl0.7.4-merge-drift-r2-plan-2026-07-23.md).

## 1. Verdict

The TL0.7.4 repository-input gate now accepts the current, fail-closed pinned
Lean installer while preserving the accepted execution authority and every
retained evidence byte exactly.

The repair separates two identities that the original validator conflated:

- **historical result inputs** remain the exact files recorded when the
  authority was published, including installer SHA-256
  `75acb49a48e18b43523257ac22bc82889d614a6678c1cc3a457b3a150e1c7f71`
  and the historical generator/test hashes; and
- **current repository inputs** require installer SHA-256
  `8a48e25ee2d2fb6d364dcbe0505b8a2fd660237e18e536d52117dc947d4c71ee`,
  which resolves `elan which lean` under the pinned toolchain, checks the
  resolved executable, and invokes that exact binary.

The current validator checks both boundaries. A changed current installer is a
repository-input failure; a changed historical source-input row is an
authority failure.

## 2. Source-first chronology and implementation correction

The R2 plan was committed and pushed at
`959374cf88de2b9062caf495c6fab4f55adf4f29` before the validator changed.
The accepted implementation was committed and pushed at
`d51650e4dfb7db565fc49724f13882144bdbe75c`.

The plan initially permitted rebinding the authority to the current installer.
A pre-commit deterministic regeneration proved that this would invalidate the
later official-U2 authority chain solely because TL0.7.4's physical seal is a
frozen parent. No such transient output was committed. The accepted correction
instead keeps the historical authority immutable and records the current
validator/test identities independently in the complete-parity registry. This
is stricter than rewriting later U2 history around unchanged evidence.

No `run-pair`, installer, exporter-build, Lean, or official-U2 process ran.

## 3. Preserved evidence and authority

The two TL0.7.4 evidence roots have the same deterministic aggregate digest
before and after R2:

`24ef19e83e10bf1c23739659f7313d4c0fb19dbc82aa97c05da7f40e3af43bd7`

The following values are unchanged:

| Boundary | Preserved value |
|---|---|
| authority physical SHA-256 | `bd3f01fc5ac61bbcfdf23a82055fd58d47cf8167240727ec35e51ceb2a4be05f` |
| authority logical seal | `f8a4d949b5dda4f37f8115a674702eb6dcaccc96394889d1ae3c28febeb4bfa5` |
| retained files / bytes | 67 / 142,523 |
| external attempts / completed controls | 3 / 2 |
| failed-attempt evidence manifest | `c4f9fa088cd0f2fdb8a1cbebc111053252326ce5ea106f3e5ffa6b22ba292ae7` |
| compile completion / projection | `412930affb456cf9b47970af0e886b96dfc370ddbd13abf8d5cba32c681dae5f` / `a3af6c24011d8eb524fed0c1fa8e45cfd2e2330e44adc193b2f1cbea9f54030f` |
| export completion / projection | `9be90a95ed7ade1015598114d43b182b193edbf6063765aee0eae7ce7e14f3a0` / `3585e2daed64c88806906c5921c15f1f1dd14a7e16c7150346a4fe7946cc9ff4` |
| U2/Axeyum/pair/performance/parity credit | 0 / 0 / 0 / 0 / 0 |

Current repair identities are:

- validator: `6b4f39901a76eb84f9ed9920c7e3b1c818a5740385ed4c668bd789c59443fa9a`;
  and
- tests: `a7141dbba6f607d6009a3d12c9a6415fbfaa6921c988acec806d6d19b1abefaf`.

## 4. Validation

The 22-test module passes: 21 offline contract tests and one deliberately
skipped opt-in live sentinel. Added assertions prove the historical/current
installer split, reject current-installer mutation, and require the exact
historical source-input rows in the sealed authority. Deterministic TL0.7.4
authority reproduction passes without changing the authority or summaries.

The complete-parity registry regenerates with only the current validator/test
source identities changed. It remains 0/10 complete populations, 0/12 complete
axes, zero paired cells, zero satisfied gates, and `terminal_ready=false`.

## 5. Nonclaims

R2 closes one semantic-merge gate defect. It adds no Lean execution, official
outcome, Axeyum outcome, dependency edge, native-support fact, pair,
performance measurement, population, axis, gate, or parity credit. It neither
authorizes nor consumes TL0.6.4 M2.1 attempt 001.
