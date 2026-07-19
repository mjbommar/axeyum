# Glaurung source-backed positive finding control (2026-07-18)

This artifact establishes a nonzero, producer-independent positive control for
Glaurung's solver-authoritative finding comparison. It joins tracked planted
driver source, compiled machine instructions, Glaurung's versioned confidence
partition, and repeated sole-authority executions. It does **not** estimate
real-world prevalence, real-driver recall, or performance.

## Result

The fail-closed join accepts all **14 expected finding rows at 12 machine-code
sites across 9 WDM fixtures**:

- 14/14 source-validated rows are present under sole Z3 authority;
- the same 14/14 rows are present under sole Axeyum authority;
- false negatives: 0;
- unexpected producer-high rows: 0;
- joined recall and precision on this planted control: 1.0 and 1.0;
- all 18 source/binary files match their manifest SHA-256 values and are
  tracked and clean at IOCTLance revision
  `905629a773f191108273a55924accd9f31145a8d`.

The authority harness ran two order-balanced repetitions per backend and
driver, for 36 processes. Every per-driver output and solve count was stable:

| Fixture | Validated high rows | Raw rows | Diagnostic rows | Solves per process |
|---|---:|---:|---:|---:|
| `test_file_operations.sys` | 2 | 13 | 11 | 453 |
| `test_integer_overflow.sys` | 2 | 16 | 14 | 538 |
| `test_physical_memory.sys` | 4 | 22 | 18 | 420 |
| `test_port_io.sys` | 1 | 10 | 9 | 42 |
| `test_wrmsr.sys` | 1 | 11 | 10 | 47 |
| `test_rdmsr.sys` | 1 | 11 | 10 | 43 |
| `test_shellcode.sys` | 1 | 9 | 8 | 102 |
| `test_stack_overflow.sys` | 1 | 10 | 9 | 121 |
| `test_process_termination.sys` | 1 | 20 | 19 | 556 |
| **Total per authority/repetition** | **14** | **122** | **108** | **2,322** |

Three detector labels at the physical-memory fixture's `memcpy` site are
separate finding rows but one machine-code site. Consequently the artifact's
denominator is explicitly 14 rows, not 14 distinct vulnerabilities.

## Identities and protocol

- Axeyum measurement checkout:
  `f330ac57fde8a2be7ffac86e6821720b3503229b`, tracked clean before and after.
- Glaurung corrected A0 branch:
  `b79f26959378f9b8ea51eee6f1b3809a4a234c84`, tracked clean before and after.
- IOCTLance source/binaries:
  `905629a773f191108273a55924accd9f31145a8d`; the repository had unrelated
  edits outside `test_drivers`, while all 18 manifest paths were tracked and
  clean.
- Z3-authority Glaurung binary SHA-256:
  `7221037f57bd9a650ad9e8fc9da0b7a2fbfb07024d97c17ce16c11c72b2017aa`.
- Axeyum-authority Glaurung binary SHA-256:
  `1436e483d67d80e523cae920e16d7958486fb30ca7523c40a340de157b6bf240`.
- Fixed work: complete reachable coverage, `max-analyzed-functions=100`,
  50,000-solve/60-second analysis bounds, 250 ms per check, two repetitions.
- Acceptance population: producer `high-confidence`, followed by the separate
  exact source-manifest join.

The manifest records each exact finding row, source line range, source hash,
binary hash, IOCTL, and corresponding instruction/call site. Direct
disassembly confirms the expected sinks: `wrmsr`, `rdmsr`, `out dx,al`, an
attacker-derived indirect call, unchecked multiplications, unbounded copies,
privileged physical mapping, process termination, and file operations.

## Reproduction

From the clean Axeyum measurement checkout, with authority-specific Glaurung
binaries built from the named corrected revision:

```sh
python3 scripts/measure-glaurung-authoritative-findings.py \
  --glaurung-repo /tmp/glaurung-concretization-a0.NEo0bV \
  --z3-binary /tmp/glaurung-system-buffer-z3-ioctlance \
  --axeyum-binary /tmp/glaurung-system-buffer-axeyum-ioctlance \
  --driver /nas4/data/workspace-infosec/ioctlance/test_drivers/test_file_operations.sys \
  --driver /nas4/data/workspace-infosec/ioctlance/test_drivers/test_integer_overflow.sys \
  --driver /nas4/data/workspace-infosec/ioctlance/test_drivers/test_physical_memory.sys \
  --driver /nas4/data/workspace-infosec/ioctlance/test_drivers/test_port_io.sys \
  --driver /nas4/data/workspace-infosec/ioctlance/test_drivers/test_wrmsr.sys \
  --driver /nas4/data/workspace-infosec/ioctlance/test_drivers/test_rdmsr.sys \
  --driver /nas4/data/workspace-infosec/ioctlance/test_drivers/test_shellcode.sys \
  --driver /nas4/data/workspace-infosec/ioctlance/test_drivers/test_stack_overflow.sys \
  --driver /nas4/data/workspace-infosec/ioctlance/test_drivers/test_process_termination.sys \
  --repetitions 2 --deadline-secs 60 --max-analyzed-functions 100 \
  --solve-budget 50000 --solve-secs 60 --process-timeout-secs 120 \
  --check-timeout-ms 250 --acceptance-population high-confidence \
  --out authority-report.json

python3 scripts/validate-glaurung-finding-population.py \
  --manifest corpus/glaurung-finding-populations/source-backed-positive-v1.json \
  --authority-report authority-report.json \
  --source-repository /nas4/data/workspace-infosec/ioctlance \
  --out validated-population.json
```

Committed artifact hashes:

- `authority-report.json`:
  `a54333ba303517ea3cd6657572837fac69136439bb53d937fc76b907a7469a34`;
- `validated-population.json`:
  `d068d3c2de89a1dbd29053caa3c137146e387be58d6d576f948178856be8b137`.

## Interpretation boundary

This closes the missing nonzero **positive-control** denominator and gives a
future concretization-policy sweep a mandatory 14/14 regression gate. These
fixtures intentionally place direct planted sinks behind shallow dispatch, so
they do not demonstrate that any concretization policy improves discovery.
Policy-dependent real-driver output must remain a separately reported
unlabeled discovery population until source/machine validation supplies ground
truth. Symbolic memory remains conditional on a validated residual gap after
the cheap configuration sweep.
