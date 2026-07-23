# TL0.6.3 M0 R3 official Lean execution result

Status: **accepted bounded local result; zero Lean parity credit**

Date: 2026-07-22

Authority:
[`lean-u2-official-execution-tl0.6.3-m0-r3-v1.json`](lean-u2-official-execution-tl0.6.3-m0-r3-v1.json)
and generated
[`JSON`](generated/lean-u2-official-execution-tl0.6.3-m0-r3.json) /
[`Markdown`](generated/lean-u2-official-execution-tl0.6.3-m0-r3.md).

## Result

The sole preregistered R3 process, attempt 004, executed the pinned official
Lean 4.30.0 `compile/534.lean` CTest case once and passed. It used the released
toolchain's bundled compiler/linker path, produced the expected output, retained
the generated C and executable, reaped the process group, and installed the
completion record last. The frozen evidence validates offline without starting
CTest.

The complete retained M0 history is:

| Attempt | Process state | Official outcome | Interpretation |
|---|---|---|---|
| 001 | incomplete | none | Lean failed to create a worker thread before a case completion existed. |
| 002 | complete | failed | Generated C compiled, but the adapter's forced system `cc` could not link the released toolchain's static C++ libraries. |
| 003 | failed before runner import | none | Direct-file Python execution exposed the script directory, not the repository root, on `sys.path`; no work/evidence root or CTest process existed. |
| 004 | complete | passed | The direct-entry-corrected runner used the released bundled compiler/linker and completed the same singleton case. |

That is four process attempts, two incomplete attempts, two official outcomes,
one pass, one failure, and **one unique official case** observed from the
3,678-case release-tag Linux-release parent. There are zero completed parent
profiles, official-provider reproductions, Axeyum outcomes, semantic pairs,
performance rows, complete axes, satisfied gates, or parity credit.

## Evidence closure

Attempt 004 retains 24 files / 8,953,979 bytes under
[`evidence/lean-u2-official-execution-tl0.6.3-m0-r3/`](evidence/lean-u2-official-execution-tl0.6.3-m0-r3/).
The authority binds:

- evidence manifest
  `982c0481784bf487995d76b6caf5c27e24d7c170115a114dccfa53d054327c78`;
- terminal record
  `f3d04115b62a582122fb3fa5dee1f9818cf5e44791e928475bcd2a10a4874607`;
- JUnit record
  `1cb384c6b4fd9655e79387a2d1aaa7845535fd621b2922f8a3ecf2c6a66dde0d`;
- case record
  `64fbf989ec5e458f6e8b69bad71c4c6532cd73e4be70baa998ffae4f702289eb`;
- completion record
  `a997934b49ef1fbb2be6322b49279dc3f183c22c2436e6fe05e211f722dcd240`;
  and
- amended result authority
  `0a82746dc3a8fd8e138f0bd9ecdc2064ba856feccb10a840fcd72ca8ad7674db`.

The separate offline result adapter was required because the frozen execution
runner's post-execution validator rejected the two correctly positive bounded
claims, `official_lean_case_observed` and `local_shard_complete`. The
[`result-projection amendment`](lean-u2-official-execution-tl0.6.3-m0-r3-result-amendment-2026-07-22.md)
preregistered that repair after execution and forbade a process rerun. The
adapter has no execution command and requires every terminal-scope claim to
remain false.

The attempt-003 root cause matches Python's documented launch behavior: direct
file execution prepends the script directory, whereas `-m` prepends the current
directory to `sys.path` ([Python command-line
documentation](https://docs.python.org/3/using/cmdline.html),
[`sys.path` initialization](https://docs.python.org/3/library/sys_path_init.html)).
R3 therefore tests the actual direct entry point instead of relying on module
execution to mask the packaging defect.

## Non-claims and next boundary

The pass validates one local official case and the evidence path used to retain
it. It does not validate the other 3,677 cases in the parent selection, any
other official workflow cell or provider, or any native Axeyum behavior.

The next U2 increment must derive fresh child shards from the registered parent
profiles, execute them without retrying this singleton, classify each selected
case by its required native surface, and form matched official/Axeyum records.
Only complete case records count; process retries for the same case do not
increase unique population coverage.
