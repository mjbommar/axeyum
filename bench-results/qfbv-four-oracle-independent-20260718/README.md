# ADR-0237 first full attempt (rejected)

This directory preserves the fail-closed first attempt at ADR-0237's unchanged
`uniform-a` range. It is **not** an accepted success artifact.

- Axeyum commit: `2aaa97d3`
- Generator/profile: `uniform-v1`
- Seeds: 1,000,000..1,004,000
- Inherited Axeyum worker cap: 5,000 ms
- Result: 3,999/4,000 Axeyum/Z3/cvc5/Bitwuzla agreements, one Axeyum worker
  timeout, no disagreement, crash, oracle unknown, or SAT replay gap
- The runner stopped before `uniform-b` and `edge-c` and wrote no JSON report.
- Exact timeout seed: 1,002,261, identified by an unchanged-formula focused
  rerun after adding nondecision telemetry. It reproduces at 5,000 ms and
  decides at the amended 30,000 ms cap.

`environment.txt` records exact oracle executable hashes and toolchain
versions. `uniform-a.log` is the unedited failed process log. ADR-0237 preserves
this attempt and preregisters an explicit 30,000 ms rerun without changing any
formula or seed.

