# SMT-COMP repaired P0 v2 Bitwuzla closure result

Status: complete; process-free closure executed and independently validated
Date: 2026-07-23
Plan: [post-run closure plan](smtcomp-repaired-p0-v2-bitwuzla-post-run-closure-plan-2026-07-23.md)
Predecessor: [Bitwuzla recovery plan](smtcomp-repaired-p0-v2-bitwuzla-recovery-plan-2026-07-23.md)

## Result

The repaired-P0 Bitwuzla cell is complete. Its sole preregistered retry had
already produced all 435 shard-1 results; the integrated closure repaired only
the post-run evidence layout and finalization boundary. No solver, runner, host
allocation, or second retry was launched.

The final cell contains 1,305 immutable records:

| Result | Count |
|---|---:|
| `sat` | 432 |
| `unsat` | 789 |
| no verdict | 84 |
| completed process | 1,221 |
| wall timeout | 84 |
| known-status contradiction | 0 |
| Axeyum/cvc5 cross-solver disagreement | 0 |

The adjudication is `safe_to_continue=true`. This closes the three repaired P0
cells under their frozen population/resource identities; it does not authorize
a larger run or an official SMT-COMP equivalence claim.

## Integrated authority and command

The integrator landed the plan, implementation, and checkpoint docs through
`origin/main=2855ddf7`. The exact source-admission check passed for the closure
plan, recovery plan, coordinator, multi-host adapter, resource adapter, and
unchanged strict filesystem loader. Both prior external cell results validated
before mutation:

| Cell | External result record SHA-256 | Safe |
|---|---|---|
| Axeyum | `97f27a480f9694e97765d669823b05c34ced8825f2f598c16e00ea301b1c4a57` | true |
| cvc5 | `e6fbc654535c82bb5d9fa9460ba802cf41d128c28778b859f990df2160a37faf` | true |

The only live command was:

```sh
python3 scripts/execute-smtcomp-repaired-p0-cell.py \
  --preparation-root /nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-75e544a8-v2 \
  --cell bitwuzla \
  --acknowledge-complete-sha256 8d9145b2673ee10bf7c38990c20301f13323cfe4ab02c9946b403d0d2e4f4261 \
  --close-post-run-validation-failure retry-1
```

It returned the sealed 1,305-row safe adjudication and exit code zero.

## Preserved lifecycle evidence

The closure does not relabel either failed retry terminal:

- outer allocation terminal remains `failed`, exit code 2, record SHA-256
  `e39ac72199dab6f126cf1f39a68bc05cd225cd80e8882fbde8c061e5ef14ad63`;
- retry resource terminal remains `failed`, worker exit `[2]`, record SHA-256
  `fac2532e80a99ab7a72cd3a663332466eff4bbd99eab2a89220066fa0e4b8a48`;
- successful inner shard terminal remains `completed`, 435/435, result-set
  SHA-256
  `78b7772ca17b9fc7b0961669591f4c5802271e7f0135782656676c768f853e9d`;
  and
- exactly one retry allocation attempt and one retry allocation terminal exist.

The original zero-record diagnostic terminal is absent from its invalid
`terminals/1/` location and retained byte-exact under quarantine. Its SHA-256
remains
`092579dd324cbbf17cebd4c5a49b0e25dcf850b0b8c85e2912bf7fdfece1ac26`.
There are zero live shard leases. The registered retry service is
inactive/dead with `MainPID=0` on `s5`, `s6`, and `s7` after closure.

## Final artifact identities

Run-root artifacts:

| Artifact | File SHA-256 | Record SHA-256 |
|---|---|---|
| Post-run closure | `75fdd87991b8194fde282c32b67f23959caf4e21eb339373a953bfc402a2e1e0` | `c39c2446b419a1eeb147cb409eb4325c4787c8d2bb540521b95e6390ab96cc48` |
| Resource completion | `ea31d45fe2e5ae602e7ad77442263985be08ef24d26ab3579d6dd2904f478513` | `b1469b1aeaecbba83a8993e62874af9171c229d9b1366378d5bf620ae98fd788` |
| Multi-host v2 completion | `01c005562b619b6f4eff0fae93bba2afc8c970c761e5e15342091f6cfa706400` | `9480613d0376608e307fee6b5c02e26d3dd9a0992ca44d3897303964a4ec9fb5` |

External cell-result artifacts:

| Artifact | File SHA-256 | Record SHA-256 / count |
|---|---|---|
| Adjudication | `6e00e522e1dea7c8252e201f00ba0aa4b47cac9dd5fbe0e4961f34afce2894f4` | `66290ded8d19a20a5bb5d0f7fcfe12c566c25d18723731e7db6c88d28de8b1d5` |
| Raw results | `390e113f1d6291402e2ae6a59a09e174cfb2d978727a01432b7f6a016b265dd4` | 1,305 rows |
| Completion | `4e0c9682931154b6455d02e00ed5a6cc3ec6b58635e7c808de703023c72dcf20` | `7ec879514032b00ed5d8fffd119d126df90681a6b0ed4e2bf9ea737ae94df6f3` |

The fully validated canonical scoring bundle SHA-256 is
`93e62151c9ef8798a9a84bbea80f772b9092b751eff686ae1dfbe249b87cee95`,
identical to the preregistered post-run projection. The complete record-set
SHA-256 remains
`ae55b2d0061ffeb615c2e852d5d16f9e886df780de2e53c79808d5578db3a78f`.

## Independent validation and replay

A fresh process independently performed all of the following after closure:

- preparation and both prior external cell-result validation;
- strict generic bundle load, all 1,305 record contracts, and output-sidecar
  verification;
- canonical merge and exact canonical hash comparison;
- all four E2 resource-session records plus resource completion;
- E3 plan, commands, attempts, terminals, clean-release recovery, post-run
  closure, v2 multi-host completion, and completion timestamp validation;
- external adjudication, raw-result, and completion-last validation; and
- a second `finalize_multi_host_run` that returned the identical completion.

The explicit closure command was then run a second time. Before and after the
replay, the sorted path/size/content inventory over the Bitwuzla run root and
external cell-result root contained exactly 1,359 files and had SHA-256
`24dc225e63646dec153be0181e9dfe3aadd9696721d7417c1e84e6738ed82724`.
The replay therefore launched no process and changed no artifact bytes.

Implementation gates on `0eff5d64` were:

```text
focused: 31 tests, OK
portable: 75 tests, OK, one live-host skip
mandatory cgroup: 75 tests, OK, one live-host skip
mandatory live E3: 75 tests, OK, no skips
live evidence: /nas3/data/axeyum/harness/e3-gate/live-1784841036231463027-0eff5d64cc60
control completion: 514f316102fa4f64cfc90af7e62336a1b0bb774521b6a7a1fa7e7d3172f5a756
loss completion: 1b665db7f48adf973c4fe28097a5b0242bd42a64d2f1d3728d2d4165516c7994
links: passed
foundational resources: passed
git diff --check: passed
```

## Credit and next action

This result grants bounded repaired-P0 evidence credit to the exact Bitwuzla
cell. It preserves both harness incidents as lifecycle evidence and does not
reinterpret an outer finalizer failure as an ordinary successful process.

Next: integrate this result document, then derive and publish the combined
three-cell repaired-P0 comparison from the three external result roots. Any
larger credited population requires a new preregistered execution identity and
resource plan.
