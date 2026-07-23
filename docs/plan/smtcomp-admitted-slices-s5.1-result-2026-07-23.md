# SMT-COMP admitted slices S5.1 result

Status: complete
Date: 2026-07-23
Plan: [S5.1 admitted-slice plan](smtcomp-admitted-slices-s5.1-plan-2026-07-23.md)
Implementation: `9f544cdb`

## Bounded result

The accepted v2 selection-input ledger now admits any nonempty, strictly
ordered subset of the official selected population. Construction and preflight
still stream and validate the complete 45,905-row official list and selected-
file ledger; only requested physical files are rehashed and emitted as
execution rows.

This closes the identity mechanism needed by bounded P0 slices. It changes no
solver, scoring, sharding, checkpoint, or resource semantics and launched no
solver.

## Tiny executable gate

The existing two-file official-selection fixture now also executes a one-file
admitted subset. Its manifest retains the complete two-row official population
identity but emits one execution row with sequence zero.

All five S5.1 mutations reject before a run directory exists:

- an execution ID absent from the official selection;
- official IDs requested out of official-list order;
- a duplicate requested ID;
- an inconsistent complete-ledger row outside the requested subset; and
- changed requested physical bytes.

The original positive full-population fixture and S5-M01 through S5-M09 remain
green.

## Exact combined P0 ledger

One no-solver pass constructed the combined complete
`QF_FP`/`QF_BVFP`/`QF_ABVFP`/`QF_AUFLIA` slice from the accepted S4 root:

| Item | Value |
|---|---:|
| Requested files | 1,810 |
| Requested physical bytes rehashed | 36,995,297 |
| Complete official list rows validated | 45,905 |
| Complete selected-file ledger rows validated | 45,905 |
| Absolute slice-list bytes | 358,776 |
| Absolute slice-list SHA-256 | `e6da1f475ef2674a8461697babaa4e86bce9f3da9d3e7f9b03f0fbf146572e3d` |
| v2 slice-ledger bytes | 762,981 |
| v2 slice-ledger SHA-256 | `a8cb9ba090b22e658e06dc53b4c97e1cdce595117acc1cbdc7f8476e9e85f4f4` |

The manifest continues to bind completion SHA-256
`322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698`,
official-list SHA-256
`49744be7b373b2baef41289bfd5d2a7e59619db2859233e892b0592cd34a8b5b`,
and complete selected-file-ledger SHA-256
`540fe29f2bc28e858b103fcd806eab709f58ed69b67d8cb95bd41bcdbaa87f39`.

The combined execution order starts in `QF_ABVFP` at
`20170428-Liew-KLEE/aachen_real_diction_style.x86_64/query.06.smt2` and ends in
`QF_FP` at `schanda/spark/user_rule_1.smt2`, exactly following official-list
order rather than caller-chosen logic order.

## Full-population non-regression

After the subset implementation landed, a second complete physical pass
rehashed all 45,905 files and 15,148,369,947 bytes. Its 19,266,433-byte v2
manifest compared byte-for-byte equal to the original S5 manifest and retained
SHA-256
`8e68f29c63f11867304d5fe03eb5a2c47e0cfd15ffdcb0b5b3878dd056734791`.

This proves the subset implementation is a strict generalization of S5 rather
than a new or weaker full-population identity.

## Repository gates

```text
python3 -m unittest scripts.tests.test_smtcomp_resume_runner
  11 tests, OK

./scripts/check-smtcomp-resume.sh
  57 tests, OK, 1 host-dependent skip

Python compilation
  passed

git diff --check
  passed
```

The retained foundational-resource and documentation-link gates are rerun in
the final documentation checkpoint.

## Next boundary

Preregister the actual P0 execution before launching anything. That plan must
freeze the staged Axeyum binary and oracle identities, the exact four slice
manifests, limits, E2/E3 host/shard/resource identities, expected-status and
disagreement adjudication, and a `DISAGREE=0` exit gate. S5.1 alone authorizes
no execution.
