# SMT-COMP harness admission S5 result

Status: complete
Date: 2026-07-23
Plan: [S5 harness-admission plan](smtcomp-harness-admission-s5-2026-07-23.md)
Decision: [accepted ADR-0356](../research/09-decisions/adr-0356-preregister-official-smtcomp-selection-identity.md)
Implementation: `db6fb545`

## Bounded result

E1b preflight now has an admitted selection-input schema that binds one
content-addressed S4 completion, its exact official selected list, its exact
selected-file ledger, and the physical execution files. Cgroup-backed E2/E3
preflight rejects the legacy v1 manifest unless the caller supplies the
explicitly named no-credit fixture override.

This closes only the S4-to-E1b identity handoff. No solver was launched, no
scoring artifact was produced, and no P0 or full-population measurement is
credited.

## Tiny executable gate

The two-file E1b fixture constructs a content-addressed completion and v2
execution ledger, completes one resumable run, and records two benchmark rows.
The preregistered mutations `S5-M01` through `S5-M09` all reject before a run
directory is created:

- completion schema/status/observation, payload, and directory identity drift;
- selected-list and selected-file-ledger artifact drift;
- selected-list order/identity drift;
- ledger row/byte identity drift;
- physical benchmark drift; and
- cgroup-backed use of only the legacy unadmitted fixture manifest.

The existing E1--E3 fixtures retain their execution semantics through an
explicit `--allow-unadmitted-selection-fixture` test-only path. That path does
not satisfy S5 admission.

## Accepted-population pass

One read-only pass consumed the immutable accepted root:

```text
/nas3/data/axeyum/harness/official-selection-2026-sq/accepted-322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698
```

It joined the official IDs to the physical S2 corpus, validated all 45,905
canonical ledger rows, and rehashed all 15,148,369,947 selected bytes. The
resulting identities are:

| Artifact or field | Bytes / rows | SHA-256 |
|---|---:|---|
| S4 `complete.json` | — | `322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698` |
| completion payload | — | `abdb0886cdc5afd4e3efdfdded16eb045f91f85859927721500c3652bcb89920` |
| `official-selected.txt` | 4,066,816 bytes | `49744be7b373b2baef41289bfd5d2a7e59619db2859233e892b0592cd34a8b5b` |
| `selected-files.jsonl` | 11,096,728 bytes / 45,905 rows | `540fe29f2bc28e858b103fcd806eab709f58ed69b67d8cb95bd41bcdbaa87f39` |
| absolute execution list | 9,024,556 bytes / 45,905 rows | `9d5f51d5b84c65f6c2ab03db822b185f60e47a505ec93284363dbd229305ac2b` |
| v2 execution ledger | 19,266,433 bytes / 45,905 rows | `8e68f29c63f11867304d5fe03eb5a2c47e0cfd15ffdcb0b5b3878dd056734791` |

The first execution ID is
`ABV/20190429-UltimateAutomizerSvcomp2019/alternating_list_true-unreach-call_true-valid-memsafety.i_4.smt2`;
the last is `UFNIRA/20240414-funcprobs/prove/problem_U93.smt2`. Their physical
size and SHA-256 values match the bound selected-file rows.

## Gates

The implementation passed:

```text
python3 -m unittest scripts.tests.test_smtcomp_resume_runner
  9 tests, OK

python3 -m unittest \
  scripts.tests.test_smtcomp_cgroup_host \
  scripts.tests.test_smtcomp_multi_host \
  scripts.tests.test_smtcomp_multi_host_live
  10 tests, OK, 1 host-dependent skip

./scripts/check-smtcomp-resume.sh
  55 tests, OK, 1 host-dependent skip

just foundational-resources
  137 concepts and 174 example packs validated

./scripts/check-links.sh
  all links ok
```

Python compilation and `git diff --check` also pass. The host-dependent live
cgroup test remains covered by the previously accepted E2/E3 gate; S5 changes
only admission and does not claim a fresh live resource-enforcement run.

## Next boundary

Fresh repaired QF_FP/QF_BVFP/QF_ABVFP and QF_AUFLIA P0 slices are next. They
must use this admitted identity, retain the existing E1--E3 evidence contract,
and return `DISAGREE=0` before any credited full-population run.
