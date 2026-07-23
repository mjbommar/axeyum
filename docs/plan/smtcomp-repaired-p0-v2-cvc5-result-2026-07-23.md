# SMT-COMP repaired P0 v2 cvc5 result

Status: live cvc5 cell complete and independently validated; Bitwuzla blocked
until these exact result and admission-source bytes are integrated on
`origin/main`
Date: 2026-07-23
Predecessor: [Axeyum closure result](smtcomp-repaired-p0-v2-axeyum-closure-result-2026-07-23.md)
Preparation: [P0-S1 v2 result](smtcomp-repaired-p0-preparation-s1-result-2026-07-23.md)

## Admission and execution

The integrator landed the Axeyum closure checkpoint at merge `39691255`. The
cvc5 coordinator admitted the cell only after fetching `origin/main`, checking
the exact preparation/closure/result/source bytes, and independently validating
the prior Axeyum external completion. It launched exactly the three frozen
initial allocations:

- `initial-0` on `s5`, shard 0;
- `initial-1` on `s6`, shard 1; and
- `initial-2` on `s7`, shard 2.

All allocations used the frozen cvc5 binary, one core, an 8 GiB memory cap, the
20-second per-benchmark wall limit, and the registered environment. No retry
generation ran. Bitwuzla retained zero runtime evidence throughout.

## Result

All 1,810 selected benchmarks have one immutable result record. All three
shards, resource enforcement, and multi-host execution closed normally. The
coordinator published adjudication, raw export, and completion-last cell result
under `cell-results/cvc5/`; no coordinator-owned artifact exists in the strict
generic run root.

| Outcome | Count |
|---|---:|
| `sat` | 672 |
| `unsat` | 841 |
| no verdict | 297 |
| completed process | 1,513 |
| wall timeout | 181 |
| nonzero exit | 116 |
| known-status contradiction | 0 |
| Axeyum/cvc5 disagreement | 0 |

The adjudication is `safe_to_continue=true`. Timeout and nonzero-exit rows are
retained as typed no-verdict evidence; they were not filtered or retried.

## Bound identity

| Item | Value |
|---|---|
| Preparation completion SHA-256 | `8d9145b2673ee10bf7c38990c20301f13323cfe4ab02c9946b403d0d2e4f4261` |
| Preparation record SHA-256 | `d3ae8e7cd870c48c19417495aeb99b53ed1a797db58092b79d0828b9255b5f7b` |
| cvc5 run identity SHA-256 | `1d32c45c1371528cf3d4e6bad5801600490f09151ede779bd348de2f124e7745` |
| Canonical bundle SHA-256 | `4d791ab4a1d35113a1e6126fc954c0ef7f6d76813fcad284f9c61b055122685b` |
| Resource completion file SHA-256 | `a1a656aadd6d47d37f2e7ef83d10272469ffcada4e6f761b38b80a620fcb8aaa` |
| Resource completion record SHA-256 | `517f252a83817f75219467aa7679af15c5fece2e8a87328d9158fb33bb7f122a` |
| Multi-host completion file SHA-256 | `759aa8a384b34a31339bf2230a618c46272dc6fb99201249d4518c0d583d4ecc` |
| Multi-host completion record SHA-256 | `822fcd19b2f05c5d0b89f2ffec00e40cb4f442a5b0e851aa70a747f85bb123c6` |
| Adjudication file SHA-256 | `b4cc8aa560536b1e1cc6f4e455ceed34cd8e865288ebe84b65aabdf489abfd3f` |
| Adjudication record SHA-256 | `fe2fe0c1c92fc97d247c85d9c52b4db792b86c7c43b231eea6c91ba1edc57a57` |
| Raw export SHA-256 | `0465d0aea6929bdf42c37f5aaa7e3ba24eca67f960a322ad6c8735a8f0d9e010` |
| Raw export rows | 1,810 |
| External completion file SHA-256 | `4abde0a6b3d02be1a4e4aa80bda32e2808e78e32db3e1e71336bc6e304bd32f8` |
| External completion record SHA-256 | `e6fbc654535c82bb5d9fa9460ba802cf41d128c28778b859f990df2160a37faf` |

Shard completion identities are:

| Shard | Records | Completion file SHA-256 | Result-set SHA-256 |
|---:|---:|---|---|
| 0 | 604 | `050e8e1bd574ef2e871c37e162d110d2409ee43457b9afd79b1d7e601717f56c` | `6c8862a8f4b14453afd17917a2ad32199d7b6da8eddb565e3d599fe6370b0fb4` |
| 1 | 603 | `5549ad19c6768ed542456b02e99d42d6d111f07db3ca4ef2f75c16a80b23a9e6` | `656df36227cab7aa5945e33723aa50202c36b3de292356c80fefa413c95f7095` |
| 2 | 603 | `7f67e988cee0667a757240324c385d0e872c97ac033943826847849d9b7a294c` | `d52ad9dcf95bb95fc6328624281590d57f2d86c3be65b0003fb3539ea3704937` |

Allocation-terminal file SHA-256 values are:

- `initial-0`: `92089aa877c1d57de71e715b015f074423b618eb4edf4813ddf6090169e96543`;
- `initial-1`: `174a976b856c40cb1c0ac987d151adb34cc6b9e5289877dd763119dcc6095817`;
- `initial-2`: `1a1899b90abca5544848ac0c5e646fe0152a6ee5c6106dadb4403f5783358d9c`.

## Independent validation and next boundary

A fresh validator pass reproduced the generic canonical bundle, recomputed the
adjudication and raw export, validated the external completion, counted exactly
1,810 records, and found zero known-status mismatch. No cvc5/coordinator process
remained on `s5`, `s6`, or `s7`; Bitwuzla still had zero runtime evidence.

The cvc5 cell is complete, but Bitwuzla remains blocked while this document and
its admission-source check exist only on the topic branch. The coordinator now
requires this exact result, the Axeyum result, the closure plan, and its own
source bytes to be byte-identical to `origin/main` before Bitwuzla can launch.
After integration, revalidate both prior external completions and launch only
the frozen Bitwuzla initial allocations.
