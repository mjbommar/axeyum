# SMT-COMP 2026 Single Query official producer (S3)

**Status:** complete

**Implementation commit:** `38c5f2afb88e1ea130699fe23440f9bfdfe86b5e`

**Selection observed:** yes

The completed twice-repeated official production is retained at:

```text
/nas3/data/axeyum/harness/official-selection-2026-sq/official-producer-1784755629430228923-38c5f2af
```

This is the first stage that observed selected membership. It ran only after
the producer, mutation tests, runtime identities, and repetition contract were
committed and pushed. Both fresh environments copied and rehashed the exact
88-file organizer bundle, created independent caches, and invoked the pinned
organizer selection code.

## Exact result

| Fact | Value |
|---|---:|
| Authority SHA-256 | `0fd1f479e809e0d8f740aa72cff193871b35f45c95a2eb9d96440ca7508b3d1a` |
| S1 completion SHA-256 | `f1ffba1da0a76df655b85252d5f3d784d9c84297023048ca393258c12b4ecf6d` |
| S2 completion SHA-256 | `a086b77cce4d43db05a0bd6ef6b7752f207b141b82ef9c9c7825ca069df3faf5` |
| Bundle files per run | 88 |
| Locked runtime packages | 14 |
| Producer repetitions | 2 |
| Selected total | 45,905 |
| Selected new / old | 2,709 / 43,196 |
| Logics with selected rows | 88 |
| Selected-list bytes | 4,066,816 |
| Repetition equality | exact selected and per-logic bytes |

`QF_UFFP` is the sole one of the 89 corpus logics without a selected row. S4
must prove this follows the competitive-logic gate rather than silently omit
it.

## Runtime and cache identity

Both runs used CPython 3.11.15, uv 0.11.1, Polars 1.39.2, seed `22,731,074`,
`PYTHONHASHSEED=0`, and `POLARS_MAX_THREADS=1`. The exact decorator-free
`create_cache` AST SHA-256 was
`ca792a127fb4f5d0c40bd5055b370a3cfb27bb28bdf2c5d4724d5e69d2009617`.
Each run independently produced the same three cache identities:

| Cache | Bytes | SHA-256 |
|---|---:|---|
| `benchmarks-non-incremental-2026.feather` | 56,310,831 | `e4bad162b9f65df252bbbdce6a2d7f1e913d56fdf52b081b71fa9d10d26c7540` |
| `benchmarks-incremental-2026.feather` | 4,744,223 | `9b4dac90b453c548e6a66c939408396f1bb8c7b9c09a54e5e00891f4ce7ea73e` |
| `previous-sq-results-2026.feather` | 560,593,875 | `e71372b0e0cdb0ed0db29daf28eaa6ab1ed816c936c5963780b917dea08880b6` |

uv warned that the two Polars 1.39.2 distributions are yanked with reason
`no lockfile`. The organizer lock explicitly pins this version; installation
therefore remained fail-closed on its recorded artifact hashes rather than
substituting another release.

## Artifact roots

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| `official-selected.txt` | 4,066,816 | `49744be7b373b2baef41289bfd5d2a7e59619db2859233e892b0592cd34a8b5b` |
| `per-logic.json` | 4,697 | `179e25ea89a82096c466ad5523bdaa2b71d1a6b7e82564246076b1bfae201b40` |
| `producer.json` | 20,757 | `ced4688fbcf853e5a629c6c718826d0f176cc96052757e7486735c2693803489` |
| `requirements.lock` | 12,436 | `37fce7549f9fecc32fed53e5dc39218392762d6b5bbfa6d1751f780a5f7d42fc` |
| `producer-audit.json` | 641 | `0af31cf06e2074a8a6480a0b987683d9b5cb1902f625d7b6c26758cf68b4d6cf` |

The completion payload hash is
`3945e0fdc80bd2ff0da18d7fde26c7d9ad0a6db071b768fbcc6fde2ccb26c2c2`.
A fresh standard-library process rehashed both complete bundle manifests and
their 176 source/data files, all six caches, both environment freezes, every
command log, both worker artifact sets, the normalized selected list,
per-logic totals, and the completion dependencies. It terminated with:

```text
S3_FRESH_AUDIT_OK|bundles=2|bundle_files=88|packages=14|selected=45905|new=2709|old=43196|logics=88|repetitions_equal=true|selection_observed=true
```

## Next boundary

S4 must remain independent of organizer imports and Polars. It must join the
official selected paths to the completed S1 eligibility ledger and S2 corpus
ledger, emit one terminal decision for every one of the 450,472 metadata rows,
hash every selected file, balance every per-logic cap/new/old count, exercise
the registered rejecting mutations, and publish completion last. No solver may
consume the selection before that audit closes.
