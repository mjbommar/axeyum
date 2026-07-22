# SMT-COMP official selection S4 final result

Status: complete
Date: 2026-07-22
Decision: [accepted ADR-0356](../research/09-decisions/adr-0356-preregister-official-smtcomp-selection-identity.md)

## Bounded result

The SMT-COMP 2026 Single Query selection now has one independently audited,
content-addressed identity. This closes selection policy and corpus-byte
identity only. It executes no solver and grants no decide-rate,
representativeness, or competition-result credit.

Accepted root:

```text
/nas3/data/axeyum/harness/official-selection-2026-sq/accepted-322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698
```

The self-hashed completion record reports schema
`axeyum-smtcomp-official-selection-v1`, payload SHA-256
`abdb0886cdc5afd4e3efdfdded16eb045f91f85859927721500c3652bcb89920`,
450,472 metadata rows, and 45,905 selected files. The accepted-directory name
is the SHA-256 of canonical `complete.json`.

## Complete partition

| Terminal reason | Rows |
|---|---:|
| `selected-new` | 2,709 |
| `selected-old` | 43,196 |
| `excluded-cap-new` | 736 |
| `excluded-cap-old` | 206,719 |
| `excluded-trivial` | 197,112 |
| **Total** | **450,472** |

The selected files contain 15,148,369,947 bytes. `official-selected.txt` is
4,066,816 bytes with SHA-256
`49744be7b373b2baef41289bfd5d2a7e59619db2859233e892b0592cd34a8b5b`,
identical to both pinned S3 producer outputs. `selected-files.jsonl` is
11,096,728 bytes with SHA-256
`540fe29f2bc28e858b103fcd806eab709f58ed69b67d8cb95bd41bcdbaa87f39`.

The complete decision ledger is 324,460,399 bytes with SHA-256
`0f44fff7d550a3aac19e1d3c86e8628db9ac3a6c85bd9dc54affc50ff9f4aaf9`.
The joined corpus and historical ledgers are 161,831,759 and 165,323,763
bytes, respectively. Their exact digests, plus every remaining required
artifact digest, are bound by `complete.json`.

## Independent audit

The standard-library auditor imported neither organizer code nor Polars. It:

- streamed the path-sorted S1 eligibility and S2 corpus ledgers in lockstep;
- joined S3 membership and reconstructed all terminal reasons;
- recomputed competitive-logic membership, historical eligibility, caps, and
  new-before-old quotas;
- checked the explicit zero-match removal set and the two-row all-trivial
  `QF_UFFP` boundary;
- physically hashed all 45,905 selected files before publication;
- passed all 18 registered invariants and rejected all 18 mutations; and
- published the accepted root only after completion-last validation.

A second fresh process then reconstructed the complete
corpus/history/decision join and physically rehashed all selected files again:

```sh
./scripts/audit-smtcomp-official-selection.py \
  --verify-root /nas3/data/axeyum/harness/official-selection-2026-sq/accepted-322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698 \
  --corpus-acquisition /nas3/data/axeyum/harness/official-selection-2026-sq/corpus-acquisition-1784745749642951377-d48fb0dc
```

It terminated with:

```text
SMTCOMP_FINAL_SELECTION_VERIFY_OK|metadata=450472|selected=45905|mutations=18|complete_sha256=322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698
```

The artifact records implementation commit
`5f8864bc2b936f5be685a69b86d7fadaa4bb3d49`. A later rebase changed the topic
commit identity without changing this live-used implementation; the exact
recorded object is therefore preserved on remote branch
`agent/smtcomp/s4-audit-5f8864bc`.

## Next boundary

S5 is a small harness-admission increment: bind E1b preflight to this exact
completion record, selected list, and selected-file ledger, then prove the
contract with a tiny fixture. It is not required before unrelated solver
capability work and does not authorize a full-population run by itself.
