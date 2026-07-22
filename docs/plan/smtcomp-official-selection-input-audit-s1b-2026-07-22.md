# SMT-COMP 2026 Single Query input audit (S1b)

**Status:** complete  
**Implementation commit:** `5051dfbc4aa1c72096d39ecf69765d5ea08324fb`  
**Selection observed:** no

The completed selection-free audit is retained at:

```text
/nas3/data/axeyum/harness/official-selection-2026-sq/input-audit-1784744992636593932-5051dfbc
```

It independently downloaded and rehashed all 89 registered inputs, normalized
the official submission and metadata formats without importing organizer code
or Polars, reduced the 2018--2024 historical results, and emitted a canonical
eligibility/cap ledger. It did not invoke the official sampler and contains no
selected set.

## Exact result

| Fact | Value |
|---|---:|
| Authority SHA-256 | `0fd1f479e809e0d8f740aa72cff193871b35f45c95a2eb9d96440ca7508b3d1a` |
| Verified inputs | 89 |
| Direct-child submissions | 51 |
| Competitive submissions | 36 |
| Global seed | 22,731,074 |
| Metadata rows / logics | 450,472 / 89 |
| New-family rows | 3,445 |
| Historical rows | 5,345,294 |
| Historical rows ignored outside current metadata | 41,554 |
| Eligible new / old | 3,445 / 249,915 |
| Excluded trivial | 197,112 |
| Configured / matched explicit removals | 2 / 0 |
| Aggregate cap | 45,905 |
| New / old quota | 2,709 / 43,196 |

Historical input rows are 1,388,191 (2018), 730,685 (2019), 563,052
(2020), 772,681 (2021), 658,873 (2022), 740,591 (2023), and 491,221
(2024).

## Artifact roots

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| `downloads.json` | 36,563 | `f1303655b099a0e197857078e1a89efcfce82a0b5055c423a0030f9b0e921e64` |
| `eligibility.jsonl` | 256,182,191 | `576e2d80c9f2a5976c25678f85be9b2267901d5ff9c607829a80c5290467a500` |
| `summary.json` | 18,230 | `84daa16f16e2e118dba622b901122258638e5523cb9590c05cda55cd011ba73c` |
| `input-audit.json` | 537 | `f1ffba1da0a76df655b85252d5f3d784d9c84297023048ca393258c12b4ecf6d` |

The completion payload hash is
`ecf9633827a8572cb114f810306d6026159950007d71d237d1ab46a9dded39f8`.
A fresh-process audit rehashed every retained input and completion dependency,
recounted all 450,472 canonical JSONL rows, checked strict benchmark-ID order,
reconstructed reason counts and aggregate quotas, and confirmed
`selection_observed=false`.

## Retained negative attempts

No failed directory was relabeled or overwritten:

1. `input-audit-1784743920768303217-16764d04` stopped on regexp-valued
   submission logics and exposed the non-recursive submission glob.
2. `input-audit-1784744315286061407-0c81f06d` stopped on the organizer's
   global-logic expansion before Single Query filtering.
3. `input-audit-1784744522957943433-eb81e506` stopped after metadata reduction
   because both configured removal IDs are already absent.
4. `input-audit-1784744715221056942-32ecd649` reduced every historical row and
   stopped when official metadata order differed from canonical path order.

Each correction was committed and pushed before a fresh run. None of these
attempts, or the successful S1b audit, generated or inspected an official
sample.

## Next boundary

S2 must acquire and verify all 90 files in Zenodo record `16740866`, extract
them without traversal or symlinks, and prove the 450,472-row metadata/tree
bijection with exact file SHA-256 values. Official Polars production remains
blocked until that corpus gate completes.
