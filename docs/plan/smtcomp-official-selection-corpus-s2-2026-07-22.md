# SMT-COMP 2026 Single Query verified corpus (S2)

**Status:** complete

**Implementation commit:** `d48fb0dc99dcf9cfe0d4519e6f97dfdc03d7bf9e`

**Selection observed:** no

The completed corpus acquisition is retained at:

```text
/nas3/data/axeyum/harness/official-selection-2026-sq/corpus-acquisition-1784745749642951377-d48fb0dc
```

It binds the completed S1 input audit, verified every published release byte,
extracted regular benchmark files only, and proved an exact metadata/tree
bijection before publishing completion. It did not invoke the organizer's
sampler and contains no selected set.

## Exact result

| Fact | Value |
|---|---:|
| Authority SHA-256 | `0fd1f479e809e0d8f740aa72cff193871b35f45c95a2eb9d96440ca7508b3d1a` |
| S1 completion SHA-256 | `f1ffba1da0a76df655b85252d5f3d784d9c84297023048ca393258c12b4ecf6d` |
| Verified release files | 90 |
| Logic archives / trees | 89 / 89 |
| Download bytes | 4,890,207,406 |
| Metadata / corpus files | 450,472 / 450,472 |
| Extracted corpus bytes | 82,270,961,563 |
| Unsafe, missing, extra, or duplicate files | 0 |

Every release file matched its published byte count and MD5 and received a
local SHA-256. The streamed extractor rejected absolute, traversing,
cross-logic, symlink, hardlink, and special members. Per-logic trees were
promoted atomically only after exact extraction, and a disk-backed join then
required one extracted regular file for every metadata row and no others.

## Artifact roots

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| `archives.json` | 35,814 | `a7f5441bf9de832cc1f1043a53fbf6237a1c45ac6b3358c3fef40682203ad562` |
| `corpus.jsonl` | 161,831,759 | `a69e768f95a4a44a15c8d5690df2b91494f3e6b3e7d685b4285829d2386d0ad5` |
| `summary.json` | 7,465 | `386fae9d7c42d938bc4ed5a56e7c6fa0142cff9cee919ffaa857aadc9e0dbbef` |
| `corpus-audit.json` | 538 | `a086b77cce4d43db05a0bd6ef6b7752f207b141b82ef9c9c7825ca069df3faf5` |

The completion payload hash is
`1d22d99635587f2ac743af85a30ff753ee60ad1f81f31ac911cb8c5932b998d1`.
A separate fresh process then rehashed all 90 retained downloads against their
published size and MD5 plus recorded SHA-256; recounted all 450,472 canonical
ledger rows in strict path order; reopened and rehashed every extracted file;
and rechecked archive assignment, byte totals, and completion dependencies. It
terminated with:

```text
S2_FRESH_AUDIT_OK|archives=90|logics=89|files=450472|bytes=82270961563|selection_observed=false
```

The acquisition wrote only below its fresh attempt directory. The prior
`/nas3/data/axeyum/corpus/smtlib-2024/` tree was not an output target.

## Next boundary

S3 must materialize and byte-check the pinned organizer source/data/submission
bundle without Git history, create its caches in a lockfile-derived Python
environment with Polars 1.39.2, export the complete Single Query selected set,
and reproduce identical normalized selection bytes and per-logic counts in a
second fresh environment. The S3 runner and its rejecting tests must be
committed and pushed before the first official sample is produced.
