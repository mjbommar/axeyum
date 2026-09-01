# CAS certificate audit: what reconstructs, what could, what is `cas-internal`

**Status: IN PROGRESS — skeleton committed early per lane protocol. Verdicts
below are being filled in module by module; anything marked `TODO` has not been
read yet and its row is not evidence.**

Dispatched against
[`2026-09-01-the-cas-certifies-far-more-than-the-ledger-records.md`](2026-09-01-the-cas-certifies-far-more-than-the-ledger-records.md).

## Method correction to the parent document, up front

The parent document's headline is `40 of 53 modules`, produced by an unmasked
grep. Re-measured with Rust line comments, block comments and string literals
masked out:

| query | modules |
| --- | --- |
| `certificate\|Certificate\|fn verify\|fn check_`, unmasked (the parent's) | 41 of 55 |
| the same pattern, comments and string literals masked | **27 of 55** |
| second shape: `struct/enum` named `*Certificate`/`*Cert`/`*Witness`, or `fn verify_*`/`check_*`/`certify_*`/`validate_*`, masked | **23 of 55** |

TODO: union, per-module verdicts.
