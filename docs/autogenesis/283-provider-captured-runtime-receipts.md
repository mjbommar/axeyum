# Provider-captured runtime receipts

Date: 2026-08-26

## Problem

The product-health dashboard previously proved only that important checks were
wired into both aggregate gates. That is useful reachability evidence, but it
cannot answer whether a gate actually ran, which commit it tested, or which
jobs failed. Calling that state green would repeat the project's
checker-that-cannot-fail error at the integration layer.

## Contract

[`capture-ci-receipt.py`](../../scripts/capture-ci-receipt.py) reads a completed
run through GitHub's authenticated API and records:

- the repository, workflow path, run ID, attempt, event, branch, and exact
  tested commit;
- the SHA-256 of the workflow bytes at that tested commit;
- every completed job's ID, name, conclusion, timestamps, and provider URL;
- a conclusion census derived from those rows.

The committed receipt is reproducible online with `--check-online`.
[`check-ci-receipt.py`](../../scripts/check-ci-receipt.py) performs the offline
gate: the tested commit must exist and be an ancestor of the checkout, the
workflow bytes must match, all jobs must be complete and unique, and the census
must rederive exactly.

This is deliberately not transitive. A successful run for commit `A` does not
prove descendant `B` green. Product health therefore reports
`passed-ancestor` or `failed-ancestor`, the exact tested commit, and its commit
identity. Updating the dashboard creates a newer commit, so even a successful
captured run normally remains an ancestor receipt. The generated artifact does
not embed a self-invalidating live commit-distance count.

## Capture sequence

```text
push exact commit
    -> wait for canonical CI run to complete
    -> capture provider response by run ID
    -> online replay the committed bytes
    -> offline-check commit, workflow, jobs, and census
    -> regenerate product health
    -> publish the receipt commit
```

The receipt reports failure as readily as success. Failed jobs are product
health data, not a reason to omit the record. Repair happens in the owning lane,
then the next completed run supersedes the receipt.

## Trust boundary

Git authenticates the committed artifact and GitHub's TLS/API authenticated the
capture. Offline checking cannot independently prove that GitHub once emitted
the JSON; that is why the online replay command exists and why provider URLs and
IDs remain explicit. This mechanism records CI execution, not local
`just check`, and it grants no theorem, fact, or operation authority.

## First captured run

Run `33013805820` tested commit `08b65942ff9d` with 14 completed jobs: eight
succeeded and six failed. The receipt immediately exposed two integration
debts from this lane that narrower checks missed: the new Cargo example made
the generated Lean-completeness inventory stale, and this lane's status file
exceeded the generated-plan size ceiling. Both are repaired in the receipt
follow-up. Other failures remain named rather than absorbed into this lane:
the tier-C resource-exhaustion timing control failed on all Python versions,
stable 1.98 Clippy rejected a concurrent `job_shop.rs` construct, and Rustdoc
rejected private links in concurrent Complex/stack work.

The product dashboard therefore says `failed-ancestor`. It will continue to do
so until a later completed canonical run is captured; repairing source files
does not rewrite history or turn the failed run green.
