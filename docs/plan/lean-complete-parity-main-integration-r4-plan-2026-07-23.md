# Lean complete-parity current-main integration R4 plan

Date: 2026-07-23

Status: **completed; see [R4 result](lean-complete-parity-main-integration-r4-result-2026-07-23.md)**

Parent: [R3 plan](lean-complete-parity-main-integration-r3-plan-2026-07-23.md)

## 1. Defect

R3 made the retained process, store, and acceptance validators independent of
the repository's absolute checkout path. A fresh detached checkout below
`/tmp`, however, exposed one remaining root-sensitive unit-test assumption in
`test_storage_descriptor_rejects_identity_and_network_drift`.

The test changes a freshly observed storage descriptor's `class_root` to the
literal path `/different/checkout/axeyum` while retaining the original
`mount.mount_point`. This is a valid same-mount relocation only when the
observed mount point is `/`. When the repository itself is on a distinct
`/tmp` mount, the production validator correctly rejects that literal path as
outside the observed mount. The test therefore passes in the ordinary
worktree and fails in a differently mounted detached checkout.

This is a fixture portability defect. The production invariant that a storage
class root must remain inside its recorded observed mount is sound and must not
be weakened.

## 2. Exact correction

The accepted relocation control must derive its alternate `class_root` below
the descriptor's own absolute `mount.mount_point`, then recompute the
descriptor identity. It need not create the path because the control validates
the retained representation rather than recapturing live storage.

R4 must also add a rejecting control whose absolute `class_root` is outside an
explicit non-root observed mount. That control must preserve every other
descriptor field, recompute the identity, and fail specifically through the
existing mount-containment invariant.

No production validator, retained authority, accepted evidence file, storage
identity, path hash, or parity denominator may change.

## 3. Required gates

R4 must pass:

1. the focused storage-descriptor test from both the ordinary integration
   worktree and a fresh detached checkout below a distinct `/tmp` mount;
2. all process/store/acceptance unit tests and exact result checks;
3. `just parity-docs` and `just links` in the differently rooted checkout;
4. `cargo fmt --all --check` status recorded separately from the Lean repair;
5. a clean path-scoped commit and push with exact local/remote equality.

The prior R3 full non-format `just check` result remains valid for its exact
revision. R4 changes only this Python test and its preregistration/result
documentation, so it must not rerun or claim external Lean, Axeyum, SMT solver,
network, or retained-evidence execution.

## 4. Nonclaims

R4 grants no official outcome, Axeyum outcome, paired cell, performance row,
or parity credit. It does not change the historical filesystem observation or
claim portability of that observation to another filesystem. It only makes
the validator test express the already intended same-observed-mount
relocation invariant without assuming that every repository lives on `/`.
