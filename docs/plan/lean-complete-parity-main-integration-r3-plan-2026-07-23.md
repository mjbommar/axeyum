# Lean complete-parity current-main integration R3 plan

Date: 2026-07-23

Status: **preregistered acceptance-checkout correction; no process or parity credit**

Parent: [R2 incomplete result](lean-complete-parity-main-integration-r2-incomplete-result-2026-07-23.md)

## 1. Defect

The acceptance validator already distinguishes live `0444` evidence from a
Git checkout of committed evidence, but its checkout branch requires exact
filesystem mode `0644`. Git records only executable versus non-executable for
ordinary blobs. Local checkout permissions can therefore be `0644`, `0664`, or
another umask/shared-repository representation while the index still records
the same `100644` blob.

Requiring exact local `0644` is not an evidence invariant. It makes the result
checker depend on checkout umask/configuration and leaves the full docs gate
structurally blind outside the original permission environment.

## 2. Exact accepted representations

`_accepted_readonly_mode(path)` must accept exactly one of:

1. a regular, non-symlink live file with local mode `0444`; or
2. a regular, non-symlink repository file with no executable bits whose exact
   path is a clean tracked `100644` entry relative to `HEAD`.

The second route must require both:

- `git diff --quiet HEAD -- <path>` succeeds, covering staged and unstaged
  content/mode changes; and
- `git ls-files --stage -z -- <path>` returns exactly one stage-zero `100644`
  entry for that exact path.

Local write bits are not evidence authority on the checkout route; exact
content sizes/hashes, canonical records, manifests, seals, namespaces, and
result relationships remain independently validated by every caller.

## 3. Rejecting controls

R3 must reject:

- untracked non-`0444` files;
- executable, symlinked, missing, or non-regular paths;
- tracked paths with staged or unstaged content/mode drift;
- tracked `100755`, non-stage-zero, duplicate, malformed, or wrong-path index
  rows; and
- any existing content, manifest, seal, namespace, or sidecar mutation.

Temporary live-store tests must continue to require `0444`; copying a committed
`0664` checkout file into an untracked directory cannot inherit checkout
authority.

## 4. Required gates

The implementation must add focused helper controls, preserve all existing
acceptance mutation tests, and pass:

1. the complete 169-test retained-evidence stack;
2. exact process/store/acceptance/U2 result checks;
3. `just parity-docs` and `just links`;
4. complete-parity generation from the integration root and a differently
   rooted detached checkout;
5. `just check`; and
6. clean branch/remote equality after a path-scoped push.

No accepted authority/evidence file may change. No Lean, Axeyum, SMT solver,
network, or other external process is authorized by this correction.
