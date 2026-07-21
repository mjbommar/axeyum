# ADR-0334: Preregister Tock LLVM capture v3 replay correction

Status: proposed
Date: 2026-07-21

## Context

ADR-0333 capture v2 closes before Cargo or either official build. Its pushed
producer validates the source, tools, dedicated-cache result, and cache
inventory, then passes the merged capture registration to ADR-0332's frozen
structural metadata validator. That validator correctly requires cache-
preparation field `expected_lock_packages`; the merged capture registration
does not copy that field, so v2 raises `KeyError` and atomically leaves no
output.

The failure does not challenge the accepted cache, the structural validator,
or the capture/build protocol. It identifies one policy-object wiring error at
the seam between them. The complete ADR-0332 cache registration is already
hash-pinned by v2 and validated before the failed call.

## Decision

Create a thin capture-v3 policy wrapper over frozen capture v2. Change only the
argument supplied to structural metadata replay: load and validate the exact
pinned ADR-0332 cache registration, pass that complete object to the unchanged
ADR-0332 validator, compare its result with the same pinned cache summary, and
retain v2's merged capture registration everywhere else.

## Frozen v3 gates

1. Commit and push this zero-result ADR before adding v3. Commit and push the
   thin wrapper, focused tests, and compact registration before the single
   official invocation. V1 and v2 remain closed and are never rerun.
2. Pin capture-v2 registration SHA-256
   `09b61b38b3552fce512a5ace05f5c8bf4f33212d423543c1d976124007ff5c16`
   and exact negative SHA-256
   `2d640758eb00a003ab456953b867830fd6a88bfee702c325774803815822c91d`.
   Validate both before any source materialization or namespace entry.
3. Reuse v2's exact v1 base registration, ADR-0332 cache registration/summary,
   local result/inventory replay, read-only stable cache mount, environment,
   source/tool/admitter identities, two-root build argv/order, cgroup envelope,
   physical-cache-path rejection, virtual-cache count, raw-module equality,
   LLVM-22 extraction/admission, outer atomicity, and no-query boundary.
4. At structural replay only, call `V5.read_registration` on the exact pinned
   `cache-v5-preparation-registration.json` and pass the returned complete cache
   registration to `V5.structural_probe`. Do not synthesize, copy, default, or
   add `expected_lock_packages` to the merged capture registration.
5. Before replay, require the full cache registration to retain its exact
   preparation schema, `expected_lock_packages == 169`, locked/offline metadata
   argv, source commit/tree, producer chain, namespace, and cache-summary
   identities through ADR-0332's unchanged validator.
6. Require the replayed structural result to equal v2's already pinned cache
   summary exactly: active digest `da6971e4...f305`, 162 packages/nodes, 814
   edges, 169 lock packages, one kernel, and 129 workspace/default members.
   Recompute inventory afterward and require byte/topology equality as in v2.
7. The v3 registration and stable result identity include the exact v2
   registration/negative lineage. Build observations remain excluded from
   stable identity exactly as before; no expected module, symbol, timing, or
   admission result is introduced pre-build.
8. Focused tests prove that structural replay receives the full cache
   registration and the merged capture registration remains unchanged; mutate
   the v2 registration/negative hashes, missing/wrong lock count, replay result,
   and post-probe inventory. All 41 v2/v1/cache protocol tests remain required.
9. Success closes only authenticated local T5.5.2 capture/parser admission and
   authorizes a separate zero-row proof/scoreboard ADR. Failure closes v3.
   Neither outcome authorizes cache mutation, source edits, property queries,
   proof, replay, performance claims, or a scoreboard row in this protocol.

No build, module hash, symbol, extraction, or admission may be observed before
the v3 producer and registration are committed and pushed. No gate may be
weakened after the first official invocation begins.

## Result

Proposed. No v3 producer, registration, official invocation, build, module,
symbol, extraction, admission, property query, proof, or scoreboard row exists.

## Rejected alternatives

- **Add `expected_lock_packages` to the merged registration.** Rejected: that
  duplicates a cache-policy field and creates two potentially drifting sources.
- **Copy every cache-registration field into capture v3.** Rejected: the exact
  complete registration is already pinned and has its own validator.
- **Change ADR-0332's validator to accept a partial object.** Rejected: the
  accepted cache contract is not at fault and is frozen.
- **Rerun v2 with an in-place patch.** Rejected: its single official invocation
  is observed and closed.
- **Combine the property proof with v3.** Rejected: capture admission remains a
  prerequisite for a separately preregistered proof/scoreboard result.
