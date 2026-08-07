# QF_NIA A3 probe-model reuse v1 result — 2026-08-07

## Verdict

Reject probe-model reuse as an A3 breadth lever. The exact 13-row bounded
experiment recovered none of the seven reference-SAT targets, changed none of
the six reference-UNSAT controls to SAT, and produced no wrong verdict. Because
the preregistered target gate was not met, no 200-row run was authorized and no
experimental solver code was retained.

The useful result is a sharper causal split. The former generic model-replay
bucket is now divided between large arithmetic-DPLL search/core workloads and
concrete integer-model reconstruction deadlines. On this population, the
earlier exact-literal consistency probe never returned a reusable SAT model.

## Exact experiment and retained boundary

The temporary implementation introduced explicit conflict, model, and decline
probe outcomes. A model was eligible for reuse only for the identical ordered
literal slice that produced it, and every candidate still had to replay the
selected literals and original assertions. A probe decline supplied no model.
The existing stronger reconstruction fallback remained available after a cheap
probe decline so that the experiment did not turn an early bounded probe into
a new completeness restriction.

The final 13-row capture is
`/tmp/axeyum-qf-nia-a3-probe-model-reuse-v1-final.jsonl`, with SHA-256
`c0692db87ac1050f5eb29c06202ae158c9f34e06857f2f14feb9cf5868fbd558`.
The temporary release binary has SHA-256
`c09cde9a638b6e5c20ce62b90d57919aaafbc723fc4af6f690a8361b3b441e85`.
These hashes identify the local experiment, not an immutable Git commit: the
probe-model patch was deliberately removed after it failed the retention gate.
The retained baseline is the typed reconstruction repair at `4ff9a82c6`, with
its result documentation at `c851a6a14` and the preregistration at `e211d1331`.

The run used the preregistered 8 GiB process ceiling and 24,000 ms per-query
wall-clock bound. All 13 rows returned `unknown`: seven of seven score targets
did not improve, six of six near-miss controls remained non-SAT, and there was
no replay failure or memory-ceiling event.

## Target disposition

The seven reference-SAT targets separate into two residual groups:

- five terminate in arithmetic-DPLL budget, refinement, skeleton-solver, or
  large-core work before a useful probe model exists:
  `juHashMapCreate...p4943`, `juHashMapCreateContainsValue...p32598`,
  `juHashMapCreateIsEmpty...p1784`, `SAT14/1051`, and `SAT14/1280`;
- two reach the existing integer reconstruction boundary and exhaust its shared
  deadline/node search: `From_T2__s1...p20015` and `SAT14/571`.

The six reference-UNSAT controls also remained `unknown`. Their unchanged
outcomes are useful safety evidence, but they are not credited decisions.

## Gates and disposition

After removing the temporary implementation, the retained branch passed 26/26
full-feature arithmetic-DPLL unit tests and warning-denied full-feature
solver-library Clippy. The worktree was clean, proving the rejected mechanism
did not remain in source.

The next A3 slice must preregister one of the now-separated causal groups. It
must not broaden caps or deadlines, and it must preserve all 34 retained QF_NIA
decisions, original-term SAT replay, and zero disagreements. Direct trace
attribution should choose between bounded large-core/search work and the two
SAT reconstruction-deadline targets before another solver-policy edit.
