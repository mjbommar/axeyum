# Lean U2 TL0.6.3 M2 R4 attempt-003 plan

Status: **preregistered; no R4 implementation, control, harness, discovery, or
selected process exists**

Date: 2026-07-23

Parents: [R3 plan](lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-plan-2026-07-23.md),
[implementation checkpoint](lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-implementation-2026-07-23.md),
and [timeout result](lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-result-2026-07-23.md).

## 1. Decision boundary

R4 authorizes implementation and offline qualification of a new 16 GiB local
address-space lane, followed by at most one selected process for the unchanged
64-case shard. It preserves the proven 512 MiB universal stack, one CTest
worker, one-hour watchdog, family-specific artifact model, and tiered store.
It does not reinterpret R1/R3 diagnostics, skip or reorder a case, add a
per-test timeout, claim an official provider, or create Axeyum, pair,
performance, population, axis, gate, or parity credit.

No R4 implementation, control process, harness, discovery, or selected process
may run until this plan is committed and pushed. Implementation and offline
tests must then be committed and pushed separately. The nonselected fanout
control must pass from that clean remote-equal revision before the one selected
invocation.

## 2. Frozen consumed history

R1 remains invalid with authority record
`0df3ed527d28b12b17cd5a3c0db3970f01a98e7886452feefda3f02068edb9fe`.
R2 remains its zero-process diagnostic completion
`5ef1040a692a7a72650868909f7477beddf770093e86e2162bec5ff3745d459b`.
R3 authority record
`e972d2ec0d69f1d38f9d0844295585b03d9b80433bf56c23b7b8392ca0af1dbc`
binds terminal
`c228a80ef0dec5204a2cd1d9478faef8273f778bf36c12c6d2fbd31262b7c6f6`:
3,600,038 ms wall timeout, SIGTERM, direct child reaped, no live group member,
17 files / 4,908,035 bytes, no JUnit/cases/completion, and zero credit.

The seven CTest rows printed pass and the partial channel output are diagnostic
only. R4 must validate this history and never import those rows as completed
outcomes or reuse any R1/R3 root.

## 3. Attempt and lane identity

| Field | Frozen value |
|---|---|
| run ID | `tl0.6.3-m2-release-linux-shard-0001-v3` |
| attempt / sequence | `attempt-003` / 3 |
| shard | unchanged membership shard `0001`, offsets `[64,128)`, exact 64 cases |
| implementation | full clean pushed R4 invocation revision |
| private work root | new `/home/mjbommar/.cache/axeyum-tl063-m2-r4-<short-revision>` |
| evidence root | `docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m2-shard-0001-r4-attempt-003/` |
| selected process count | exactly one |
| CTest | exact harness, `-j1`, one-hour watchdog |
| memory | 16 GiB `RLIMIT_AS` = 17,179,869,184 bytes per selected process |
| stack | universal `LEAN_STACK_SIZE_KB=524288` |

Any preflight mismatch stops before harness construction. Once selected
discovery or CTest exists, attempt 003 is consumed and cannot retry.

## 4. Why memory changes and stack does not

R3 proved that the environment reaches released Lean and changes runtime
behavior: seven cases completed and `channel.lean` created more dedicated
workers than R1. It then reported `failed to create thread` and deadlocked
while the 8 GiB `RLIMIT_AS` lane was unchanged. Reducing stack size would trade
this known address-space failure against a new unqualified recursion margin;
adding a per-test timeout would change official registration semantics. R4
therefore changes one dimension only: double the local address-space ceiling
while retaining the accepted stack and exact command.

This is a local resource qualification, not evidence that an official provider
has 16 GiB or reproduces the result. Direct-child RSS remains non-performance
data because it does not measure descendants.

## 5. Required nonselected controls

Offline tests must validate 16 GiB limit installation/classification with a
fake child and no selected source. A separately explicit harmless released-Lean
probe must run under the same 16 GiB limit, export `LEAN_STACK_SIZE_KB=524288`,
create nine dedicated tasks that perform no channel or selected-case work,
join all nine, print one exact success line, and leave no group member. Its
source bytes, command, environment, terminal, peak direct-child RSS, and cleanup
must be reported. Failure stops before selected harness construction and does
not authorize stack/memory adjustment.

The existing direct environment probe also remains required. Control processes
are typed preflight evidence and never count as selected U2 attempts/outcomes.

## 6. Evidence and credit closure

R4 must freshly derive the exact 124 generated rows. It retains 64
`.out.produced` captures and three CTest logs by bytes, keeps 56 generated
C/executable intermediates metadata-only, and retains the wrapper once as a
harness artifact. Missing/extra/linked paths, original-source mutation,
metadata/payload misstatement, overwrite, incomplete JUnit, noneligible
terminal, or incomplete completion-last closure invalidates the attempt.

Only a clean exited CTest with exact 64-row no-skip JUnit and complete store may
credit exactly 64 local official outcomes. All parent/provider/Axeyum/pair/
performance/complete-population/axis/gate/parity counters remain zero. Any
timeout, signal, limit, JUnit, artifact, or store failure is retained with zero
outcomes and no retry.

## 7. Required gates and stop

Tests cover exact R1-R3 history, new identities/root non-reuse, unchanged
registrations/order, exact one-variable resource delta, both harmless controls,
16 GiB adapter classification/cleanup, wrapper mutations, family paths,
124/67/56/1 store closure, mixed/all-pass JUnit, invalid terminal/JUnit/store
variants, completion-last conflicts, zero terminal promotion, CLI smoke, and
absence of implicit control or selected execution. Full Lean/parity generators,
known-link exception, and clean local/tracking/remote equality must pass.

R4 stops on any mismatch and never changes memory, stack, timeout, shard,
command, or storage policy after observation. Even a valid 64-case completion
would close only one local physical shard, not Lean 4 parity.
