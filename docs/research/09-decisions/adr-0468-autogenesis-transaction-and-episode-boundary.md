# ADR-0468: Autogenesis transaction and episode boundary

Status: proposed
Date: 2026-08-18
Index-summary: Content-addressed Autogenesis proposals, compare-and-swap fact admission, and roll-forward recovery events

## Context

Autogenesis-1 requires a result to become durable knowledge before descendants
are scheduled. The repository already had `close-fact.py`, but its transaction
boundary is too small and its trust boundary is too wide: callers author shell
checker commands and evidence rows, the live fact is written before whole-ledger
validation, and only that one file is restored on failure. Its dry run does not
materialize an independently checkable after-state.

The backward-foundation programme has now exercised a narrower typed chain:
snapshot, proposal projection, fresh kernel evidence, typed receipt,
episode-local transition, accepted event, and a complete read-only fact
transaction proposal. Exact-commit replay at `b64f6a8dd` reproduced proposal
digest `e4db86cadd69b305101c9dacbf6f0939cee6d45da9f485b631892d9dd32ceda1`.
The proposal still performs no authoritative write and emits no durable
admission event.

One rename cannot make all of Git, an external artifact store, and a fact file
atomic. Treating them as one transaction would make crash recovery depend on an
unrecorded ordering accident. The v1 boundary must say which state is knowledge,
which records recovery intent, and which publication steps may be retried.

This closes the Autogenesis AG0.5 / S0.6 decision requested by
[`docs/autogenesis/02-phased-roadmap.md`](../../autogenesis/02-phased-roadmap.md)
and
[`docs/autogenesis/07-first-90-days.md`](../../autogenesis/07-first-90-days.md).

## Decision

**Autogenesis v1 uses a content-addressed prepared proposal followed by a
compare-and-swap fact admission. A same-filesystem local journal makes the fact
replacement and admission event crash-recoverable by deterministic roll-forward;
external artifact archival and Git publication are separately retryable,
hash-linked durability steps and are never reported as part of the atomic
filesystem commit.**

The boundary has these rules:

1. A prepared proposal contains the exact before-fact digest, complete validated
   after-fact, registered checker operation and arguments, typed evidence/event
   identities, and its own digest. It cannot claim `committed` state or contain
   an admission event.
2. The applicant independently replays the registered checker operation and
   proposal before acquiring write authority. Caller-authored shell commands,
   statuses, routes, footprints, dependencies, and evidence rows are not
   accepted by this path.
3. Authoritative apply is compare-and-swap: the current fact must be the exact
   authoritative path and match the proposal's before digest. A fixture or
   already-settled row cannot receive production write authority.
4. Before changing the fact, the applicant durably writes a content-addressed
   intent journal on the same filesystem as the fact. The journal contains the
   proposal identity and both fact digests, not mutable orchestration prose.
5. The applicant writes and fsyncs a temporary after-fact in the fact directory,
   atomically replaces the fact, fsyncs the directory, then writes and fsyncs
   the admission event. The event binds the proposal, before/after fact digests,
   evidence identity, and resulting durable-state digest.
6. Recovery is monotone. Before-fact plus intent and no event means uncommitted;
   after-fact plus intent and no event rolls forward by emitting the uniquely
   derivable event; after-fact plus matching event is committed. Any other
   combination is corruption and refuses automatic action. Recovery never
   guesses and never rolls an admitted fact backward.
7. Readiness consumes only the durable admission event, not a prepared proposal,
   bootstrap event, modified file, or successful checker stdout.
8. The external episode/replay bundle is retained outside Git. After local
   admission, the journal/event directory is archived content-addressedly and
   the fact change is published through normal Git review. Those operations may
   be retried; their completion states are reported separately. The fact's
   evidence row stores typed operation and artifact digests rather than a host
   path.
9. V1 admits one fact per transaction. Multi-fact atomic admission is deferred
   until a real proof plan requires it; the event and digest model must remain
   extensible to an ordered set of writes.

## Evidence

- `prepare-autogenesis-fact-transaction.py` derives a valid open-to-proved
  after-state without writing the ledger and rejects both a settled
  authoritative fact and mismatched evidence for a real open fact.
- `replay-autogenesis-apply-experiment.sh` regenerates the kernel evidence,
  receipt, transition, event, and prepared fact transaction in a separate
  exact-commit invocation.
- Existing `close-fact.py` demonstrates that single-file restoration is useful,
  but also that caller-authored evidence and write-then-validate are not the
  intended autonomous trust boundary.
- The current seven authoritative open facts have no admissible matching typed
  evidence. Therefore the positive write/recovery tests must use an explicit
  temporary fact root until a real route closes one; no production fact is
  changed to manufacture the first success.

## Alternatives

### Treat Git commit as the transaction

Rejected. Git publication happens after proof checking and local mutation,
cannot provide process-crash recovery for the applicant, and would couple
autonomous admission to credentials and remote availability.

### Store all episode artifacts in the repository

Rejected for v1. Search traces and retained execution bundles are high-volume
run data, not knowledge rows. The repository stores generators, schemas,
content identities, and accepted fact state; the artifact store retains the
replay bundle.

### Atomically rename fact and event as two files

Rejected. POSIX provides atomic replacement per path, not a two-path commit.
Claiming otherwise hides the exact crash window the journal must resolve.

### Roll back the fact if event publication fails

Rejected. Once the validated after-fact is visible, reverse mutation creates a
second failure window and can erase knowledge observed by another process.
The event is uniquely derivable, so monotone roll-forward is simpler and safer.

### Extend `close-fact.py` with more flags

Rejected as the autonomous interface. It accepts precisely the fields the typed
proposal must derive and executes arbitrary shell. It remains a manual
compatibility tool until migrated consumers no longer need it.

## Consequences

- The next implementation must include fault injection after intent, after fact
  replacement, and after event publication, with exact recovery outcomes.
- Readiness/frontier work cannot consume filesystem observation directly; it
  waits for the committed event.
- Admission and publication status remain distinct in reports. A locally
  admitted but unarchived/unpublished result is not described as fully durable.
- Content-addressed external storage remains replaceable; no repository schema
  commits to NAS paths, hostnames, or one object-store implementation.
- A later multi-fact transaction can extend the ordered write set without
  changing the principle that only independently replayed evidence crosses the
  trust boundary.
