# Backward foundation from Autogenesis-1

## Why work backward

Autogenesis-1 is credited only when a clean run establishes B, accepts B into
the durable knowledge state, observes A becoming ready, and then establishes A
using B. Starting from components invites an impressive pipeline that misses
one of those verbs. This document starts from the exit observation and asks
what evidence must exist immediately before it.

The dependency order is:

```text
clean reproduction of B then A
  <- replayable episode and immutable execution identity
  <- accepted A transition whose checked proof derives dependency on B
  <- admission-triggered readiness recomputation
  <- accepted B transition
  <- typed evidence handoff and transactional fact delta
  <- machine-readable selection and fixed budgets
  <- preregistered chain, counterfactual, and corruption controls
  <- generated baseline over exact source identities and known manual seams
```

No later observation can compensate for a missing earlier contract. In
particular, a final proof term mentioning B does not by itself show that B made A
operationally reachable.

## Requirement and evidence matrix

| Required observation | Evidence that proves it | Current verdict | Earliest missing foundation |
|---|---|---|---|
| Inputs were fixed | Clean execution capture binds commit and generated baseline digest | Partial | Retain the first clean `--capture` record |
| B and A were selected without intervention | Content-addressed frontier snapshot plus deterministic selection rationale | Missing | Stable machine-readable frontier output |
| A was unavailable before B | Pre-B attempt under the identical route policy and budget receives no credit for the registered reason | Missing | Counterfactual snapshot and proof-leakage controls |
| B was established | Independently replayed evidence produces a proposed fact delta | Missing | Typed dispatch/evidence adapter |
| B became durable knowledge | Atomic application after fresh-process replay and fact validation | Missing | Episode-wide transaction boundary |
| A became newly ready | Readiness changes only after the accepted B event | Missing | Accepted-transition event and snapshot recomputation |
| A was established using B | Fresh proof is accepted and its dependency on B is derived from the proof term | Candidate substrate | Chain qualification and new-proof dependency check |
| Corruption cannot receive credit | Independent mutations of statement, evidence, checker, dependency, footprint, and status all reject | Missing | Typed episode and evidence identities |
| The sequence reproduces | Clean checkout repeats the same accepted transitions from retained inputs | Missing | Replay command and portable artifact bundle |
| Human proof work was zero after launch | Append-only intervention log contains no proof-affecting action | Missing | Episode event model and audit vocabulary |
| Trusted base did not grow | Before/after kernel declaration classification and checker registry are identical | Partial | Bind both inventories into the execution result |

The generated [Autogenesis baseline](../plan/generated/autogenesis-baseline.md)
is the executable current-state half of this matrix. It refuses stale reviewed
seams and content-identifies the fact ledger, proof-gap authority, schemas, and
the scripts that define their semantics.

The counterfactual half now has an executable first contract:

```sh
python3 scripts/create-autogenesis-snapshot.py \
  --premise F:nat-zero-add \
  --consequent F:nat-mul-one \
  --output /tmp/autogenesis-snapshot.json
```

The creator accepts only a settled `kernel-lean` B -> A edge present in both the
ledger and the kernel-derived direct dependency inventory. It withholds the
original fact rows and theorem names in every phase. Post-B, only a fresh,
episode-namespaced B declaration becomes visible. Candidate admission can then
be checked with `theorem_knowledge_audit`, whose deny/require decisions use the
full transitive declaration closure, so hiding a forbidden proof behind a
helper theorem does not pass.

## Assumptions tested now

### A. The ledger has a usable chain substrate

**Supported, with a narrower meaning than previously reported.** At the first
generated baseline, the whole ledger has 110 facts, 60 edges, 63 isolated
facts, and depth six. The `kernel-lean` subgraph has 40 facts, 52 internal
edges, only six isolated facts, and the same depth.

The global isolation count therefore does not establish that Autogenesis-1
needs a new hundred-fact nursery. Most isolated facts belong to routes where an
independent proposition may correctly have no theorem dependency.

### B. The live ledger can demonstrate a new B -> A transition directly

**Contradicted at this snapshot.** All 40 `kernel-lean` facts are already
settled. Their edges form a replay curriculum, not an open live chain. The
first experiment needs an explicit pre-B knowledge snapshot that withholds B
and A without modifying or lying about the authoritative ledger.

That snapshot must also prevent retrieval of their existing proof terms. Merely
changing two fact statuses to `open` would be theatre: the library could still
contain both answers.

### C. A proof-term edge means B operationally unlocked A

**Unproven.** It proves that one checked proof of A references B. It does not
prove necessity, search reachability, or absence of an equivalent theorem.
Chain qualification therefore requires all three:

1. derived dependency in the newly produced A proof;
2. no-credit pre-B run under the same budget; and
3. a B-removal or equivalent-premise control that fails for the expected
   reason.

### D. A full nursery is prerequisite to Autogenesis-1

**Refuted.** Existing chains are sufficient for a bootstrap replay experiment
if proof leakage is excluded. A connected nursery remains a Phase-2 product for
held-out evaluation, route diversity, and repeated compounding; it should not
delay the first transactional closure.

### E. An exact-commit baseline can be a normal committed generated file

**Refuted by construction.** A file cannot contain the hash of the commit that
contains itself. The stable baseline therefore records content digests of its
authoritative inputs. A separate execution capture binds that baseline digest
to an exact clean commit at launch. Conflating these identities either creates
permanent staleness or quietly records the parent commit.

### F. The current closer is already a transaction

**Only partially true.** `close-fact.py` restores one fact if validation fails.
It does not atomically bind selection, evidence, checker identity, dependency
derivation, fact delta, readiness recomputation, and replay. Its rollback is a
useful primitive, not the Autogenesis transaction boundary.

## Revised critical path

### Foundation 0A — bind reality

1. Gate the generated baseline in both aggregate command paths.
2. Retain a clean execution capture at the exact integration commit.
3. Keep source identity and execution identity separate.
4. Make every reviewed seam depend on a source marker so implementation drift
   fails rather than leaving stale prose green.

### Foundation 0B — qualify the chain

1. Land deterministic derived-chain enumeration with machine-readable output.
2. Choose several small axiom-free Nat candidates from distinct subgraphs.
3. Build a knowledge snapshot that masks retained declarations, ledger rows,
   and evidence. Keep the complete environment for checking, but audit the
   candidate theorem's transitive declaration closure against the deny policy.
4. Measure A before B, B itself, and A after B under fixed budgets.
5. Preregister one primary and one fallback only after those measurements are
   reproducible.

### Foundation 1 — make one closure portable

1. Define internal goal-snapshot and episode values; do not publish a schema
   before the first real route exercises them.
2. Replace caller-selected shell commands with a registered checker operation.
3. Reparse statement and evidence in a fresh arena/process.
4. Produce a proposed before/after fact delta and apply it only after replay.

### Foundation 2 — make knowledge trigger work

1. Emit an accepted-transition event only after durable admission.
2. Recompute the frontier from the new snapshot digest.
3. Record why A changed from ineligible to eligible.
4. Suppress retries whose full episode identity has not changed.

### Foundation 3 — reproduce Autogenesis-1

Run B then A from a clean checkout, repeat it, compare deterministic fields,
audit intervention and trusted-base deltas, and retain both the successful run
and the expected pre-B failure.

## Friction and reliability backlog

These improvements are ordered by how many later steps they simplify:

1. **One machine-readable frontier contract.** Text views remain for humans;
   selection, chain enumeration, and unlock deltas share one canonical object.
2. **One content-identity helper.** Statements, files, library snapshots,
   budgets, and artifacts should not each invent digest formatting.
3. **Registered checker operations.** An evidence kind maps to typed arguments
   and a fixed implementation; arbitrary shell is retained only for the manual
   compatibility path.
4. **Proposed-delta validation.** Validate and display a complete ledger change
   without touching the authoritative fact file.
5. **Snapshot overlays.** Counterfactual experiments name withheld facts and
   declarations without editing committed truth. Original B remains withheld
   after acceptance; only the episode-local B declaration becomes available.
6. **Mutation harness.** Controls declare the field or artifact mutated and the
   exact gate expected to fail; surviving mutations are test failures.
7. **Gate parity.** Every lightweight Autogenesis authority runs from both
   `just check` and `scripts/check.sh`; external or expensive replay is explicit
   and cannot silently masquerade as a pass.
8. **Retained failure vocabulary.** Decline, invalid evidence, operational
   error, timeout, and resource exhaustion remain distinct through reporting.

## Decision pressure beyond Autogenesis-1

The first loop should preserve capabilities needed later without implementing
them prematurely:

- snapshots must support imported Mathlib corpora and non-mathematical domains;
- evidence identity must permit heterogeneous proof plans;
- event records must be suitable for held-out evaluation without becoming a
  truth authority;
- scheduler explanations must survive replacement by learned policies; and
- acceptance must remain reproducible with the proposing policy removed.

The correct next feature after Autogenesis-1 is selected by its retained
failure distribution, not by this document.
