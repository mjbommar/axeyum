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
| A was unavailable before B | The identical A target under the identical route policy and budget receives no credit before B | Fixture | Bind the result into a replayed episode transaction |
| B was established | Catalog-only structural search produces typed, content-addressed, kernel-checked evidence for fresh B | Fixture | Fresh-process replay of the staged transition bundle |
| B became durable knowledge | Atomic application after fresh-process replay and fact validation | Missing | Episode-wide transaction boundary |
| A became newly ready | Readiness changes only after the accepted B event | Fixture | Replace phase projection with frontier recomputation from durable state |
| A was established using B | Fresh proof is accepted and its dependency on B is derived from the proof term | Fixture | Transactional admission and readiness event |
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

This audit proves term dependency, not historical provenance. If a proposer is
given a retained theorem's raw proof body and copies that expression under a
fresh name, the resulting term is extensionally indistinguishable from an
independent reconstruction. Therefore the search process must receive a
sanitized theorem catalog containing visible names and types but no withheld
proof bodies. The full environment belongs only in the separate checker
process. `scripts/check-autogenesis-knowledge-controls.sh` establishes the
current positive boundary (fresh exact-type proof using B) and rejects direct
and helper-mediated reuse of retained A as well as a fresh B that aliases
retained B. A separate process boundary is still required for provenance.

That first process boundary is now executable for Python proposers. A verified
catalog contains canonical theorem types and visible names but no declaration
values or evidence. `run-autogenesis-python-proposer.sh` then gives Bubblewrap
only that catalog, the proposer program, an empty output directory, `/usr`, and
minimal `/proc`/`dev`/`tmp` mounts; it unshares all namespaces and clears the
environment. The aggregate control confirms the repository and network are
unreachable from inside.

This boundary now carries two deliberately small automatic search fixtures.
The sandboxed `autogenesis-induction-proposer.py` enumerates the same structural
Nat plans for every target binder: induction with a definitionally reflexive
base, followed by either the hypothesis itself or its congruence under the
successor constructor. It neither parses the target expression nor contains a
`zero_add` case. The fresh kernel rejects plan 1 and accepts plan 2 for B; the
same interpreter also proves `add_zero` with plan 2 and `zero_mul` with plan 1,
which guards against disguising the retained B proof as an interpreter.

The sandboxed `autogenesis-apply-proposer.py` then sees only the post-B catalog
and deterministically proposes same-arity theorem applications. Separate
kernel processes reparse both digest-bound TSVs, attempt real declarations,
and require the registered outcomes:

```sh
scripts/check-autogenesis-induction-search.sh
scripts/check-autogenesis-apply-search.sh
```

For the current `Nat.zero_add` B -> `Nat.mul_one` A curriculum, B is produced
from the catalog-only structural search in two attempts. The same A target,
policy, and budget of 20 then produce no proof in the `pre_a` phase and a proof
on the first attempt in `post_b`. The accepted closures are axiom-free, exclude
both retained answers, and A contains the fresh episode-local B. Negative
controls prove that plan 1 cannot receive B credit and that the pre-A result
cannot satisfy an expected `proved` outcome.

The B checker also emits a versioned TSV rather than asking orchestration code
to parse its console prose. `create-autogenesis-premise-evidence.py` verifies
the snapshot, catalog, proposal JSON, plan projection, candidate type, accepted
rank, budget, footprint, and retained-answer closure, then derives one
content-addressed internal evidence object. Independent mutation tests reject
changes to each load-bearing identity and assurance field. This is an
exercised internal handoff, intentionally not yet a public evidence schema.

That receipt now derives a second content-addressed object through
`create-autogenesis-premise-transition.py`. It replays the counterfactual
knowledge change from `pre_b` to `post_b`, admits exactly the episode-local B
declaration, and rejects stale evidence, retained-answer leakage, non-empty
axiom or retained-answer closures, a pre-existing episode fact, and any proposed
authoritative-ledger write. The last control matters because the bootstrap B
fact is already proved in the real ledger: this experiment may change only the
episode overlay. Re-running the creator with `--verify` reconstructs the
expected transition from the snapshot and typed receipt rather than trusting
the staged JSON.

The checked transition now emits a third object,
`axeyum-autogenesis-accepted-transition-event`. Post-B catalog construction
requires the complete receipt → transition → event chain and independently
rederives it; the snapshot alone can no longer expose B. The event digest is
bound into the catalog consumed by the sandboxed proposer. An explicit negative
control requests `post_b` with no event and must fail before catalog creation.
`stage-autogenesis-premise.sh` is the single shared producer for this chain, so
the apply-search and proposer-isolation gates cannot quietly implement different
acceptance rules.

This establishes an operational-unlock and catalog-only search substrate, not
Autogenesis-1. The chain remains preregistered by a human; route dispatch is
still shell orchestration; the B change is an episode-local bootstrap overlay,
not a durable ledger admission; event-gated phase projection is not yet a
frontier recomputation from durable state; and the full kernel search has not
yet been replayed from a retained bundle in a clean process. No transaction or
programme credit is claimed. A clean, exact-commit evidence bundle can be retained
outside Git with `--retain NEW-DIRECTORY`; the repository keeps only the
generator, gates, and content identities rather than vendoring execution
artifacts.

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

**Supported for the bounded two-search fixture, not yet for a ledger episode.**
The same-target counterfactual now proves reachability changed within the fixed
catalog-only policies and budgets, with B itself produced by structural-plan
search. It does not prove mathematical necessity, absence of equivalent
theorems under broader search, or an accepted knowledge transition. Full chain
qualification therefore requires all three:

1. derived dependency in the newly produced A proof;
2. no-credit run of the identical A target before B under the same policy and
   budget; and
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
4. Measure the identical A target before and after B under one fixed policy and
   budget, and measure B itself through its intended route.
5. Preregister one primary and one fallback only after those measurements are
   reproducible.

### Foundation 1 — make one closure portable

1. Define internal goal-snapshot and episode values; do not publish a schema
   before the first real route exercises them.
2. Replace caller-selected shell commands with a registered checker operation.
3. Reparse statement and evidence in a fresh arena/process.
4. Produce a proposed before/after fact delta and apply it only after replay.

### Foundation 2 — make knowledge trigger work

1. Replace the bootstrap event with one emitted only after durable admission.
2. Recompute the frontier from the new durable-state digest.
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
