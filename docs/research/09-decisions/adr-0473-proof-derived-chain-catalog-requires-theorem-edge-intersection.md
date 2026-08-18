# ADR-0473: Proof-derived chain catalogs require theorem-edge intersection

Status: accepted
Date: 2026-08-18
Index-summary: A kernel-route label does not make every authored fact dependency proof-derived; intersect ledger edges with the kernel theorem inventory and refuse selection until operational qualification

## Context

The first `fact-frontier.py --chains` implementation counted every
`depends_on` edge whose endpoints used `kernel-lean`. It reported 52 B -> A
edges across 26 consequents in the 110-fact ledger.

That is not what the dependency gate proves. `check-fact-depends-derived.py`
requires every fact-backed theorem dependency used by the proof term to appear
in `depends_on`, but deliberately permits additional authored mathematical
dependencies. Therefore:

```text
proof-derived theorem edge  implies  declared fact edge
declared fact edge           does not imply proof-derived theorem edge
```

Filtering declared edges by route inverted that one-way guarantee. It could
call B an operational unlock for A even when A's checked proof never references
B.

The current theorem inventory also does not cover every named kernel fact. In
particular, 14 integer facts are named in ledger evidence but absent from the
inventory. Treating absence as an empty dependency list would turn missing
coverage into false isolation.

## Decision

`scripts/create-autogenesis-chain-catalog.py` is the scheduler-facing structural
catalog. It:

1. indexes settled `kernel-lean` facts by the theorem named in their own checked
   evidence;
2. reads direct dependencies from the independent kernel inventory;
3. emits an edge only when the kernel theorem edge and ledger fact edge both
   exist;
4. fails when a kernel-derived edge is absent from `depends_on`;
5. reports unnamed facts and named facts missing from the inventory as explicit
   coverage gaps;
6. requires both endpoints to have an empty kernel axiom footprint and all
   other consequent dependencies to be established before ranking them first;
7. content-addresses the ledger, theorem inventory, candidates, ranking policy,
   and refusal; and
8. selects nothing until separate operational qualification proves same-target
   pre-B no-credit, B production, post-B A production with a newly derived B
   dependency, and proof-leakage isolation.

Qualification mode consumes the complete retained experiment rather than a
caller-authored verdict. It verifies content identities for the experiment,
snapshot, B evidence, transaction, readiness delta, pre/post catalogs, and
post-B plan bundle; checks the B/no-A/then-A outcomes and leakage controls; and
binds the selected structural chain to that experiment. The resulting selection
explicitly carries `authoritative_write_authority: false`.

The human `fact-frontier.py --chains` view now consumes the same exact catalog
logic. Both aggregate gate paths build the catalog and run its mutation tests.

## Evidence

On the 110-fact ledger, exact intersection reports 35 named kernel facts, 23
proof-derived direct edges, 10 distinct consequents, and 14 named kernel facts
missing from the inventory. All 23 observed edges are axiom-free. The previous
52-edge count is retained in history as a useful but broader count of authored
kernel-subgraph edges; it is not Autogenesis chain authority.

The retained `F:nat-zero-add -> F:nat-mul-one` experiment at exact commit
`a90255a92` replayed cleanly again: B proved axiom-free, the identical pre-B A
search exhausted its budget with no proof, the durable fixture admission made A
ready, and post-B A proved using the episode-local B. Qualified catalog digest
`95e8c8d401441b98793259d79f95cda485493b81c996c08f0d1df998285c925b`
selects that chain for engineering while granting no authoritative-write power.

Mutation controls prove that an authored-only edge is excluded, a derived edge
missing from `depends_on` fails, duplicate theorem-to-fact identity fails, an
inventory coverage hole is reported rather than inferred, and a rehashed
catalog mutation still fails exact replay.

## Consequences

- The candidate denominator is smaller and more trustworthy.
- `F:nat-zero-add -> F:nat-mul-one`, the existing counterfactual fixture chain,
  remains one of the exact candidates.
- Structural candidacy still does not receive selection credit. A separate
  qualification receipt must bind measured proof search and leakage controls.
- Extending theorem dependency inventory coverage, especially for Int and the
  unnamed kernel rows, can add candidates without weakening the policy.
