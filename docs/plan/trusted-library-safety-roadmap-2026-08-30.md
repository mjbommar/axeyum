# Trusted library production safety roadmap

Status: accepted programme under ADR-0717
Date: 2026-08-30

## Outcome

Make the safe path the shortest path: one command constructs a theorem receipt,
runs every applicable check, explains every decline, and refuses ledger credit
if coverage or a control is missing.  A contributor should not need to remember
which inventory, footprint, mutation, or real-Lean command applies.

## Threat model

Kernel acceptance alone leaves five independent risks:

1. **kernel unsoundness:** substitution, conversion, universes, inductives,
   recursion, proof irrelevance, or reduction accepts an invalid term;
2. **statement error:** the proved type mistranscribes or weakens the intended
   proposition;
3. **vacuity:** an impossible/irrelevant hypothesis, degenerate definition, or
   zero cofactor makes a readable theorem meaningless;
4. **contamination:** the target proof, an equivalent imported theorem, an
   axiom, opaque, or quotient enters the dependency closure;
5. **false evidence:** a checker exits zero on completion, omits the subject,
   shares the implementation defect, or records stale ledger state.

An empty axiom footprint addresses only part of risks 4 and 5.

## One receipt and one command

Add a generated `theorem-credit` receipt with:

- exact fact and kernel declaration identities;
- external statement source and elaborated-type digest;
- proof hash and direct/transitive dependency identities;
- reached axiom/opaque/quotient/trusted declarations;
- positive semantic examples and boundary cases;
- statement, hypothesis, proof, and checker mutations;
- independent Lean replay result or typed non-representability reason;
- every checker command, expected subject count, observed subject count, exit,
  duration, and tool version;
- ledger transition preview and final transaction identity.

The ergonomic front door should be one bounded command, for example:

```sh
just check-theorem F:example
```

It prints a short ordered table and writes only after every mandatory row is
green.  `--explain` shows commands and artifacts; `--no-write` is the default
for discovery; `--json` supports agents.  No flag may waive a mandatory check
and still produce `proved` credit.

## Phases and exits

### S0 — Inventory the current safety matrix

Generate facts × protections for every proved ledger row: exact statement,
kernel theorem, per-theorem footprint, environment footprint, circularity,
semantic falsification, mutations, independent replay, and coverage-bearing
checker.

**Exit:** every proved fact is present exactly once; absent protections are
reported as gaps, not inferred from neighboring tests.  Deleting a fact or
checker row fails the census.

### S1 — Bind statement identity

For imported/mirrored claims, bind the exact elaborated upstream type and
Axeyum type through a reviewed translation or specialization receipt.  For
native claims, bind a canonical kernel rendering and intended reader-facing
statement.  Preserve previous statements when correcting a row.

**Exit:** swapped binders, changed constants, altered relations, source drift,
and replacing the upstream statement with Axeyum's own rendering all reject.

### S2 — Universal trust and circularity audit

Compute proof dependencies from the admitted term.  Reject target occurrence,
target aliases/equivalents registered in the identity map, nonempty forbidden
trust, unowned opaques/quotients, and mismatch between authored and observed
dependencies.

**Exit:** target injection, indirect target injection, axiom insertion, and
checker-population deletion mutations each fail through different guards.

### S3 — Automatic semantic falsification

Before proof construction, generate the cheapest applicable tests:

- exhaustive finite/small-domain evaluation;
- property-based boundary values;
- SMT/CAS counterexample search;
- definition equations and non-degenerate witnesses;
- removal/weakening of each hypothesis;
- relation, constant, quantifier, and operand mutations.

Failure to falsify a mutation is a review result, not automatically a theorem
failure: some mutations are also true.  But every receipt must classify it and
must include at least one independently demonstrated load-bearing control for
each nontrivial theorem family.

**Exit:** the known false/vacuous fixture pack is rejected and known valid
controls remain accepted; zero executed cases is always failure.

### S4 — Independent proof replay

Export every representable credited theorem closure and ask pinned Lean's
kernel to check it.  Keep Axeyum acceptance and Lean acceptance as separate
grades.  For non-representable theorems, require a typed reason and retain
Axeyum-only labeling.

**Exit:** complete subject census, `missing=0`, wrong-goal and wrong-proof
mutations rejected, and no accepted theorem receives a stronger grade by
inheritance from a sampled family.

### S5 — Kernel differential and mutation programme

Generate well-typed and nearly-well-typed core declarations across conversion,
universes, inductives, recursors, projections, literals, quotient rules, and
proof irrelevance.  Compare Axeyum with pinned Lean.  Mutation-test the kernel
tests themselves and publish surviving mutants by semantic subsystem.

**Exit:** deterministic nonzero corpus per subsystem, zero unexplained
accept/reject disagreement, and a ratchet on killed critical mutants.  Any
wrong acceptance is P0 and preempts production.

### S6 — Atomic credit transaction

The checked receipt, fact transition, dependency-derived cascade, and generated
dashboards commit through one crash-safe transaction.  Checkers operate on a
fresh read of the proposed state, not mutable in-process assumptions.

**Exit:** interruption at every write boundary leaves either old state or a
complete new state; replay is idempotent; stale receipt, source, graph, or
checker versions reject.

## Efficiency rules

- Run cheap statement/semantic checks before expensive proof search.
- Cache by content digest, never by fact name alone.
- Reuse one closure build across footprint, circularity, export, and replay.
- Shard independent Lean checks but aggregate through one generated writer.
- Always report `checked / expected / missing / extra`, not only passes.
- Keep discovery failures typed: false statement, unsupported vocabulary,
  resource limit, no proof, kernel rejection, and assurance rejection are
  different outcomes.

## Parallel ownership

| Lane | Owns |
|---|---|
| `credit-contract` | Receipt schema, validator, one-command UX, atomic transaction |
| `semantic-controls` | Counterexample engines, hypothesis/statement mutations, fixture pack |
| `independent-replay` | Lean export/replay census, kernel differential fuzzing, coverage ratchets |

No lane owns another lane's expected counts.  Aggregate counts are derived.
