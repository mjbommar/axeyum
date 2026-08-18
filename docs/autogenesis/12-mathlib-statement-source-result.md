# Mathlib statement-source result

Date: 2026-08-18

## Verdict

**A reusable, proof-isolated source pool now exists.** It is candidate material,
not an evaluation nursery and not proof credit.

The fleet asset was confirmed on s5:

| Object | Identity |
|---|---|
| Mathlib checkout | v4.30.0, `c5ea00351c28e24afc9f0f84379aa41082b1188f` |
| full environment export | 5,863,567,660 bytes; external reference only |
| declaration-name index | 680,925 rows; SHA-256 `869988f…ac5e80` |
| statement-only Nat/Int inventory | 9,729 rows, 38,978,919 bytes; SHA-256 `4285e55…1aecc` |
| selected source candidates | 240 rows in twelve families; SHA-256 `3b4cd0e…b0dc3` |

The full export and statement inventory stay under
`/nas3/data/axeyum/`; neither is vendored. Git contains the exact
[source manifest](../../artifacts/autogenesis/mathlib-statement-source-v1.json),
[extractor](../../scripts/lean/autogenesis_mathlib_statement_inventory.lean),
[selection policy](../../artifacts/autogenesis/mathlib-nursery-source-policy-v1.json),
and [240-row candidate view](../../artifacts/autogenesis/mathlib-nat-int-candidates-v1.json).

## Version decision

v4.30.0 is not the newest upstream release. As observed on 2026-08-18, the
official [Lean release page](https://github.com/leanprover/lean4/releases) and
[Mathlib release page](https://github.com/leanprover-community/mathlib4/releases)
list v4.33.0 as stable and v4.34.0-rc1 as a prerelease; the
[lean4export tags](https://github.com/leanprover/lean4export/tags) track those
lines.

We should not regenerate the 5.5 GB full export merely because a newer release
exists. The repository importer, retained streams, and fleet Lean pin currently
match v4.30.0, so it remains a coherent baseline. The economical sequence is:

1. select and review the small v4.30 statement population;
2. extract only the metadata needed to form dependency components;
3. re-export the final small slices at the exact baseline pin;
4. generate a separate v4.33 statement inventory and compare selected type
   identities; and
5. treat survival across versions as measured generalization, not silently mix
   revisions inside one population.

An importer/toolchain migration may still be worthwhile, but it is a separate
capability change with its own before/after corpus. It should not block nursery
design or invalidate the already reproducible v4.30 source.

## Proof-isolation boundary

The Lean extractor pattern-matches theorem declarations but emits only:

- name;
- defining module;
- universe parameters;
- a human-readable type; and
- a structural type representation.

It never evaluates or serializes `TheoremVal.value`. The external checker
rehashes all 38,978,919 bytes, parses all 9,729 rows, requires exact fields and
portable lexical order, and rejects any proof/value field. The candidate builder
reads only that artifact. It has no path to the checkout or full export.

This boundary already paid for itself: the producer first sorted with Lean's
internal `Name.lt`, while the independent consumer used rendered-name order.
The consumer rejected row three. We regenerated with an independently
reproducible lexical order instead of teaching the checker to trust Lean's
internal ordering.

## Candidate population

The deterministic source policy selects twenty statement shapes from each of:

- integer Fibonacci, GCD, and modular equivalence;
- natural bitwise arithmetic, binomial coefficients, factorials, Fibonacci,
  GCD, logarithms, modular equivalence, primes, and square roots.

Ranking uses only theorem-type structure: fewest distinct constants, shortest
structural type, then name. It does not inspect an Axeyum solve, imported proof,
or expected route. Generated helper names and unstable pretty-printer artifacts
are excluded.

The 240 rows intentionally satisfy the programme's size envelope but do **not**
make the nursery ready. They remain source candidates until an evaluation-only
dependency pass groups whole components, statement-strength mutations are
authored, partitions are frozen, and each selected statement becomes a reviewed
fact-ledger row. This preserves the nine-blocker nursery report instead of
turning source availability into false evaluation credit.

## Next boundary

Derive a graph-only dependency view for these 240 candidates in a sandbox that
can read Mathlib proof values but emits only names/edges and cannot write the
candidate set. Use that graph to reject cross-component, family, and proof-shape
leakage before selecting train/development/held-out membership. Only then run
fixed-budget Axeyum episodes and let their typed declines choose the first
Phase 3 proof-plan primitive.
