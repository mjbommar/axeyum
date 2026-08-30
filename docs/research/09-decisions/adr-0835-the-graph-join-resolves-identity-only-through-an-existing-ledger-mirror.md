# ADR-0835: The graph join resolves identity only through an existing ledger mirror, never through a bare name match

Status: accepted
Date: 2026-08-30
Index-summary: L1 phase G2 joins the Mathlib declaration graph (ADR-0820,
446 declarations over population `mathlib-group-defs-v1`) to Axeyum's fact
ledger, kernel declarations, statement vocabulary, curriculum destination,
producers, declines, and trust footprints. 9 of 446 declarations resolve to
a ledger fact via an EXACT match on the fact's own `title` field (never its
id, never a substring), all 9 further resolve to a proved, axiom-free
kernel declaration, and every dimension reports its population and
unresolved names explicitly. 27 name-coincidence candidates are recorded
and deliberately kept unresolved.

## Context

`docs/plan/graph-directed-library-roadmap-2026-08-30.md` phase G2 asks for
the declaration graph joined against seven kinds of Axeyum state (fact ids,
kernel declarations, statement vocabulary, destination nodes, producers,
declines, trust footprints), with the exit criterion: "generated dashboard
reports all join populations and unresolved counts; no theorem-name
similarity silently creates an identity."

That clause is the whole risk of the phase. `Nat.add_comm` in Mathlib and
`Nat.add_comm` in this kernel share a string but are not guaranteed to be
the same proposition -- ADR-0716 already measured a case
(`Nat.multichoose`) where an identical NAME hides Mathlib proving a theorem
about a structurally different definition than the one this kernel builds.
A join whose resolution mechanism is "the names match" would silently
manufacture false identities across all 446 declarations, most of which
are Lean/Mathlib-core lemmas (`Nat.le_trans`, `Nat.zero_add`,
`Nat.succ_add`, ...) that plausibly coincide by name with real Axeyum
kernel declarations without either side having compared what they state.

## Decision

1. **`fact_ids` resolves ONLY through an exact match on a fact's `title`
   field** against the template `"Mathlib v4.30 source proposition
   {name}"` (`scripts/lib/graph_join.py::resolve_fact_ids`). This is never
   a match against the fact's `id` (`F:ml430-nat-add-comm-56a2d614` embeds
   a hash suffix specifically so it cannot be reverse-derived from a bare
   name) and never a substring/fuzzy match. The `F:ml430-*` mirror family
   this matches against is itself a prior, human-authored identity claim:
   each such fact's evidence already compares a rendered kernel type
   against the Mathlib `formal.statement` (see any `F-ml430-*.json`'s
   `kernel-term` evidence notes). This join REUSES that established
   identity; it does not derive a new one from names.

2. **`kernel_declarations` resolves only for names dimension 1 already
   resolved**, via `theorem_of()` -- imported verbatim from
   `scripts/check-fact-depends-derived.py`, the same extraction
   `check-trust-closure.py` reuses for the identical reason (one copy of
   the subject-extraction regex, not two that can drift). Every resolved
   row records its `basis`: `kernel_theorem-field-explicit` when the
   fact's `formal.kernel_theorem` names the subject directly, or
   `checker-command-regex-fallback` when it does not. 7 of the 9 resolved
   rows in the current population carry the explicit, stronger basis.

3. **Name-coincidence candidates are computed and reported, never acted
   on.** `name_coincidence_candidates` scans every declaration with NO
   mirror fact and checks whether its bare string equals some OTHER fact's
   extracted kernel subject ELSEWHERE in the ledger. All 27 hits in the
   current population (e.g. `Eq.symm`, `Nat.le_succ_of_le`) stay
   unresolved with a reason naming the coincidence -- this is the
   demonstration that the prevention was considered and rejected as a
   basis, not that nobody looked.

4. **Vocabulary resolution is root-exact, and one deliberate non-match is
   pinned as a test.** `resolve_vocabulary` checks a declaration's
   top-level name segment against `KERNEL_CARRIER_ROOTS`, the twelve
   inductive types CLAUDE.md's own measured account gives as this kernel's
   complete trusted inductive surface. A Mathlib root of `Fin` (Lean/
   Mathlib's own standalone `Fin n`) is deliberately NOT matched to this
   kernel's `Nat.Fin` -- a different construction -- and
   `test-graph-join.py::test_fin_root_not_matched_to_nat_fin` pins that
   the join produces this exact non-match rather than an accidental
   equivalence.

5. **Six guards, six distinct mutation classes, mutation-verified 1:1**
   (`scripts/check-graph-join.py`, kill table in
   `scripts/tests/test-graph-join-mutations.sh`):

   | Guard | What it catches |
   |---|---|
   | `EMPTY_POPULATION` | the declaration graph has zero declarations |
   | `EMPTY_FACTS` | the fact ledger has zero facts |
   | `ACCOUNTING` | a dimension drops or double-counts a population member |
   | `STALE_ARTIFACT` | the committed join.json disagrees with a fresh recompute |
   | `POSITIVE_CONTROL` | the known-good chain (`Nat.add_comm`) stops resolving, against the REAL fact file, not the cached join |
   | `BARE_NAME_BASIS` | a resolved link whose backing fact does not actually carry the required title/subject evidence |

   `BARE_NAME_BASIS` is the guard that directly enforces this ADR's title:
   it re-derives, from the resolved row alone, that the claimed fact's
   title matches the mirror template and that `theorem_of()` independently
   reproduces the claimed kernel subject. An identity injected by name
   similarity without the evidence trail fails this guard specifically.

6. **The join needs no Lean toolchain and no cargo run.** Every input
   (`artifacts/declaration-graph/graph/*.rows.json`,
   `artifacts/facts/*.json`, `artifacts/trust-closure/identity-map.tsv`,
   `artifacts/autogenesis/{operations,*decline*}.json`,
   `artifacts/ontology/foundational-concepts.json`) is already-committed
   JSON, matching `check-declaration-graph.py`'s own posture.

7. **No second duplicate-detection mechanism.** Trust-footprint's
   `in_identity_class` flag reads `artifacts/trust-closure/identity-map.tsv`
   verbatim (S2's own output); nothing here recomputes
   `Kernel::render_lean` canonical-type equality. This join therefore
   inherits ADR-0790/S2's own stated limit: identity classes are found only
   by BYTE-IDENTICAL canonical types, so a duplicate proposition rendered
   even slightly differently would not be caught by that layer, and this
   join does not attempt to catch it either.

## Evidence

Over the bounded population `mathlib-group-defs-v1` (446 declarations, 7
real roots, ADR-0820):

```
fact_ids:             9 / 446 resolved (437 unresolved, named)
kernel_declarations:  9 / 9   resolved (population = fact_ids.resolved)
statement_vocabulary: 161 / 446 resolved
destination_nodes:    1 / 1   resolved -> curriculum_groups (lean_status: planned)
producers:            0 / 9   resolved
declines:             0 / 9   resolved
trust_footprints:     9 / 9   resolved, all axiom_footprint = []
name_coincidence_candidates: 27 (all unresolved)
```

Two independent runs of `scripts/gen-graph-join.py` produce byte-identical
`join.json` (no timestamps or host-dependent fields). All six guards each
kill exactly their own fixture when deleted in a scratch copy; deleting any
one guard leaves the good fixture passing and every other guard's bad
fixture still failing.

## What this join does not capture

It is bounded to the 446-declaration `mathlib-group-defs-v1` population,
which is heavily Lean/Mathlib-CORE arithmetic and abstract-algebra
typeclass scaffolding (`Add`, `Mul`, `Semigroup`, `Monoid`, `CommMagma`) --
0 of which have a representable Axeyum counterpart, since this kernel has
no bundled-structure/typeclass mechanism at all. `destination_nodes`
operates at POPULATION granularity, not per-declaration, because
`artifacts/ontology/foundational-concepts.json` carries no finer join key.
`producers`/`declines` are checked only against the 9 fact ids dimension 1
already resolved; a producer targeting an unresolved declaration (which has
no fact yet) cannot be seen by this join by construction. Trust footprints
are read from each fact's own committed `axiom_footprint`, never
re-derived by calling the kernel, so a fact whose stored footprint has
drifted from what the kernel would currently report is invisible here.

## Alternatives

**Resolve `fact_ids` by matching the declaration name against a fact's
`id` slug.** Rejected: `F:ml430-*` ids carry a hash suffix specifically so
they cannot be reverse-derived from a name, and matching against `id`
would silently create identities for any two facts an id-slugification
scheme happened to collide on.

**Skip the name-coincidence diagnostic.** Rejected: without it, "no
identity was created from a name match" is an unverifiable claim about
code that never looked. Computing and reporting the 27 coincidences is
what makes the prevention checkable rather than assumed.

**Recompute identity classes from `Kernel::render_lean` output directly,
inside this join.** Rejected per the task's own instruction not to build a
second duplicate-detection mechanism; `artifacts/trust-closure/
identity-map.tsv` (S2, ADR-0790's own dependency) is reused verbatim.

## Consequences

G3 (publish the infrastructure frontier) can read `artifacts/graph-join/
mathlib-group-defs-v1.join.json` for which declarations in this bounded
population already have ledger/kernel/producer coverage and which do not,
without re-deriving any identity judgment. Extending the join to a wider or
different declaration-graph population inherits this ADR's resolution
rules (title-exact match, root-exact vocabulary, reused S2 identity
classes) for free; it does not need a new identity mechanism, only a new
population.
