# ADR-0820: The declaration graph reuses the artifact contract's type/proof separation, adds an atomic type-to-constructor edge to make mutual inductives detectable, and drops binder display names for alpha-invariant digests

Status: accepted
Date: 2026-08-30
Index-summary: L1 phase C1/G1 builds a real (not hand-authored) declaration
graph over a bounded, named Mathlib population by parsing lean4export ndjson
directly, reuses ADR-0800's compute_closure/project_type_only rather than
re-deriving them, adds a deliberate type->own-constructor edge so mutual
inductives become detectable graph cycles at all, and drops binder display
names from canonical text because lean4export's macro hygiene assigns
per-elaboration-session numeric suffixes that made two independent exports
of the identical declaration disagree byte-for-byte.

## Context

`docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md` section C1
and `docs/plan/graph-directed-library-roadmap-2026-08-30.md` section G1 ask
for the declaration-level graph BELOW G0's module-import graph (ADR-0805):
one row per declaration, direct and transitive dependency edges split by
type versus proof/value, and cycle handling that classifies mutual
recursion/mutual inductives rather than silently dropping edges to force
acyclicity. `docs/plan/global/50-planning-rules.md` requires proof-derived
data to be PHYSICALLY excluded from anything a producer pipeline reads, and
ADR-0800 already built the mechanism for that (a projection function that
destructures only type-facing keys) over nine hand-authored Lean-core
declarations. This ADR is C1/G1: it turns that mechanism loose on a real,
pinned-toolchain-extracted population, and records what changed to make
real data behave.

## Decision

1. **Reuse ADR-0800's digest/closure/projection functions verbatim, via
   `importlib`, never reimplemented.** `scripts/lib/declaration_graph.py`
   loads `scripts/check-library-artifact-contract.py` (a dash-named file, so
   a plain `import` cannot reach it) and calls `compute_type_digest`,
   `compute_value_digest`, `compute_identity_digest`, `compute_pack_digest`,
   `compute_closure`, and `project_type_only` directly. A declaration-graph
   row is shaped as a valid ADR-0800 pack record (plus two extra fields,
   `mutual_group` and `origin_module`, which those functions never read), so
   `scripts/check-declaration-graph.py` can call ADR-0800's own guard
   functions (`check_missing_roots`, `check_no_duplicate_names`,
   `check_pack_digest`, `check_record_digests`,
   `check_typeproj_no_value_leak`) against real graph data with no
   modification.

2. **The population is a committed, named file, checked first.**
   `artifacts/declaration-graph/populations/mathlib-group-defs-v1.json`
   names seven real roots -- `Semigroup`, `CommMagma`, `Monoid`,
   `mul_left_cancel`, `mul_comm`, `mul_assoc` (all from
   `Mathlib.Algebra.Group.Defs`), plus core `Nat.add_comm` -- and was
   committed BEFORE any extraction ran. `check_missing_roots` reads this
   file's `expected_roots` as external authority, never the graph's own
   `source_population` counts, so a pack that deletes a root and tidies its
   own metadata to match still fails (identical guarantee to ADR-0800's).

3. **A lean4export-derived declaration's binder display names must NOT be
   part of canonical text.** Measured directly: exporting `Nat.add_comm`
   through two independent `lake env` invocations (once via mathlib4's
   environment, once via lean4export's own Init-only environment) produced
   byte-identical structural content for the shared auxiliary
   `Nat.add.match_1` in every respect except bound-variable NAMES --
   `x._@.Init.Prelude.#2075127268._hygCtx...` in one run,
   `x._@.Init.Prelude.#2314059840._hygCtx...` in the other. Lean's macro
   hygiene assigns those numeric suffixes per elaboration SESSION, not per
   declaration, so rendering them makes `type_digest`/`identity_digest`
   disagree between two independent, semantically identical exports of the
   same real declaration -- exactly the nondeterminism a content digest
   exists to catch. `render_expr` therefore never renders a binder's display
   name at `lam`/`forallE`/`letE` (printing `_` in its place); only the de
   Bruijn body references (`#i`) and the binder's TYPE are hashed. This is
   safe because Lean terms are meaningful up to alpha-equivalence. Verified:
   two independent regenerations of the full 446-declaration population are
   now byte-identical (`diff` empty).

4. **An inductive type depends on its own constructors, as a deliberate
   modeling choice beyond what the type's own declared Lean type says.** A
   naive graph with only "constructor mentions the type(s) it refers to" as
   an edge can NEVER form a literal cycle for any inductive, mutual or not:
   nothing ever points back at the type (a type's own declared type is
   always just `Sort _`). This would make mutual inductives structurally
   undetectable by any cycle-based classifier, and even an ordinary
   multi-constructor type like `Nat` would show zero cycles. The fix adds
   one edge per inductive type, to each of ITS OWN constructors -- a real
   semantic fact (the kernel checks a type and its constructors as one
   atomic `Declaration::InductiveDecl` unit, never separably) -- which turns
   `Nat <-> {Nat.zero, Nat.succ}` and a synthetic cross-type mutual
   inductive fixture into real, correctly-classified 3-node and 4-node SCCs
   respectively (`scripts/tests/test-declaration-graph.py`'s
   `CycleClassificationTests`).

5. **Every row in one `inductive` JSON record shares ONE `mutual_group`: the
   whole block's type+constructor+recursor name set**, not each type's
   narrower per-family `all` list. A single-type inductive with several
   constructors (`Nat`: `zero`/`succ`) needs its ENTIRE constructor set to
   explain the SCC the atomic edge above creates; a narrower per-constructor
   group of `[type, this-ctor]` cannot, because `Nat` reaches both `zero`
   AND `succ`, making all three nodes one SCC via `Nat` as the hub.

6. **Cycles are computed and classified separately for the TYPE graph
   (`direct_type_deps` only) and the FULL graph
   (`direct_type_deps ∪ direct_value_deps`)**, via Tarjan SCC, with
   self-loops stripped and reported separately (a length-1 cycle carries no
   ordering obligation, unlike a genuine multi-node SCC). A multi-node SCC is
   classified `mutual_inductive` or `mutual_recursion` iff its whole node set
   is a subset of some member row's `mutual_group`; anything else is
   `UNEXPECTED_CYCLE` and fails the gate -- silently dropping an edge to force
   acyclicity is exactly the failure mode this roadmap phase forbids.

7. **Eight guards, eight distinct mutation classes, mutation-verified 1:1.**
   Five are ADR-0800's own (MISSING, DUPLICATE, REORDERED, TRUNCATED,
   VALUE_EXPOSED); three are new, one per exit-criterion requirement this
   phase adds beyond C0:

   | Mutation | Guard | What only that guard checks |
   |---|---|---|
   | ROW deletion | `check_endpoint_resolution` | every `direct_type_deps`/`direct_value_deps` name resolves to a row in this graph |
   | EDGE deletion | `check_edges_consistent` | the materialized `edges.json` exactly equals edges recomputed from `rows.json`'s own `direct_*_deps` |
   | unexplained cycle | `check_cycle_classification` | every multi-node SCC is a subset of some row's `mutual_group`; `cycles.json` matches a fresh recomputation |

   `check_record_digests` (TRUNCATED) alone does NOT reliably catch a row
   deletion: `compute_closure`'s `edges.get(n, [])` silently treats a
   dangling name as a childless leaf, so deleting a row with no further
   dependencies of its own changes nothing any other row's recorded
   transitive closure contains. `check_endpoint_resolution` is what actually
   catches it. Similarly, deleting one entry from `edges.json` alone changes
   nothing any ROW-level guard inspects (every row's own `direct_*_deps`
   field is untouched) -- only `check_edges_consistent`, which recomputes
   the edge set independently, can see it. `scripts/tests/
   test-declaration-graph-mutations.sh` builds nine fixtures (a small,
   synthetic 5-declaration good graph -- including one genuine, correctly-
   classified mutual-inductive cycle, proving the CYCLE_CLASSIFICATION guard
   tolerates an EXPLAINED cycle rather than rejecting all of them -- plus
   one mutation per guard), neutralizes each guard in a scratch copy of BOTH
   `check-declaration-graph.py` and `check-library-artifact-contract.py`,
   and confirms each deletion flips EXACTLY its own fixture.

## Alternatives

**Vendor lean4export's raw ndjson exports into the repository.** Rejected:
the roadmap and CLAUDE.md both forbid vendoring Mathlib-derived bulk data;
`scripts/gen-declaration-graph.py` reads the pinned toolchain checkout and
writes only the four compact derived JSON files (`rows`/`typeproj`/`edges`/
`cycles`), the same posture ADR-0805's module-baseline receipt takes toward
a Mathlib checkout.

**Render binder display names and accept that two independent exports of the
same declaration might disagree.** Rejected once measured: this would make
`identity_digest`/`pack_digest` nondeterministic across ordinary re-runs
whenever an auxiliary declaration carrying a hygienic internal name is
pulled in from two different root closures, defeating the entire point of a
content digest. Dropping binder names is lossless for a term's meaning
(alpha-equivalence) and costs nothing a consumer of this graph needs.

**Force acyclicity by dropping the edge that closes a cycle.** Rejected per
the roadmap's explicit instruction ("do not 'fix' those by dropping edges";
CLAUDE.md's standing account of checkers that manufacture unfalsifiable
green results by construction). An edge silently dropped to make a graph
look acyclic is a graph that no longer describes what the data actually
contains.

**Treat every SCC as acceptable ("cycles happen in real code").** Rejected:
that is indistinguishable from a checker that cannot fail. Classifying each
cycle against `mutual_group` and failing on anything unexplained is what
makes an actual extraction bug (or a genuine wrong-edge defect) visible
instead of invisible.

## Consequences

G2 (join Axeyum state) and G3 (publish the infrastructure frontier) can
treat `artifacts/declaration-graph/graph/mathlib-group-defs-v1.{rows,
typeproj,edges,cycles}.json` as a checked precondition. Any future
`gen-declaration-graph.py` run over a wider or different population inherits
this ADR's four correctness properties for free (reused digest/closure
mechanism, alpha-invariant text, atomic inductive edges, cycle
classification) without re-deriving them. A producer pipeline must read only
`*.typeproj.json`, never `*.rows.json`, for anything upstream of a decided
kernel admission -- the same rule ADR-0800 states for its own pack/
projection pair.

## What this graph does not capture

446 declarations from 7 real roots is a bounded, stated-as-such extraction,
not all of Mathlib (`docs/formalized-math-2026-08/diary-import-scale.md`
measures a full `lean4export Mathlib` dump at 680,925 records, ~4 minutes,
~7 GB -- an unbounded run was never attempted here). Per-declaration MODULE
attribution is only the REQUESTING root's own module, not a true
declaration-to-Mathlib-file map (that join is G0's module graph's job, not
this one's). Recursor iota-rule bodies (`rules[*].rhs` in lean4export's
`inductive` records) are not walked into edges at all -- a Recursor is a
TRUSTED kind by construction (ADR-0800's `TRUSTED_KINDS`), so it carries
zero value/proof edges regardless of what lean4export's own export happens
to include for it, and its `type` field alone is what is walked for
`direct_type_deps`. The real Mathlib population extracted here contains no
naturally-occurring UNEXPECTED_CYCLE and (among the 49 real cycles found,
all `mutual_inductive`) no naturally-occurring mutual-RECURSION example
either -- both classification branches are proven correct against synthetic
fixtures in `scripts/tests/test-declaration-graph.py`, independent of
whatever a given bounded real population happens to contain.
