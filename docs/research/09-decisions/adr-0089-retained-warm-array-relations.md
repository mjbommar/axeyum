# ADR-0089: Retained Warm Array Relations and Diff Witnesses

Status: accepted
Date: 2026-07-10

## Context

ADR-0086/0087 retain bounded structural array reads and activate their exact
transitive semantics only after a candidate violation. ADR-0088 adds retained
scalar-keyed array-valued UF parents with private array projection owners. The
remaining warm relation boundary is asymmetric:

- direct positive equality is currently accepted only between two user array
  symbols, so `f(x) = a` and `f(x) = g(y)` still rebuild through the canonical
  dispatcher even though every operand already has a total projection owner;
- array disequality always rebuilds, although extensionality gives one exact
  existential witness index and both witness reads are already supported by the
  warm structural-read machinery; and
- positive equality involving `store`, constant-array, or array-ITE terms cannot
  be justified from finitely observed reads. It needs total structural model
  realization like ADR-0085, not an observational shortcut.

The next increment should close the projection-owned equality and exact diff-
witness slices without claiming general structural equality. This advances the
open array/equality question in the
[research register](../08-planning/research-questions.md), follows the array-
first/function-second ownership order of ADR-0084/0088, and keeps ADR-0030's
warm learned-state objective.

## Decision

`IncrementalBvSolver` will admit top-level positive and negative array-equality
literals over arrays with BV indices and Bool or BV elements.

### Positive equality

For `A = B`, both operands must be projection-owned leaves:

- a direct array symbol; or
- a supported scalar-keyed array-valued UF application from ADR-0088.

The solver recursively abstracts application arguments through the existing
warm scalar select/UF path, retains each application and private array owner,
and records a selector-scoped equality edge between the two projection owners.
That edge drives exact same-index read congruence, including reads asserted
before the equality. During SAT model construction, equality classes merge
their array observations before array-valued function tables are built. This
order ensures a function entry captures the merged result rather than a stale
pre-equality private array. Private owners remain hidden and original replay is
mandatory.

### Disequality

For `not (A = B)`, each operand may be any parent already covered by the warm
structural-read contract: symbol, store, constant array, array ITE, or supported
array-valued UF application. The operands must have the same admitted array
sort.

The solver allocates one private BV index `d`, builds the exact scalar root

```text
select(A, d) != select(B, d)
```

and sends both reads through the existing retained abstraction. Structural
reads therefore keep candidate-triggered transitive summaries; application
reads keep their private owners and conditional function congruence. The root,
all newly required read/function congruence lemmas, and the user literal share
the frame or one-shot assumption scope. The diff symbol and all private owners
are filtered from returned models.

The equivalence is the standard extensional array law:

```text
A != B  iff  exists d. select(A, d) != select(B, d)
```

The internal free symbol supplies the existential witness. No finite-domain
enumeration or finite-observation approximation is involved.

### Admission and lifecycle

- Relation handling is literal-only in this increment. Array equality nested
  under arbitrary Boolean structure remains on the canonical route.
- Existing exact limits apply before mutation: 512 structural nodes/read sites,
  depth 256, 64 array-valued UF parents per root, the shared lowering deadline,
  and the candidate-refinement round bound. One-over inputs defer without
  partial warm state.
- Equality edges and generated roots are selector-scoped. Application/read/diff
  metadata may survive pop harmlessly, but only active frame and one-shot terms
  participate in congruence and projection.
- Assumption cores report only original user literals; internal equality,
  congruence, and diff-witness roots are never exposed.
- Unsupported indices/elements/signatures, positive structural equality,
  array-valued UF parameters, nested/extended arrays, and proof logging remain
  deferred.

## Soundness Argument

A positive projection-owned equality imposes a valid array equality relation on
two otherwise total model owners. Same-index read congruence is a direct
consequence, and merging all observed entries plus one common deterministic
default constructs equal total arrays. Building function tables after the merge
makes original applications denote those arrays. Conflicting observations
cannot produce SAT: scalar congruence refutes prepared conflicts, and any
remaining projection conflict or replay failure degrades to `Unknown`.

A negative relation is encoded by an exact existential extensionality witness.
Each structural witness read is tied to its original parent by ADR-0087's exact
summary before SAT acceptance. Thus an UNSAT result follows only from user roots
plus valid equality/extensionality/ROW/function-congruence consequences. A SAT
result contains a concrete witness where the projected arrays differ and must
still replay the original disequality. Selector scoping prevents popped or
opposite one-shot relation consequences from persisting.

Positive structural equality is deliberately excluded. Equal values at a
finite set of reads do not imply whole-array equality, and merging leaf models
without solving store/ITE equations can change structural semantics. Missing
owners, inconsistent merges, exhausted limits/deadlines, or replay uncertainty
therefore cannot yield an accepted verdict.

## Acceptance Validation

- Eight default-feature and nine all-feature focused tests cover no-read
  `f(x) = g(y)` function projection, symbol/application equality, equality
  chains over reads asserted first, private diff-witness projection, self-
  disequality, push/pop, one-shot cores, and private-owner filtering.
- Store, constant-array, and array-ITE disequalities compose with candidate-
  triggered summaries. Bool elements and BV256 index/element values replay.
- Positive structural equality and nested Boolean relation use defer before
  mutation. Depth 256 is admitted while 257 defers with zero diff witnesses;
  ADR-0088's exact 64/65 application-parent regression remains green.
- A deterministic 64-seed matrix contributes 64 warm, 64 `check_auto`, and 64
  direct-Z3 comparisons. All 192 agree, and every warm SAT model replays every
  original relation and scalar assertion.
- All 816 solver unit tests, 77 symbolic-execution tests, the ten-test retained
  array-result-UF suite, and the complete EVM test/fuzz suite pass. The EVM
  corpus does not construct whole-array relation roots, so no timing change is
  claimed.
- Strict solver/EVM clippy, warning-denied solver/EVM rustdoc, documentation
  links, foundational-resource generation, and exact-SHA push gates pass.
  Design commit `d891c901` and implementation commit `70c8a15c` are on
  `origin/main`.

## Alternatives

### Treat finite read agreement as structural equality

Rejected. This is not extensionality: finitely many equal reads do not prove two
arrays equal, and assigning structural terms independently would violate store/
ITE semantics.

### Give every structural array term an independent projection owner

Rejected for this increment. Such an owner requires exact total equations and
leaf-model realization, the warm analogue of ADR-0085. A private symbol alone
would be an unsound flattening.

### Route all disequality to canonical AUFBV

Retained as fallback, but rejected as the warm implementation. One diff witness
plus two already-supported reads is exact and preserves the incremental CNF/SAT
state that ADR-0030 requires.

### Enumerate every finite BV index

Rejected. It is exponential in index width and unnecessary: the free private
diff index is the exact existential witness used by standard array solvers.

### Admit arbitrary Boolean combinations of relation atoms

Deferred. That requires retained Boolean relation flags and candidate-sensitive
positive/negative activation, naturally shared with the future warm equality
bus. Literal roots establish the semantic and model boundary first.

## Consequences

Warm symbolic memory gains exact array disequality across all currently retained
structural parents and positive equality across direct/application projection
owners. Array-result UFs no longer fall back merely because their whole result
is compared with another owned array.

Model construction must track active array-valued applications independently of
observed reads and must merge positive equality classes before function-table
projection. The arena gains private diff-index symbols, but public models and
cores remain user-facing. Positive structural equality, Boolean relation flags,
array-valued parameters, proof artifacts, memory BMC/k-induction, and the
remaining EVM performance gap remain later work.
