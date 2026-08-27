# ADR-0608: Retrieval is by shape, and "absent" is a different answer from "unanswerable"

Status: accepted
Date: 2026-08-27
Index-summary: Declaration retrieval goes through a shape index over `Kernel::environment()` covering every declaration kind (`shape_search`), not through a name grep or the theorem inventory; and a search tool must distinguish a genuine zero (exit 1) from a query whose vocabulary, kind or namespace the index does not carry (exit 3), so a fact-ledger checker can depend on it and no lane can read an unaimed tool's silence as absence.
Index-status: accepted

## Context

Lanes here repeatedly declared themselves blocked on a lemma that already
existed, proved, in the tree. Audited over commits from 2026-08-25 to
2026-08-27 (method and per-instance list in
[`docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`](../11-design-review/2026-08-27-retrieval-is-the-bottleneck.md)),
**seventeen distinct instances** are visible in commit messages alone, and
**three of them landed as real duplicates** — including one hand-re-derivation
of an already-checked witness that cost a measured 5x on *every* prelude build
until it was found and removed.

The searches were competent. The most expensive instance,
`CReal.congrOfUniformlyContinuous`, was searched for in
`creal/uniform_continuity.rs` — the module where it belongs — and correctly not
found, because it lives in `creal/integral.rs` where its first consumer needed
it. You cannot find by name a thing whose name you do not know.

Three properties of this codebase make a name search structurally unable to
answer the question:

1. **`prelude_theorem_inventory` filters to `Declaration::Theorem`.** `Nat.add`,
   `CReal.integral`, `Rat.polyEval` and `Complex.conj` return **zero rows**
   from it, while a prefix grep for `Rat.polyEval` returns sixteen hits that are
   all lemmas *about* it. The careless query confirms presence, the anchored
   query reports absence, and both are wrong about the definition.
2. **The naming convention is not uniform.** Measured 2026-08-27 over 464
   `CReal` declarations: 315 contain an underscore, 200 contain an internal
   capital, and **114 contain both**. `CReal.congrOfUniformlyContinuous` is
   camelCase while `CReal.equiv_of_le_le` beside it is snake_case, and the Rust
   *field* for the former is `congr_of_uniformly_continuous`. A lane guessing
   either convention searches for a spelling that does not exist.
3. **An empty answer and a wrong question are the same observation.** Every
   existing instrument reports both as no output. A lane that queried a
   package it had not built, or a kind the tool does not carry, receives a
   confident-looking zero.

Prose did not fix this. CLAUDE.md has carried "search for the STEP, not the
NAME" for some time, every brief in the session repeated it, and instances kept
occurring to careful lanes following the instruction.

## Decision

**1. Declaration retrieval is a shape query over the kernel environment.**

`crates/axeyum-lean-kernel/src/shape_index.rs` indexes every declaration of
every kind by the structure of its type — conclusion head constant, the head
constant of each hypothesis taken under that hypothesis's own telescope, every
constant occurring in the type, and (opt-in) every constant occurring in the
checked value. `examples/shape_search.rs` is the CLI. The question it answers is
*"does a declaration of this shape exist, anywhere, under any name?"*

Covering every kind is not an extra: it is the point. A `Definition` query and a
`Theorem` query are different questions and the tool must not silently answer
the wrong one.

**2. A search tool has three outcomes, not two, and the third is not an error.**

* **found** (exit 0),
* **absent** (exit 1) — the query was answerable and nothing matched,
* **unanswerable** (exit 3) — the query named a constant, a declaration kind or
  a namespace root that the built index does not carry, so any count would be
  meaningless.

Unanswerable is checked *before* matching and is not overridable by any
assertion flag. This makes the required same-kind positive control **structural
rather than advisory**: it is not possible to receive "0 rows" from a subject
the tool was never pointed at. Querying a `CReal` name without
`--include-constructed` is exit 3, and `AxNat.add` — a `lean_pp` *export* name
with no kernel declaration behind it — is exit 3 with a pointer to `Nat.add`.

**3. Because it fails on the finding, a fact-ledger `checker_command` may depend
on it**, in both directions: `--expect 1` for a construction that must exist
(which the theorem inventory structurally cannot assert), and `--expect-absent`
for a shape the library must not duplicate. Neither passes by the run merely
completing.

**4. Duplicate detection is part of retrieval.** `--duplicates` groups
declarations whose types are identical up to binder naming. A duplicate is worse
than a delay: two proofs of one fact that must stay in sync while the kernel
happily verifies both.

## Consequences

* The index is built at query time from the prelude builders, ~13 s in
  `--release` with `--include-constructed`, covering 1,797 distinct
  declarations across nine groups. Value indexing adds no measurable cost.
* Rows carry **kernel** names (`Nat.add`), never `lean_pp` export names
  (`AxNat.add`). `AxReal` and `CReal` are distinct namespace roots and are never
  matched against each other by prefix.
* The first `--duplicates` run over the constructed library found **six theorem
  pairs stating literally the same proposition under two names**, none
  previously reported.
* **Stated blind spot, not implied coverage.** A reusable step built *inline*
  inside a larger declaration has no declaration, so no index over declared
  names can list it. `--value-const` is a partial route — it finds the
  *enclosing* declaration when you can already name a lemma the inline step uses
  — and is documented as such rather than as a fix.
* This does not replace `prelude_theorem_inventory`, which remains the
  instrument for theorem *counts* and axiom footprints. It replaces the grep.

## Alternatives considered

* **Better prose.** Rejected on evidence: the instruction existed, was repeated
  per-brief, and instances kept occurring.
* **A discrimination tree / full higher-order matching**, as Mathlib's `exact?`
  uses. Rejected for now as disproportionate: head-symbol plus constant-set
  filtering retrieved every one of the five known misses on the first query, and
  a syntactic index has no defeq blow-up to bound.
* **Indexing rendered type strings and grepping them.** Rejected: it reproduces
  the substring hazard this repository has already been bitten by
  (`contains("Real.")` matching `CReal.`), and it cannot distinguish a
  conclusion from a hypothesis.
* **Making absence an error.** Rejected: a lane legitimately needs to establish
  that a shape is *not* yet proved. That is why absence is exit 1 and carries
  its positive control in the same output.
