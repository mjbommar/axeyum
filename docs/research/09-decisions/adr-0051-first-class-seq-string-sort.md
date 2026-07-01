# ADR-0051: First-class `Seq`/`String` sort in the IR

Status: proposed
Date: 2026-07-01

## Context

axeyum decides the **bounded** SMT-LIB string fragment exactly today: `strings.rs`
(~1305 lines) encodes each string as a `(len, content)` bit-vector pair
(`max_len ≤ 16`, content ≤ 128 bits), lowers every `str.*` op to the BV→SAT path,
and holds `DISAGREE=0` over 371 instances vs Z3
([P2.7 00-current-state](../../plan/track-2-theories/P2.7-strings/00-current-state.md)).
The ceiling is structural, not a bug: **there is no string/sequence sort in the IR**,
so nothing longer than `max_len` — and none of the unbounded word-equation / regex /
extended-function theory Z3/cvc5 solve — can even be *represented*. Strings live in a
side channel (`Parsed = Term | Str`), which is why every downstream pass has to
special-case them.

Strings are the **largest single decide-rate gap by instance count** (~117) against
the measured Z3/cvc5 frontier. The first increment of the P2.7 program
([Phase A](../../plan/track-2-theories/P2.7-strings/03-phaseA-ir-sort-and-combination.md))
is the enabling refactor: make strings ordinary IR terms so the length theory can talk
to the existing LIA solver Nelson–Oppen-style over shared `len(x)` terms, and so the
word-level solver (Phase B) and regex derivatives (Phase C) have a home. That refactor
touches the foundational `Sort` enum, so it needs a recorded decision before code — per
the standing rule that semantics of a new logic fragment are explicit before it becomes
public surface. This ADR closes the "how are sequences/strings represented in the IR"
question.

## Decision

**Add a first-class sequence sort `Sort::Seq(ArraySortKey)` to `axeyum-ir`, with
`String` the distinguished instance `Seq(BitVec(18))` over the Unicode code-point
alphabet; strings become ordinary interned terms, and the existing bounded
`(len, content)` encoder is retained as a sound fast pre-check, not the
representation.**

- **Sort — Copy-preserving.** `Sort` is deliberately a `Copy` enum (recursion is
  interned, not `Box`ed — arrays carry a flat `ArraySortKey`, not `Box<Sort>`, so the
  sort stays `Copy` across ~138 use sites). `Sort::Seq` therefore carries the **same
  flat, `Copy` element key** as arrays — `Sort::Seq(ArraySortKey)` — over the scalar
  element sorts (`Bool`/`BitVec`/`Int`/`Real`/`Datatype`/`Uninterpreted`/`Float`).
  `Sort::String` is the helper `Seq(ArraySortKey::BitVec(18))`: `2^18 = 262144 >
  0x2FFFF`, and the unsigned bit-vector order over `BitVec(18)` **is** the Unicode
  code-point total order (so `str.<`/`str.<=` are the lexicographic order over it) —
  no separate `Unicode` sort or `String` variant is needed. **Nested sequences**
  (`Seq(Seq …)`) are **deferred** exactly as nested arrays are, and migrate to an
  interned `SortId` (a superseding ADR) if a use proves them needed.
- **Terms.** `str.++`, `str.len`, `str.at`/`seq.nth`, `seq.unit`, `seq.empty`,
  `str.substr`, comparisons, `str.in_re`, and the extended functions become IR nodes
  with **string/sequence-valued results** — resolving the `Parsed = Term | Str`
  friction by making strings terms like any other.
- **Length ↔ LIA.** `len(x)` is a shared **integer** term between the (future) string
  solver and the existing LIA online solver (Nelson–Oppen over the `Int`-sorted
  `len`); this is the headline deliverable that closes the `str.len`-unsat gap
  (Phase A · A.2).
- **Model / evidence discipline unchanged.** Every `sat` still replays through the
  ground evaluator (now over the new sort); every `unsat` still carries its existing
  certificate. The bounded encoder remains the decision path for provably-small
  instances (a sound pre-check that never overrides a word-level verdict).
- **Crate boundary deferred.** No `axeyum-strings` crate yet — the sort + eval +
  SMT-LIB round-trip live in `axeyum-ir` (+ the bounded encoder in `axeyum-solver`);
  the crate is split only when the Phase-B word-level solver proves the boundary, per
  the minimal-crate rule ([ADR-0001](adr-0001-vertical-slice-first.md)).

## Evidence

- The bounded encoder + differential-fuzz discipline already work and stay
  (DISAGREE=0 / 371); this ADR only adds a representation *above* them, so it cannot
  regress the validated bounded path.
- SMT-LIB `Seq`/`String` semantics (Unicode alphabet, total order, `str.*` totality)
  are fixed by the standard and by the reference solvers in
  `references/{z3,cvc5}` — no novel semantics are being invented, only represented.
- The δ-relaxation / simplex LRA work landed this cycle (ADR-adjacent, P1.9) means the
  `len`↔LIA combination has a scalable arithmetic backend to talk to.

## Alternatives

- **Keep the `(len, content)` BV pair as the only representation** (status quo).
  Rejected: it is fundamentally length-capped (`≤ 16`) and cannot represent unbounded
  strings, word equations, or non-Thompson regex — the exact ~117-instance gap.
- **A dedicated opaque `String` sort with bespoke ops, no `Seq` parameter.** Rejected:
  it duplicates machinery for `Seq Int` / `Seq (BitVec _)` and re-introduces the
  string-as-special-case friction the parametric `Seq` removes.
- **A separate `axeyum-strings` crate up front.** Deferred, not rejected: the crate
  boundary is only justified once the word-level solver exists (Phase B), per the
  minimal-crate rule; premature extraction would couple an unproven boundary.

## Consequences

- **Easier:** strings are ordinary terms (no side channel); `len`↔LIA combination
  becomes a direct application of the existing theory-combination bus; Phases B–E
  (word equations, regex derivatives, extended functions, models) have a real IR to
  build on.
- **Harder / the cost:** adding a `Sort` variant is a **workspace-wide** change —
  ~138 files reference `Sort::*`, and every *exhaustive* `match` on `Sort` becomes a
  compile error until it grows a `Seq` arm. Mitigated by the sliced rollout
  ([Phase A doc, "Blast radius + slicing strategy"](../../plan/track-2-theories/P2.7-strings/03-phaseA-ir-sort-and-combination.md#blast-radius--slicing-strategy-scoped-2026-07-01)):
  **A.1a** adds the bare variant and a *decline-cleanly* arm in every crate that does
  not yet handle sequences (green build, no new capability), then **A.1b** (eval) and
  **A.1c** (SMT-LIB round-trip) add capability incrementally.
- **Revisited when:** the Phase-B word-level solver lands (may prompt the
  `axeyum-strings` crate split and a superseding ADR for the solver architecture); and
  if the Unicode alphabet bound (`0x2FFFF`) ever needs the full `0x10FFFF` range.

## Foundational-DAG / register updates

- Add `Sort::Seq`/`String` as a new sort node under the foundational DAG's sort layer
  (a new logic-fragment surface — the DAG gate this ADR satisfies).
- Close the P2.7 "string representation" research-question entry with a link here.
