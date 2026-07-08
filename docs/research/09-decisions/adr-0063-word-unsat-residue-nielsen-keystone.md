# ADR-0063: The word-level UNSAT residue is the Nielsen-arrangement keystone (deferred)

Status: accepted
Date: 2026-07-08

## Context

The string decide-rate push (tasks #74–#81) harvested the accessible bounded and
word-equation levers (corpus `sat` 74→82, `unsat` 39, DISAGREE=0 vs cvc5 and
`:status` throughout). The remaining string `unsat` decline class needed a
decision: which of it is soundly decidable now, and which is a deferred keystone?
This must be closed so future work does not re-scope it (the #80/#81 scoping cost
two agents to establish) and does not accidentally ship a word-level wrong-unsat
chasing it.

Word-level `unsat` is **already built and live** — not a new frontier. `refute.rs`
(`axeyum-strings`) ships `RefuteOutcome::Unsat` behind an independent re-check
(slices 1–3: direct clash, chained clash, cycle-ε, augmented clash, congruence/
affix-cancellation disequality), consumed at `smtlib.rs` `apply_word_route` and
certified as `Evidence::UnsatWordClash` (self-contained Alethe, ADR-0061). Plus
`StringGate::confirm` refutes **length/Parikh** contradictions via the unbounded
length abstraction (steps 1/1a). Together these already decide `str001`–`str005`
(congruence + length-projection).

## Decision

**The remaining word-level `unsat` residue reduces to the Nielsen-arrangement
class, which is DEFERRED as a soundness-critical keystone (task #82); the two
search-free sub-classes are not pursued — one is redundant, one is zero-ROI.**

- **Rank #2 — word-derived-ε → length-clash bridge — NOT pursued (redundant).**
  Its only corpus targets (`str004`/`str005`) already decide `unsat` via the
  landed `StringGate` length projection. It is also architecturally infeasible as
  a clean slice: `refute.rs` (`axeyum-strings`) cannot reach the length refuter
  (`axeyum-solver`) without a dependency inversion, and `WordProblem` carries no
  length atom (`build_word_problem` declines `str.len`). Building it would add a
  soundness-critical word-unsat pathway for **zero** verdict change.
- **Rank #1 — two-ended (prefix+suffix) constant clash — NOT pursued now
  (zero measured corpus ROI).** It is the correct completion of the prefix-only
  `check_conflict` and is search-free/sound, but every residual corpus row
  (`quad-028`, `quad-138`, `str007`) has **variable** ends, which equal-length-
  only affix cancellation correctly refuses to cancel — so it decides 0 named
  rows. Under the measure-don't-seed rule it waits for a corpus that needs it.
- **Rank #3 — Nielsen-arrangement `unsat` — the real ~4-row lever, DEFERRED
  (#82).** `quad-028/138`, `str007`, `nf-ff-contains-abs` are unsat only through
  arrangement (Nielsen split) search. Certifying that as `unsat` requires a
  **completeness-of-splits witness** (a proof the enumerated splits at each node
  are exhaustive) — the single largest soundness surface in the arc. Explicitly
  **not** a quick slice.

The non-word rows in the same `:status unsat` bucket — `ctn-repl-to-ctn`
(replace/contains identity), `open-pf-merge` (prefix/substr), `issue2958`
(regex+prefix), `artemis-0512-nonterm` (finite-literal disjunction + `str.to_int`
enumeration) — belong to **other** arcs (theory-specific rewriting / ADR-0054
regex / finite modeling), not T-B.7.

## Evidence

- Per-row mapping (task #80 scoping): `str001/str002` decided by slice-3
  congruence; `str003` by endpoint-inference + augmented disequality;
  `str004/str005` by `StringGate` length (commit `a264681a`); `quad-*`/`str007`/
  `nf-ff` are the Nielsen residue.
- Task #81 verified `str004`/`str005` already decide `unsat` at HEAD and that the
  bridge crate boundary blocks a clean slice; whole-corpus cvc5 + `:status`
  differential DISAGREE=0 with no source change.
- `arrange.rs`'s `SearchOutcome` has **no** `Unsat` variant by construction — a
  cleanly-exhausted search stays `unknown`; this is the invariant that keeps the
  deferral safe.

## Alternatives

- **Build Rank #1/#2 now** — rejected: zero/redundant corpus ROI and (Rank #2)
  soundness-critical surface with no verdict change; violates measure-don't-seed
  and "never add an unsat route you cannot independently re-check for a gain."
- **Ship Nielsen `unsat` from the search's "no branch left"** — rejected as the
  core wrong-unsat trap: the arrangement search's exhaustion is not a
  re-checkable certificate without the completeness witness.
- **Widen the bounded encoder to cover the quad rows** — rejected (ADR-0053: the
  9-hour-hang cost profile; the quad rows are unbounded word equations).

## Consequences

- **Easier / recorded:** the word-unsat frontier is now a single, well-scoped
  keystone (#82) with a known slice order (emit checkable split trace → build the
  independent re-checker → the exhaustiveness witness LAST) and a known soundness
  burden. No future session need re-scope the residue.
- **Harder / revisit:** #82 is a genuine multi-session, soundness-critical arc —
  take it with fresh focus, gate every step on the cvc5 whole-corpus differential
  (DISAGREE=0) plus a quadratic-word-equation differential fuzz, and keep
  `SearchOutcome` `Unsat`-free until the certified path in `refute.rs` is proven.
- **Standing:** with SAT harvested (#77–#79) and this residue mapped, the string
  track's next decide-rate gain is #82; the parallel deep tracks are ADR-0058
  (NRA CAD/nlsat, ~9 arithmetic rows) and #68 (QF_BV in-solver inprocessing,
  perf).

## Backlinks

- Tasks #80 (scoping), #81 (Rank #2 verified-redundant), #82 (the deferred Nielsen
  keystone).
- ADR-0053 (word-equation core, the "unsat only through a re-checkable derivation"
  rule), ADR-0061 (self-contained string Evidence certification), ADR-0062
  (bounded-completeness unsat route).
