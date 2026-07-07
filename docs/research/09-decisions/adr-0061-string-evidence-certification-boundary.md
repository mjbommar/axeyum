# ADR-0061: Evidence certification for non-arena theories lives at the text front door

Status: accepted
Date: 2026-07-07

## Context

Axeyum's `Evidence` contract (`07-verification/evidence-and-checking.md`) is
arena-centric: `produce_evidence(arena, assertions, config)` builds a report, and
`Evidence::check(arena, assertions)` re-validates a `sat` model or `unsat`
certificate by evaluating **against the original `axeyum-ir` term arena**. Every
certified `unsat` variant either re-derives from `(arena, assertions)` (e.g.
`UnsatDiophantine`, `UnsatFarkas`) or carries a self-checking certificate object.

String/regex theory breaks this assumption. The bounded string fragment lowers to
BV, but the **word-equation core** (ADR-0053), **regex symbolic derivatives**
(ADR-0054), and the **length↔LIA bridge** (ADR-0052) are decided over structures
that are *not representable in the term arena*:

- The term IR has only a handful of `Seq` operators; `str.in_re` / `replace_re` /
  `str.contains` do not exist as arena terms. They live only in the bounded
  packed-BV *encoding* or in the parser's word / membership / length **side
  channels**, built from the parse tree (`axeyum_smtlib::Script`), not the arena.
- A *word-only-fallback* script (the bounded encoder declined it wholesale) has an
  **empty `script.assertions`**.

Two soundness incidents made this concrete (tasks #62/#63):
`produce_evidence(arena, &[])` reported a **vacuous `sat` with `checked = true`** for
an `unsat` word/regex problem (empty arena view is trivially satisfiable), and a
bounded `unsat` for a `sat` membership — each passing `Evidence::check` because the
check ran against the wrong (empty/bounded) view. `check_auto` (arena-level) was
equally wrong; only `solve_smtlib` (the parse-tree Script routes) was correct.

The question this ADR closes: **where is the evidence-certification boundary for a
theory that the arena cannot faithfully represent?**

## Decision

**Evidence for non-arena theories is produced and re-checked at the *text* front
door, not the arena front door, and its certificates are *self-contained* —
re-derived from the parse-tree decision object, never from `(arena, assertions)`.**

Concretely (tasks #63, #58):

1. `produce_evidence_smtlib(input: &str, config)` is the string-capable door. A
   string script (`uses_bounded_strings || word_only_fallback.is_some()`) delegates
   the *decision* to `solve_smtlib` (whose `sat` is Seq-level replay-checked inside
   the routes and whose `unsat` is a re-checked theory conflict), and wraps the
   **sound verdict** without inventing a bounded model. Non-string scripts route to
   the existing arena `produce_evidence` byte-for-byte.
2. A string `unsat` carrying a transferable certificate becomes a **self-contained
   certified `Evidence` variant**. The first is `Evidence::UnsatRegexEmptiness {
   membership, lean_module }`: `Evidence::check` **ignores `(arena, assertions)`** and
   re-derives the derivative-emptiness closure from the stored `Membership` from
   first principles, re-running the kernel `infer`/`def_eq False` check — the stored
   module string is never trusted. This mirrors how `UnsatDiophantine` re-derives,
   but the re-derivation input is the *parse-tree object*, not the arena.
3. A string `unsat` with no transferable certificate yet (word clash, concat/length
   conflict) is recorded as a **correct-but-bare `Evidence::Unsat(None)`** — the
   sound verdict, honestly uncertified. Never a fabricated bounded model, never a
   spurious `checked = true`.

## Consequences

- **The arena `Evidence::check(arena, assertions)` contract is unchanged and stays
  honest.** It never claims to check a string query — string evidence is produced by
  and re-checked through the text door. Consumers with a string query must use
  `produce_evidence_smtlib` (the dominance audit harness now does, #64).
- **Soundness trap to remember:** `Evidence::Unsat(None).check()` returns a *vacuous*
  `Ok(true)` (there is no certificate to refute). Any consumer crediting a
  "checked"/"certified" status for a string row MUST gate on `is_certified()` first
  (false for `Unsat(None)`, true for `UnsatRegexEmptiness`) — never on `check()`
  alone. The audit harness credits `evidence_checked` as `is_certified() && check()`
  for string scripts precisely for this reason (#58c).
- **Extensible pattern.** Every future non-arena theory result (sequences, the
  word-clash certificate #58b via `reconstruct_word_clash_to_lean_module`, richer
  regex/length refutations) follows the same shape: a self-contained `Evidence`
  variant whose `check()` re-derives from the parse-tree decision object. New string
  `unsat` classes land as *new certified variants*, shrinking the residual
  `Unsat(None)` set toward the Gap-7 ledger goal (Lean coverage never regresses).
- **Determinism/soundness invariants hold:** the verdict always comes from
  `solve_smtlib` (replay-gated `sat`, re-checked `unsat`); `is_certified()`/`check()`
  only ever hold on a re-derived kernel-checked `False`.

## Alternatives

- **Represent strings/regex in the term arena.** Rejected for now: a word-level
  string core + regex terms in the IR is a large, still-open design (`P2.7`); until
  then the arena cannot host these queries, and forcing a bounded arena view is
  exactly what produced the #62/#63 wrong verdicts.
- **Store the Lean module and trust it at re-check.** Rejected: `check()` must
  independently re-derive; a stored proof string is an output artifact, never a
  trusted premise (consistent with the ADR-0041/0042 reconstruction discipline).
- **Return `unknown` for all string `unsat` in the evidence layer.** Rejected: the
  verdict is sound and known; a bare `Unsat(None)` records it honestly, and certified
  variants upgrade it — degrading to `unknown` would discard a correct result.

## Backlinks

- Word core ADR-0053, regex derivatives ADR-0054, length↔LIA ADR-0052.
- Reconstruction discipline: ADR-0041/0042 (proof is evidence, re-derived not
  trusted).
- Tasks: #63 (`produce_evidence_smtlib`, f719c27d), #58 (`UnsatRegexEmptiness`,
  a7c323cc), #64 (audit harness → text door), #58b/#58c (word-clash cert + audit
  crediting), Gap 7 in the 2026-07-07 gap analysis.
