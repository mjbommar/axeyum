# ADR-0049: Abduction (`get-abduct`) as a verify-guarded generator

Status: accepted
Date: 2026-06-22

## Context

Abduction (`get-abduct`) is the third of the three categorically-missing engines
vs Z3/cvc5 (the gap audit in [PLAN.md](../../../PLAN.md);
[P4.7](../../plan/track-4-usecases-frontend/P4.7-synthesis.md)). It turns the
checker into a *generator*: given axioms `G` that do not entail a conjecture `C`,
find a hypothesis (abduct) `H` such that `G ∧ H` is satisfiable and `G ∧ H ⊨ C`,
with `H` over the shared vocabulary. The other two missing engines are now
addressed — Craig interpolation is complete across all seven QF fragments
([ADR-0047](adr-0047-craig-interpolation-proof-based.md)) and CHC/PDR is opened
([ADR-0048](adr-0048-chc-pdr-verify-guarded-invariant-discovery.md)) — and
abduction reuses the same trusted decision procedures.

The question this closes: **how do we generate abducts soundly without a new
trusted component?** cvc5 uses a SyGuS grammar-guided enumerative synthesis. We
take the same shape but keep the *checker* the trust anchor.

## Decision

**`abduct(axioms, conjecture, config)` enumerates candidate hypotheses from the
shared-vocabulary atoms of the problem and returns the first that passes three
independent re-checks; the enumeration is entirely untrusted.** A candidate `H`
is returned only when, decided by the trusted `check_auto`:

1. **Consistency:** `axioms ∧ H` is `Sat` (a replay-checked model);
2. **Sufficiency:** `axioms ∧ H ∧ ¬C` is `Unsat` (so `axioms ∧ H ⊨ C`);
3. **Vocabulary:** every uninterpreted symbol / function of `H` occurs in both the
   axioms and the conjecture.

Any `Unknown` on (1)/(2) rejects the candidate; `Err` propagates (a soundness
alarm). So a generation bug can only cause an over-eager `None`, never a wrong
abduct — the same conservative-slicing + verify-before-return discipline used for
interpolation (ADR-0047), CHC (ADR-0048), and MBP.

First slice (bounded enumerative): collect the Bool-sorted atoms (and their
negations) of `axioms ∪ {conjecture}`, restricted to the shared vocabulary; try
each single literal, then conjunctions of two, smallest first, under a candidate
cap. Edge cases: if `axioms ⊨ C` already, return `⊤` (the trivial abduct); if the
axioms are inconsistent, return `None`. The SyGuS grammar-guided generalization
(richer terms, minimality/weakest-abduct objectives, `get-abduct-next`) is future
work behind the same re-check.

## Evidence

- Tests independently re-check each returned abduct's three conditions: an LRA
  non-entailed case, an EUF equality abduct, the already-entailed `⊤` edge case,
  inconsistent axioms, out-of-scope decline, and a deterministic LCG fuzz that
  re-verifies every produced abduct (0 unsound).
- Reuses `check_auto` (the trusted multi-theory decider) verbatim — no new trusted
  code.

## Alternatives

- **A bespoke abduction calculus.** Rejected: a new trusted component, against the
  trusted-small-checking identity; the verify-guarded enumerator reuses the
  existing deciders.
- **Trust the enumerator.** Rejected: a candidate-generation bug would emit a wrong
  abduct silently; the three re-checks are cheap and make the generator untrusted.
- **Full SyGuS grammar synthesis first.** Deferred: the bounded atom-enumeration
  covers the common shapes soundly and establishes the verify-guarded contract;
  the grammar engine is an incremental upgrade.

## Consequences

- New feature column (`get-abduct`), the last of the three missing engines, with
  self-checked output — extends the moat.
- Revisit/upgrade: grammar-guided synthesis, weakest/minimal-abduct objectives,
  `get-abduct-next`, and the SMT-LIB `(get-abduct)` command surface (coordination
  with `axeyum-smtlib`, like `(get-interpolant)`).
- Adds the `abduct` public surface to `axeyum-solver`; a capability ledger row
  (synthesis, `Validated` — verify-before-return, no per-query certificate)
  accompanies the implementation.
