# LLM Integration Points

Status: draft
Last updated: 2026-06-10

## Purpose

Map where large language models are useful inside Axeyum. The governing
principle is the project thesis itself: LLMs are untrusted search. Every
integration is proposer/checker shaped — the LLM proposes, existing trusted
machinery (evaluator, oracle, proof checker, benchmark harness) disposes.

## Scope

In scope:

- LLM roles across rule libraries, testing, triage, encodings, heuristics,
  explanation, autoformalization, and proving-horizon guidance.

Out of scope:

- Model/provider choice, prompt engineering, agent tooling.
- Any LLM participation in the trusted base.

## Core Claims

- The untrusted-search/trusted-checking architecture admits LLMs natively;
  no special trust machinery is needed beyond what is already planned.
- The highest near-term value is volume work with cheap gates: rule
  conjecture, adversarial tests, triage hypotheses.
- The trusted base (evaluators, proof checkers, lift-map validation) must
  remain LLM-free; checkers stay small so everything else can be wild.

## Integration Points

| # | Task | Gate (trusted disposer) | Earliest phase |
|---|---|---|---|
| 1 | Rewrite-rule conjecture for the rule library. | Exhaustive small-width check + oracle equivalence; rule IDs and obligations. | 3 |
| 2 | Adversarial/metamorphic test generation (semantic edge cases). | Oracle-labeled expected results; lands in `corpus/micro/`. | 1 |
| 3 | Differential-failure triage: layer hypothesis + reduction guidance. | Delta-debugging verifies each reduction step. | 3–5 |
| 4 | Alternative encoding/lowering drafts (adders, shifters, multipliers). | Equivalence check at small widths; PAR-2 on harness decides. | 4–5 |
| 5 | Heuristic/portfolio tuning hypotheses from benchmark telemetry. | Methodology-note corpus runs. | 6+ |
| 6 | Invariant-level code review of hot/tricky code (watch lists, arenas). | Tests, fuzzing, differential suite. Precedent: LLM-found bugs in Rocq and nanoda ("Who Watches the Provers?", 2026). | any |
| 7 | Model/proof/core explanation in user vocabulary. | None needed — presentation only; consumes provenance plumbing. | 2+ |
| 8 | Autoformalization: natural language to Axeyum terms. | Answers are checkable (model evaluation, witness replay), so mistranslation surfaces visibly. | client layer, later |
| 9 | Quantifier instantiation, lemma and induction-hypothesis guessing. | Solver/kernel discharges each candidate; cf. ML-guided instantiation work in cvc5 (2025–26). | horizon |
| 10 | Doc–code consistency sweeps (glossary, ADR drift, stale claims). | Human review of diffs. | now |

## Design Implications

- Evidence artifacts and rule libraries should record provenance including
  "conjectured-by" metadata, so LLM-originated content is auditable.
- The differential harness and corpus conventions are the LLM on-ramps;
  building them well (Phases 1–3) is what makes LLM leverage cheap later.
- Explanation features (point 7) depend on never discarding lowering/lift
  maps — already a hard rule.

## Risks

- Plausible-but-wrong volume: conjecture pipelines without aggressive gates
  create review debt instead of value; gates must be automatic, not manual.
- Benchmark leakage: LLM-generated tests may mimic public corpus instances;
  keep tiers labeled so measured wins are real.
- Drift of LLM output into trusted code paths via convenience; CLAUDE.md
  and review discipline are the guard.

## Open Questions

- [ ] Should rule conjecture be an offline batch pipeline or an interactive
      research CLI mode?
- [ ] What metadata schema marks LLM-conjectured rules/tests in artifacts?
- [ ] At the horizon rungs, does instantiation guidance call an LLM online
      (latency, determinism concerns) or precompute hint libraries?

## Source Pointers

- "Who Watches the Provers?" (kernel diversity, LLM-found kernel bugs):
  https://arena.lean-lang.org/
- ML/LLM-guided instantiation in cvc5 (2024–26): https://arxiv.org/abs/2408.14338
- Lean-SMT proof replay (checked-bridge precedent): https://github.com/ufmg-smite/lean-smt
