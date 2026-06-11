# North Star: General Reasoning, Logic, And Proving

Status: draft
Last updated: 2026-06-10

## Purpose

Record the long-horizon goal — a complete framework for general reasoning,
logic, and proving — so near-term scoping decisions (quantifier-free,
finite-domain) are read as sequencing, not identity. This note maps the
ladder from the current core to that goal and the 2026 landscape at each
rung, so today's IR, solver-trait, and evidence decisions do not foreclose
tomorrow's rungs.

## Scope

In scope:

- The expansion ladder, landscape landmarks per rung, and the design
  implications that flow backward into current work.

Out of scope:

- Commitments or schedules for any horizon rung (each gets its own ADR).

## Core Claims

- The finite-domain core (SAT, QF_BV, arrays, EUF) is the foundation layer
  of a general reasoning framework, not the product boundary.
- The evidence thesis scales all the way up: the modern Lean ecosystem's
  reliability argument is *kernel diversity* — independent re-checkers like
  nanoda (a Rust Lean kernel) and lean4lean cross-checking the official
  kernel. Axeyum's untrusted-search/trusted-checking architecture is the
  same idea applied from SAT upward.
- The Rust gap is the opportunity: as of 2026 there is no maintained
  Rust-native superposition prover at Vampire/E parity and no Rust-native
  general FOL+SMT proof kernel. Existing Rust strength is SAT (RustSAT),
  connection tableaux (small projects), and Lean kernel re-checking
  (nanoda) — the middle of the ladder is unfilled.
- Quantified SMT in production remains E-matching first with MBQI and
  enumerative instantiation as fallback; the 2025–26 frontier (MBQI-Enum,
  ML-guided instantiation) refines selection, not the primitives. The
  primitives are what Axeyum would implement.
- SMT proof production has a clear leader to learn from: cvc5's CPC format,
  formalized in the Eunoia framework and checked by Ethos, with Alethe
  (checked by Carcara, in Rust) as the interop format. Z3's
  DRUP-style proof logs are weaker. Lean-SMT already replays cvc5 proofs
  inside Lean — the bridge pattern Axeyum would eventually want exists.

## The Ladder And Its Landmarks

| Rung | What it adds | Landmarks to learn from |
|---|---|---|
| Arithmetic (QF_LRA/QF_LIA) | Simplex core, branch and bound. | Z3, cvc5, Yices2 (GPLv3 — study, don't embed). |
| Theory combination | Multiple theories in one query. | Nelson-Oppen, polite combination; MCSAT/CDSAT as the modern trail-sharing framing. |
| Quantified fragments | E-matching, MBQI, enumerative instantiation. | Z3, cvc5 (MBQI-Enum 2025). |
| First-order proving | Saturation, superposition calculus. | Vampire (BSD-3; swept all 8 CASC-30 divisions in 2025), E (GPL2+/LGPL dual), Zipperposition (higher-order). TPTP/CASC as corpus and yardstick. |
| Proof production throughout | Checkable artifacts above clausal level. | cvc5 CPC/Eunoia/Ethos, Alethe/Carcara; DRAT/LRAT below. |
| Proof-assistant interop | Export obligations, import checked rules. | Lean 4 (Apache-2.0), lean-smt (replays cvc5 proofs in Lean), lean-auto/Duper hammer stack, nanoda as the Rust kernel precedent. |

## Design Implications (Backward Pressure On Today)

- The IR's `Binder(later)` placeholder is a real commitment: arena and
  interning choices must not assume binder-free terms forever. The binder
  representation question is in the research-questions register.
- `Sort` must stay open to new theory sorts (Int, Real, datatypes) without
  breaking interning or evaluator architecture.
- The solver trait's capability model already distinguishes logics; horizon
  rungs extend capabilities rather than fork the trait.
- Evidence artifacts need a versioned, extensible envelope from the first
  release, because the certificate hierarchy grows rungs (clausal proof →
  theory lemma → quantifier instantiation trace → kernel-checkable proof).
- The rewrite-rule library with stable IDs and proof obligations is the
  seed of the eventual axiom/lemma library; treat rule IDs as long-lived.

## Risks

- Horizon gravity: drifting toward prover features before the foundation
  meets its exit criteria. Mitigation: every rung entry requires an ADR and
  may not starve a foundation phase (roadmap rule).
- The ladder above the finite core is research-hard; landmarks (Vampire's
  CASC sweep) show how far ahead mature systems are. The differentiator
  remains Rust-native, evidence-first infrastructure, not raw prover power.

## Open Questions

- [ ] See the "Horizon: General Reasoning And Proving" section of the
      [research-questions register](../08-planning/research-questions.md).

## Source Pointers

- Vampire: https://github.com/vprover/vampire
- E prover: https://github.com/eprover/eprover
- Zipperposition: https://github.com/sneeuwballen/zipperposition
- TPTP and CASC: https://www.tptp.org/ and https://tptp.org/CASC/
- cvc5 Ethos checker: https://github.com/cvc5/ethos
- lean-smt: https://github.com/ufmg-smite/lean-smt
- Lean 4: https://github.com/leanprover/lean4
- nanoda_lib (Rust Lean kernel): https://github.com/ammkrn/nanoda_lib
- Lean Kernel Arena: https://github.com/leanprover/lean-kernel-arena
- Rust formalized-reasoning index: https://github.com/newca12/awesome-rust-formalized-reasoning
