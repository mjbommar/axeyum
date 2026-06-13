# ADR-0011: DRAT As The UNSAT Proof Format, With An In-Tree Checker

Status: accepted
Date: 2026-06-13

## Context

Axeyum's identity is "untrusted fast search, trusted small checking": every
`sat` is checked by model replay, but `unsat` is currently *unchecked* — the SAT
adapter marks it `SatProofStatus::Unchecked` (ADR-0007) and nothing verifies it.
This is the largest remaining gap in the trust story and the open
research-questions item "Which proof checker discharges UNSAT in high-assurance
mode?". The foundational DAG's "SAT proof path" layer requires "UNSAT is
checkable outside the solver" via "DRAT/LRAT or chosen proof checker".

The current adapter (`rustsat-batsat`) does not emit proofs, so a *producer*
must come later (a proof-capable adapter such as varisat, or the custom CDCL
core of Phase 6). The *checker*, however, is the trust anchor and can — and
should — be built first and independently, the way a proof assistant's kernel is
the thing you actually trust.

## Decision

Adopt **DRAT** as Axeyum's clausal UNSAT proof format and implement an
**independent in-tree DRAT checker** (`axeyum-cnf`) as the trusted component
that discharges UNSAT.

- The checker takes a CNF formula and a DRAT proof (a sequence of clause
  additions and deletions) and verifies that every added clause is **RUP**
  (reverse unit propagation) or **RAT** (resolution asymmetric tautology) with
  respect to the current clause set, and that the empty clause is derived —
  confirming UNSAT.
- It is deliberately small and self-contained (unit propagation + RUP/RAT), with
  no dependency on the solver that produced the proof, so a checker bug is the
  only trust assumption and it is auditable in isolation.
- A DRAT *producer* is a separate decision (a future ADR): wiring a
  proof-capable SAT adapter or the custom CDCL core to emit DRAT, then routing
  its output through this checker for end-to-end high-assurance UNSAT.

## Evidence

- DRAT is the SAT-competition standard UNSAT certificate format; RUP+RAT
  checking is the standard, well-specified verification procedure (DRAT-trim).
- A checker is exactly the "trusted small checking" component: small, total, and
  independent of search. It is testable now against hand-authored proofs and,
  once a producer lands, against real solver output.
- This closes the research-questions item on the high-assurance UNSAT gate (the
  checker) while honestly separating it from the producer decision.

## Alternatives

- **LRAT** (RAT with hints): checking is simpler/faster and easier to verify
  formally, but the producer must emit unit-propagation hints. Deferred; an LRAT
  path can be added later (DRAT→LRAT via this checker or a trimmer).
- **FRAT / Alethe / cvc5 CPC**: FRAT is a producer-friendly intermediate;
  Alethe/CPC are SMT-level proof formats for the theory layers, relevant later
  when proofs extend beyond clausal UNSAT. Out of scope for the bit-blasted SAT
  layer.
- **Adopt a producer first (varisat)**: rejected as the first step — the checker
  is the trust anchor and is independent of any producer; building it first lets
  any producer be discharged and keeps the unmaintained-varisat dependency
  question separate.

## Consequences

- Axeyum gains a trusted, independent UNSAT checker; `unsat` can become
  high-assurance once a producer emits DRAT through it.
- The SAT/solver result and evidence envelope can later carry a proof-checked
  assurance level (Unchecked → DRAT-checked), distinct from oracle cross-check.
- A proof-producing SAT path (varisat adapter or the custom CDCL core with DRAT
  logging) is the next proof-track step and gets its own ADR.
- Phase 6's "proof-logging target" question is partially settled: DRAT first,
  with this checker as the discharge route.
