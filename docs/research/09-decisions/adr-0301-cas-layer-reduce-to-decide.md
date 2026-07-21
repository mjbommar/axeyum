# ADR-0301: A proof-carrying CAS as a separate `axeyum-cas` layer that lowers to the decidable core to certify

Status: proposed
Date: 2026-07-20

## Context

A new initiative (`docs/research/10-cas/`) sets out to build the compute-side
functionality of SymPy / Mathematica — differentiate, simplify, factor, integrate,
solve, series, summation, symbolic linear algebra — in axeyum. The distinguishing
goal is a **proof-carrying CAS**: every answer carries a first-class trust tag
(`certified` / `decidable-uncertified` / `heuristic`), and `certified` answers
carry an independently re-checkable witness.

Two facts from the kickoff survey shape the architecture
(`10-cas/substrate-map.md`, `10-cas/cas-architecture-survey.md`,
`10-cas/decidability-map.md`):

1. **The solver IR is deliberately confined to decidable theories.**
   `axeyum-ir::Op` has Bool/BV/Int/Real/Array/Datatype/UF/FP/Seq heads and **no
   transcendental function heads** (no `exp`/`log`/`sin`/`cos`, and `sqrt` exists
   only as a real-algebraic *value*). Every head has a total evaluator denotation
   and a bit-blast / decision-procedure route.

2. **A CAS's surface is broader than any decidable theory, and provably so.**
   By Richardson's theorem, deciding identity-to-zero for expressions involving
   `sin`/`exp`/`abs` is undecidable; there is no canonical form for general
   elementary expressions and no complete `simplify`. A CAS must therefore carry
   heads and operations that the solver core neither needs nor can decide.

Putting the CAS surface directly into `axeyum-ir::Op` would (a) inject
undecidable, non-total, or model-less heads into an IR whose every layer contract
(`foundational-dag.md`) requires a total evaluator denotation and a
model/proof-lift story, and (b) pollute the clean decidable core that the solver,
the proof reconstructors, and the capability matrix depend on. That is
unacceptable under the existing gates.

## Decision

**Build the CAS as a separate `axeyum-cas` crate — a broad symbolic algebra layer
— and make certification a *lowering* into the decidable IR core.**

1. **Broad algebra, narrow certifier.** `axeyum-cas` owns a CAS expression
   representation for the full surface (a superset of IR heads: transcendental
   functions, symbolic matrices, unevaluated integrals/sums/limits, polynomials
   over a domain tower). Transforms (`differentiate`, `normalize`, `factor`,
   `integrate`, …) operate on this layer and return new expressions.

2. **Reuse the IR for the decidable fragment.** Where a CAS expression lies in the
   decidable fragment (variables, ℚ/ℤ/algebraic constants, `+ − × ÷ ^ℤ`, and
   later the heads a theory supports), it maps to `axeyum-ir` `TermArena` terms
   verbatim, reusing `poly.rs`, `real_algebraic.rs`, and `eval.rs` unchanged.

3. **Certification = reduce-to-decide.** To certify a transform result, the engine
   lowers the correctness obligation (typically `transform(e) − e ≡ 0`, or a
   structural equality) into an IR term over a decidable theory and discharges it
   with an existing decision procedure (`poly.rs` normal form / QF_NRA / QF_BV +
   DRAT / QF_LRA Farkas / …), attaching the returned witness. The trust tag is
   `certified` iff a witness is produced and re-checks; `decidable-uncertified` if
   a complete algorithm produced it without an emitted witness; `heuristic`
   otherwise. **A `heuristic` result is never presented as certified, and no
   `certified` result may be unsound** (golden-tested, mirroring the capability
   matrix discipline).

4. **No new IR heads for undecidable surface.** Transcendental and other broad
   heads live only in `axeyum-cas`. If a future theory makes some head decidable
   (e.g. a bounded/interval semantics), adding it to the IR is a separate ADR
   under the `foundational-dag.md` gates — not a side effect of CAS work.

5. **Every public transform ships its checker and a self-checking scenario**
   (ADR-0008 / ADR-0033 double-duty). SymPy/Mathematica may be **test-only**
   differential oracles; they are never in the trust base of a shipped answer.

The first slice under this ADR is the **certified polynomial kernel** (Phase C0 of
`10-cas/build-plan.md`): `differentiate`, `normalize`, and decidable `equal?` over
the rational-function fragment, certified via `poly.rs` + QF_NRA — answering the
exemplar `D[x² + c] = 2x` with a re-checkable witness.

## Alternatives considered

- **(A) Extend `axeyum-ir::Op` with elementary functions.** Rejected: injects
  undecidable/non-total heads into the decidable core, violating the layer
  contracts and endangering the solver/proof stack. The broad surface does not
  belong where every head must have a total denotation and a proof-lift route.

- **(C) A fully independent CAS with its own arithmetic and no solver reuse.**
  Rejected: discards the initiative's entire advantage — the exact arithmetic,
  the decision procedures, and the self-grounded oracle corpus that make a
  *proof-carrying* CAS tractable in the first place.

- **(D) Certify by differential comparison against SymPy/Mathematica/Z3.**
  Rejected as the *trust base*: that is oracle laundering. External CAS/solvers
  are permitted only as test-time differential checks, per the standing rules.

## Consequences

- The solver IR stays clean and decidable; the CAS gets unlimited surface; the
  decidability boundary becomes an explicit, testable **lowering boundary** — the
  engine certifies exactly when it can lower the obligation into a decided theory.
- Integration gains its flagship property: *finding* an antiderivative may be
  heuristic, but *checking* one is differentiation + a decidable zero-test, so a
  returned integral over the rational/decidable-constant fragment is `certified`
  even when the search was heuristic.
- A new crate boundary is introduced only as the first use exercises it (ADR-0001);
  `axeyum-cas` starts minimal (Phase C0) and grows per `build-plan.md`.
- This initiative must not starve the solver + Lean-parity mission (PLAN.md); its
  phases reuse and stress-test the decision procedures rather than competing for
  sequencing.

## Follow-ups

- Phase C0 scaffolds `crates/axeyum-cas` and lands the certified polynomial kernel
  (TDD, WASM-green, self-checking scenario).
- A later ADR will fix the trust-tag type and the golden test that forbids an
  unsound `certified`, once the second certifying transform needs a shared type.
