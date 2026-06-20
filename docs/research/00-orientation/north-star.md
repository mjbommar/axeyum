# North Star: Solver Replacement, Then Lean / angr First-Class

Status: draft
Last updated: 2026-06-13

## Purpose

Record the long-horizon goal so near-term scoping (quantifier-free,
finite-domain) is read as *sequencing*, not identity. The product goal is a
**usable, ideally pareto-dominant system for constrained program optimization
and software verification**, reached through three destinations in order:

1. **Foundation** — the decidable finite-domain + arithmetic core with checkable
   evidence (where the project is today).
2. **Complete solver replacement** — a drop-in Z3/cvc5-class SMT solver: full
   theory coverage *and* competitive performance.
3. **Lean / angr as first-class functionality** — program analysis
   (angr/unicorn: binary/IR frontend, memory model, symbolic execution +
   emulation) and proof assistance (Lean: kernel-checkable proofs,
   proof-assistant interop) as first-class capabilities, not consumers on top.

This note maps the technical ladder from the current core to those destinations
and the 2026 landscape at each rung, so today's IR, solver-trait, and evidence
decisions do not foreclose tomorrow's rungs.

**Where we are (2026-06-13):** destination 1. Not yet a solver replacement
(performance on real corpora is the open gate, not theory breadth alone); not
yet Lean/angr-class (the symbolic-execution consumer is a test-only register
VM). Destinations 2 then 3 are the work ahead.

**Measured update (2026-06-20) — destination 2 is NEAR-PARITY on the first
public corpus, not an open chasm.** On the public p4dfa QF_BV slice @20s, axeyum
decides **8/113** and Z3 4.13.3 decides **8/113** — *different* sets, DISAGREE=0:
both get 6 (compose.p2/.s2, mobiledevice×3, simple), axeyum uniquely decides
`string1x8.3` (z3 times out @20.5s) + `string1x8.6`, z3 uniquely decides
`compose.p3`/`compose.s2_nr4`, and the other ~105 defeat **both** (the
"defeats-even-kissat" reduction-bound bulk). So the destination-2 gate is best
read as **per-fragment milestones** — on *this* corpus we are at parity with Z3,
both hard-capped — rather than a monolithic "Z3 sweeps everything" chasm. The
earlier "Z3 decides essentially all in ~1s" premise was never measured and is
false at second-scale (corrected; baselines committed under
`bench-results/baselines/qf-bv-p4dfa-*`). Frame progress as *which fragments
reach parity*, corpus by corpus, not a single global percentage.

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

## Product Destinations (What "Done" Means)

The technical ladder above is the means; these are the product endpoints, and
what each *actually* requires (so we don't mistake feature-coverage for arrival).

### Destination 2 — complete solver replacement (Z3 / cvc5 class)

A drop-in alternative a real consumer would choose. Requires, beyond the
foundation:

- **Performance, the gate.** A real CDCL(T) loop (theory propagation, conflict
  learning across theories), encoding/preprocessing engineering, and a
  competitive SAT core. *This is the binding constraint* — today the pure-Rust
  path decides only a small slice of real public QF_BV where Z3 decides nearly
  all. Measured against an angr+Z3-style baseline, not feature checkboxes.
- **Theory breadth.** Floating point (`QF_FP`), strings/sequences/regex,
  datatypes, nonlinear arithmetic (NIA/NRA), unbounded `LIA`/`LRA` via a real
  simplex + branch-and-bound (the bounded bit-blasting today is a stand-in), and
  production quantifier instantiation (E-matching + MBQI).
- **Surface + robustness.** Full SMT-LIB 2 (incl. `get-value`/`get-unsat-core`/
  `get-proof`, options, optimization), incremental at scale, and validation on
  the SMT-COMP corpora — not a handful of families.

### Destination 3 — Lean / angr as first-class functionality

- **angr/unicorn class.** A binary/IR frontend (lifting, CFG recovery), a
  realistic memory model, and symbolic execution + concrete emulation as
  first-class APIs driving the solver for **constrained program optimization and
  verification**. Today's `tests/symbolic_execution*.rs` is a hand-built
  register VM for testing — the *shape* of the consumer, not the product.
- **Lean class.** Kernel-checkable proofs above the clausal layer (the evidence
  envelope grown into a proof term + an independent Rust kernel, cf. nanoda),
  proof-assistant interop (export obligations / import checked rules, cf.
  lean-smt/Alethe), and eventually dependent-type proving. The evidence thesis
  already in the foundation is the seam this grows along.

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
