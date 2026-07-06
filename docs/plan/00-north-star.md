# 00 — North star: what "Z3 + Lean parity" means

This file pins down the goal so progress is measurable and "done" is not a
moving target. It is the answer to "what are we actually building, and how do we
know when a piece is finished."

## The one-sentence identity

**Untrusted fast search, trusted small checking** — a complete framework for
general reasoning that finds answers fast with whatever heuristics work, and
backs every definitive answer with a small, independent, machine-checkable
certificate. Z3 is the performance/feature yardstick; Lean is the
proof-checking yardstick.

## Definition of done — Z3 parity

Z3 is ~688k lines of C++ (`references/z3/src`); cvc5 ~512k. "100% parity" is not
a single deliverable and not a single-session target — it is a destination
reached fragment by fragment. A fragment is at **Z3 parity** when:

1. **Feature coverage** — axeyum decides the same query class Z3 does
   (operators, sorts, commands), end to end (IR → decision procedure → model /
   proof → SMT-LIB I/O).
2. **Soundness + completeness** — on the decidable fragment it never returns a
   wrong answer and returns `unknown` only where Z3 also would (resource limits),
   not because of missing reasoning.
3. **Measured performance** — on a committed real-corpus slice, axeyum's PAR-2
   is within a target factor of Z3's (initial bar: same order of magnitude;
   stretch: competitive), measured **head-to-head** by
   [P4.5](track-4-usecases-frontend/P4.5-benchmarking.md). No parity claim
   exists without this number.
4. **Honest unknown on the undecidable** — for semidecidable/undecidable
   fragments (full NRA without CAD, general quantifiers), parity means matching
   Z3's *practical* decide-rate and heuristics, with `unknown` first-class. We do
   not claim to "solve the halting problem"; we claim to match the engineering.

## Definition of done — Lean parity

"Lean parity" means axeyum is a proof-producing solver whose proofs a
**Lean-grade kernel** accepts:

1. Every `unsat`/`valid` over a supported fragment emits a proof object.
2. The proof is checked by a **small, independent** checker — first the Rust
   **Carcara** Alethe checker (and an in-tree subset), ultimately an in-tree
   Lean-style kernel (`axeyum-lean-kernel`, modeled on `nanoda_lib`).
3. The **trusted base is enumerable and shrinking**: every reduction step
   (bit-blast, Ackermann, read-over-write, int-blast, fp→bv) is either certified
   or listed in the [trust ledger](track-3-proof-lean/P3.0-trust-ledger.md) with
   a pedantic level. "Modulo trusted reduction" becomes a countable list that
   goes to zero.
4. **Proof-assistant interop**: axeyum's proofs can be reconstructed as Lean
   proof terms (the lean-smt-style bridge), so axeyum can serve as a Lean tactic
   backend.

## Definition of done — the verified-systems trajectory (Track 5)

The **application-level** destination, adopted as first-class by
[ADR-0056](../research/09-decisions/adr-0056-verified-systems-track.md)
(2026-07-06): `Rust + axeyum` as a natural, low-ceremony way to build systems
and network-protocol code — the seL4-inspired goal — whose safety- and
correctness-critical core carries machine-checkable evidence. Z3 parity and
Lean parity are the *capability* yardsticks; this is what the capabilities are
**for**. Track 5 v1 is done when:

1. **IR-level front end** — the MIR + LLVM IR reflection consumes real `cargo`
   build artifacts (not curated fixtures), with contracts making calls modular
   and loops bridged to the unbounded engines.
2. **The kernel obligation families ship** — panic-freedom (overflow /
   division / bounds, from the compiler's own checks), constant-time
   (2-safety), cross-IR/cross-profile translation-validation, bounded
   memory/page-table invariants, and protocol-FSM refinement — each
   push-button, each with replayed or certified evidence.
3. **The fuzz loop is one harness** — proofs where decidable, solver-witness
   seeds and directed fuzz where not, the three outcomes never conflated.
4. **Measured on someone else's code** — at least one external Rust systems
   target with a committed scoreboard result (module verified or bug
   found+reproduced), DISAGREE=0, wall-times recorded.

What Track 5 never claims (the honesty boundary): seL4 parity, whole-kernel
interactive functional correctness, or source-level Rust semantics — we verify
what the compiler produced, post-borrowck and post-optimization, and the
cross-IR equivalence proofs are what let us trust both views at once. Plan:
[`track-5-verified-systems/`](track-5-verified-systems/README.md).

## What is already true (the starting line, 2026-06-15)

- Broad decidable+arithmetic foundation, ~63k LoC Rust, pure (no C/C++ default).
- Independently checked today: QF_BV clausal `unsat` (DRAT, `UnsatProof::recheck`),
  the bit-blast reduction (exhaustive miter, `EndToEndUnsatOutcome::recheck`),
  QF_LRA `unsat` (Farkas, `FarkasCertificate::verify`), all `sat` (model replay),
  small QF_BV (exhaustive enumeration).
- Everything reached through a non-bit-blast reduction (arrays, UF, datatypes,
  LIA, FP, strings) is "checked **modulo trusted reduction**."
- No measured Z3 head-to-head where axeyum decides a large slice at competitive
  PAR-2. The strongest data point: ~3× slower than Z3 on one shared hard QF_BV
  instance; ~90% decided on an easy family (oracle disabled).

Full inventory: [`references/axeyum-current-state.md`](references/axeyum-current-state.md).

## The two load-bearing fronts (everything else serves these)

1. **Measured performance** (Track 1, gated by P4.5). Highest single lever:
   **SAT inprocessing (bounded variable elimination)** + **word-level
   preprocessing** on the bit-blasted path.
2. **Reduction certificates** (Track 3). Critical path: **Alethe emitter**
   (P3.2) → Carcara-checked QF_BV (P3.3) → per-reduction proofs (P3.5) → Lean.

## The two keystones (build once, unlock many)

- **Incremental e-graph + CDCL(T) loop** (P1.4 + P1.5): the shared equality bus
  and theory-propagation loop that nearly every lazy theory and all quantifier
  work in Track 2 depends on.
- **Alethe term/proof IR + emitter** (P3.2): the Rust-checkable, BV-shaped,
  Lean-on-ramp proof format the whole proof track depends on.

## Legends used throughout

**Size:** `S` ≈ ≤2 days · `M` ≈ ~1 week · `L` ≈ ~2–4 weeks · `XL` ≈ multi-month.

**Status** (tracked in [STATUS.md](../../STATUS.md)): `TODO` · `WIP` · `DONE` ·
`BLOCKED`.

**Assurance** (capability ledger): `checked` (independent per-query certificate) ·
`validated` (differential vs oracle) · `sound-incomplete` (`unknown`-safe) ·
`experimental`.

## Non-negotiables (these never bend, even for parity)

- No C/C++ in the default build; `unsafe_code` denied; determinism is a public
  promise; `unknown` is never an error; never a wrong `unsat`; build at `-j4`;
  no 41GB corpus sweeps. (Full list in [PLAN.md](../../PLAN.md).)
