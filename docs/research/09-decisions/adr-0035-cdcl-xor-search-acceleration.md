# ADR-0035: CDCL(XOR) Search Acceleration with a Ledgered Trust Hole

Status: accepted

Date: 2026-06-17

## Context

The curated QF_BV performance wall is multiplier-equivalence: bit-blasted
multiplier circuits have exponential resolution lower bounds, so the CDCL search
(whose proof system is resolution) cannot crack them cheaply
([multiplier-sat-wall-and-algebraic-paths.md](../05-algorithms/multiplier-sat-wall-and-algebraic-paths.md)).
The diagnosed lever is **in-search Gaussian elimination over the XOR (parity)
structure** the multiplier/adder CNFs carry — CDCL(XOR), as in CryptoMiniSat.

The static-preprocessing form of this idea is measured-exhausted on the curated
slice: across 20 firing files, 12 908 recovered XOR gates yield 1 implied unit and
351 equalities, and the equalities concentrate on AC-structured instances the
canonicalizer already targets, not the `mulhs*`/`stp_samples`/`calypto` unknowns.
The remaining power is only reachable by reasoning about the XOR system **as the
search assigns variables** (the nonlinear AND-gate partial products only the
search fixes).

The algorithmic foundation is built and brute-force-validated in `axeyum-cnf`:
`gf2` (GF(2) Gaussian), `xor_extract` (sound gate recovery), `xor_search`
(`xor_implications` — XOR propagation under a partial assignment → implied
literals + conflicts with reasons), and `xor_dpll` (a correctness-first XOR-aware
decider, agreeing with a brute-force oracle and `rustsat-batsat` over 700 random
instances with zero disagreement).

Integrating this into the **proof-producing** CDCL core raises one hard question.
`solve_with_drat_proof` emits a DRAT certificate, and the project's identity is
*untrusted search, trusted small checking*: every `unsat` is independently checked
or an explicit, ledgered trust hole (Hard Rules; the
[trust ledger](../08-planning/trust-ledger.md), ADR-0031). But an XOR-derived
reason clause is **generally not RUP** — that is precisely why Gaussian reasoning
beats resolution — so emitting it as a `DratStep::Add` would produce a proof the
independent `check_drat` correctly rejects. There is no cheap fix inside DRAT
(`check_drat` is RUP+RAT only).

## Decision

Adopt **search-only XOR acceleration with a ledgered trust hole**, exactly
mirroring how ADR-0007 admitted `rustsat-batsat`'s `unsat` before a proof route
existed:

1. XOR reasoning (`xor_implications`, later the incremental watched-row matrix)
   participates in the CDCL search as a theory propagator interleaved with clause
   unit propagation.
2. When a refutation uses an XOR-derived reason, the solver **does not emit a DRAT
   proof** for it (no false certificate) and instead records a new trust-ledger
   entry **`TrustId::XorGaussian`** on that `unsat`. The assurance backing the hole
   is the brute-force-validated soundness of `xor_search`/`gf2`
   (conflict-soundness + implication-soundness over all completions).
3. **`sat` results carry no trust cost**: the model replays against the original
   terms regardless of how the search found it (the existing soundness gate). XOR
   acceleration on satisfiable instances is fully sound today.
4. The hole is **demotable**, and the demotion path is named: an algebraic
   (Nullstellensatz/PAC) certificate for the XOR steps, which is the easy
   sub-case of the path-3 algebraic engine and later subsumes into it — the same
   trusted→checked arc `BitBlast`/`Tseitin`/`SatRefutation` took to Alethe.

`TrustId::XorGaussian` is added to `trust.rs` (the 6th hole), the golden
trust-ledger test, and `trust-ledger.md`. The default build is unaffected: the
accelerator is opt-in until measured, and it adds **no** C/C++ dependency (pure
Rust, reusing the in-tree `gf2`/`xor_search`).

## Consequences

- **Positive.** Unblocks the only diagnosed technique that can reach the curated
  multiplier-equivalence unknowns, while keeping the Hard Rule intact: never a
  wrong `unsat`, only an explicit ledgered trust. `sat` stays fully checked. The
  XOR engine is reused, not re-implemented. The trust hole is countable and has a
  concrete demotion route.
- **Negative / cost.** A 6th trust hole until the PAC certificate lands — the
  trusted base grows before it shrinks. XOR-assisted `unsat` is lower-assurance
  than the DRAT/LRAT/Alethe-checked routes (mitigated by the brute-force
  validation and the differential against batsat). The first production
  integration touches the proof-producing core, a soundness-critical area.
- **Scope guard.** This ADR authorizes *search acceleration + the trust hole*, not
  a proof system. The correctness-first `xor_dpll` decider validates soundness;
  the production-core integration (1-UIP learned clauses, watched-row matrix) is
  the implementation that follows, measured on the curated slice with the
  `DISAGREE=0` invariant before it is enabled by default. Enabling it by default
  is a separate, measured decision.

## Alternatives considered

- **Extended DRAT/DPR for XOR (PR/SR clauses, or recording row operations).**
  Heavy, and the in-tree `check_drat` does not implement it. Deferred.
- **No trust hole — pure-resolution re-certification of XOR-assisted `unsat`.**
  Circular: a resolution re-check cannot certify what required Gaussian reasoning.
- **Stay preprocessing-only.** Measured-exhausted on the curated wall (see
  Context); forecloses the lever entirely.
