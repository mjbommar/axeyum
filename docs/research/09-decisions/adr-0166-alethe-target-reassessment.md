# ADR-0166: Reassess the Alethe proof-format bet against CPC

Status: proposed
Date: 2026-07-15

## Context

P3.2 (Alethe term/proof IR + emitter) is marked **`[critical path]`** in
`docs/plan/track-3-proof-lean/README.md:17`, and P3.7 (Alethe→Lean
reconstruction) is Track 3's declared **capstone** and the operational definition
of "Lean parity" (`docs/plan/01-dependency-dag.md:71-72,116`). The chain is
`P3.0 → P3.2 → P3.3 → P3.5 → P3.6 → P3.7`, and P3.2 gates the rest.

The Alethe choice was made when the research question "which proof format?"
closed (`docs/research/08-planning/research-questions.md`, Horizon section). Two
facts surfaced during the prover-track research sweep
([`docs/prover-track/research/03-atp-itp-seam.md`](../../prover-track/research/03-atp-itp-seam.md))
that the original decision does not appear to have weighed, and that bear
directly on whether the keystone is aimed correctly:

1. **`lean-smt` uses CPC, not Alethe.** The Lean 4 SMT integration (Mohamed et
   al., CAV 2025) targets cvc5's **CPC**; the paper does not present Alethe as a
   target. cvc5's own documentation notes that "the concrete syntax of CPC is very
   similar to Alethe. However, the proof rules used by these two formats are
   different."
2. **cvc5's Alethe output does not cover bit-vectors.** Its Alethe coverage is
   EUF plus parts of arithmetic and quantifiers.

The resulting landscape reads: **Alethe is Isabelle's format; CPC is Lean's.**

This matters because of where axeyum's strength actually is. QF_BV is our
strongest fragment (~2× Z3 on the 13,462-row glaurung tranche, `STATUS.md:736-741`;
QF_ABV 169/169 dominant). So the current plan aims **at Lean**, **through the
format Lean's own SMT tactic declined**, **in a fragment that format does not
cover**, while our comparative advantage sits in exactly that fragment.

This ADR does not assert the bet is wrong. It asserts the bet is currently being
**held by inertia rather than by decision**, on a keystone, and that this is not
an acceptable state for a critical-path item.

## Decision

**Re-open the proof-format question for the Lean route before further P3.2/P3.3
investment, and record the outcome as an accepted ADR superseding this one.**

Concretely, before P3.2 proceeds past its current slice:

1. Verify both findings against primary sources (the CAV 2025 lean-smt paper and
   cvc5's current proof-format documentation). They came from a single research
   sweep and have not been independently confirmed by this project.
2. Determine whether Alethe's BV gap is a *cvc5 output* limitation or an *Alethe
   format* limitation. **This is the crux.** If the format can express BV and only
   cvc5 declines to emit it, axeyum emitting BV Alethe is novel but not blocked,
   and the bet may stand.
3. Choose explicitly among the alternatives below and write it down.

## Evidence

- `docs/prover-track/research/03-atp-itp-seam.md` — the CPC/Alethe finding, the
  BV-coverage gap, and the Isabelle-vs-Lean split.
- `docs/plan/track-3-proof-lean/README.md:17` — P3.2 marked `[critical path]`.
- `docs/plan/01-dependency-dag.md:71-72,116` — the Lean-parity chain and P3.7 as
  capstone.
- `STATUS.md:736-741` — QF_BV at ~2× Z3, our strongest measured fragment.
- `bench-results/DOMINANCE.md` — QF_ABV 169/169 dominant with Lean unsat 85/85;
  the fragment where a Lean route already demonstrably works.
- Related: `bv_decide` (OOPSLA 2025) already occupies QF_BV-in-Lean via verified
  reflection + LRAT, with its bottleneck at **kernel reduction speed, not solve
  time**. This is relevant to option 1 below: an LRAT-shaped route competes where
  a proof-*reconstruction* route may not need to.

## Alternatives

1. **Retarget the Lean route** — to CPC, to a Lean-native reconstruction, or to
   LRAT-carried BV. Follows Lean where Lean actually is. Cost: P3.2's emitter work
   partially retargets; the Alethe IR itself may survive as an internal format.
2. **Keep Alethe, aim it at Isabelle.** Alethe is Isabelle's format and Isabelle
   is a real consumer with a real user base. This *changes the customer*, not the
   plan — and it would make "Lean parity" the wrong name for the capstone.
3. **Keep Alethe for Lean as a deliberate, eyes-open bet** — e.g. because we
   intend to emit BV Alethe that cvc5 does not, making us the format's most
   capable producer. Defensible, but it must be written down as a choice with its
   reasoning, not inherited.
4. **Do nothing.** Rejected. A critical-path keystone held by inertia is the
   failure mode this ADR exists to stop.

## Consequences

- **Easier:** P3.7's value becomes assessable rather than assumed. If option 1 is
  taken, the Lean route aims where Lean's own tooling aims.
- **Harder:** P3.2 is mid-flight (`STATUS.md:2754`, WIP). Re-opening a keystone
  mid-slice has a real cost, and that cost is the argument for deciding *now*
  rather than after P3.3/P3.5 build on it.
- **Revisited when:** the three steps above complete. This ADR should be
  superseded by an accepted decision, not left in `proposed`.
- **Scope note:** this ADR does not touch the DRAT/LRAT clausal layer (ADR-0011,
  ADR-0012) or the in-tree kernel (ADR-0036). Those stand regardless.

## Provenance

Surfaced by the prover-track research sweep
([`docs/prover-track/`](../../prover-track/README.md)), which recommended
**against** building a prover but produced this finding and the `sat`-trust gap as
byproducts worth more than the question that prompted them. Filed by that track
rather than deferred, because "urgent, and owned by nobody" is how a keystone stays
wrong.
