# Scalable bit-blast-reduction certification (track a) — design and obstacle

Status: **open research program.** This note records, precisely, what
"machine-checked `QF_BV` `unsat` end to end" requires, why it is not a bounded
code increment, and the concrete path to it — so a future session can pick it up
deliberately. Everything *bounded* in track (a) is done (see below).

## What is already certified

The pure-Rust `QF_BV` `unsat` pipeline is `term → AIG → CNF → SAT → DRAT`. Two
trust gaps exist; here is their current status.

- **Clausal layer (CNF `unsat`): certified.** `axeyum_cnf::solve_with_drat_proof`
  emits a DRAT proof that the in-tree `check_drat` kernel verifies. This is the
  "trusted small checking" anchor for the clausal layer.
- **Small-instance term level: certified, reduction-free.**
  `certify_qf_bv_by_enumeration` evaluates the original term over the whole finite
  symbol domain (≤ a bit budget) using only the `axeyum-ir` evaluator, and the
  `Evidence` envelope (`Evidence::UnsatTermLevel`) attaches this for small `unsat`
  instances. It trusts neither the bit-blaster, CNF encoder, nor SAT solver, so it
  closes **both** gaps for the tractable case.

## The remaining gap (the open program)

For *large* instances the **reduction** `term → CNF` is trusted, not checked. A
buggy bit-blaster that adds a spurious constraint could turn a satisfiable term
into an unsatisfiable CNF; the DRAT would faithfully certify the (wrong) CNF
`unsat`, and we would wrongly report the term `unsat`. So a sound *scalable*
`unsat` certificate must establish **term/CNF equisatisfiability** independently.

Split the reduction:

1. **CNF ⟺ AIG (Tseitin).** Closable by *construction*: a simple reference
   Tseitin encoder (3 clauses per AND gate, roots asserted) is a known
   equisatisfiability-preserving transform, sound by inspection. Using it on the
   certified path discharges this gap with no checker. (The fast encoder's
   sparse-CNF optimizations are *not* needed on the certified path.)

2. **AIG ⟺ term (bit-blasting).** This is the hard gap, and it is **circular** to
   discharge cheaply:
   - A *per-instance structural* check ("the AIG node for term bit `i` is the
     correct gadget over the children's bits") requires the checker to know each
     operator's bit-level gadget — i.e. the checker *is* a bit-blaster. Re-running
     the *same* gadget builder checks nothing (it is deterministic); using a
     *different* reference gadget makes the two AIGs structurally distinct, so
     equality no longer holds and confirming agreement becomes an
     equivalence/miter **SAT** problem — which is what we were trying to certify.
   - A *per-instance miter* (`fast-AIG-bit XOR reference-AIG-bit`, refuted by the
     DRAT core) is sound and scalable, **but** its soundness rests on trusting the
     *reference* bit-blaster, which for arithmetic gadgets (ripple-carry adder,
     shift-and-add multiplier, restoring divider) is **not** obviously correct.
     "Trusted by simplicity" does not hold for arithmetic, so this only moves the
     trust, it does not eliminate it.

   The non-circular options both leave the bounded-increment regime:
   - **(A) Formally verify the gadgets.** Prove, *width-parametrically* (by
     induction on the bit-vector width), that each `axeyum-bv` gadget computes its
     SMT-LIB bit-level semantics. This is a proof-assistant effort (Lean/Coq/ACL2),
     i.e. a verified-bit-blaster — months-scale, and the genuine "scalable
     certification."
   - **(B) Trusted reference + miter.** Accept a maximally-simple reference
     bit-blaster as the spec (its assurance bounded by exhaustive small-width
     testing, the same level the fast one already has), and per instance refute
     the miter with the DRAT core. Cheaper to build, but the assurance is a
     *differential* between two tested-not-proved encoders, not a proof.

## Recommended path

Option **(B)** is the practical, in-Rust, sound-modulo-tested-reference step that
*advances* (not closes) scalable certification, and it fits the project's
"two independent procedures cross-validating" pattern (cf. the Fourier–Motzkin vs
δ-simplex LRA engines, and the rustsat-batsat vs proof-core SAT differential).
Concrete sub-increments, each green:

1. A second, deliberately-simple reference bit-blaster (`axeyum-bv`, separate
   module) for the supported operator set, gadget by gadget, each exhaustively
   cross-checked against the evaluator at small widths (as the existing gadgets
   are).
2. A per-instance **miter certificate**: build `fast ⊕ reference` over the term
   bits, bit-blast + Tseitin + `solve_with_drat_proof`, and require the miter
   `unsat` with a `check_drat`-verified proof. Bundle it with the original
   `unsat` DRAT as the end-to-end artifact.
3. Wire it into `produce_qf_bv_evidence` as a stronger `unsat` evidence kind for
   instances above the enumeration budget (the term-level cert stays primary for
   small instances).

Option **(A)** (a verified bit-blaster) remains the eventual fully-trusted form
and is the genuine open research frontier of the proof-carrying arm — it is the
one roadmap item that is intrinsically not a bounded code increment.

## Delivered: scalable faithfulness *checking* (the differential layer)

Ahead of full certification, a **scalable, sound bug-detector** for the
reduction is implemented: `axeyum_solver::check_qf_bv_faithfulness` samples
random assignments and confirms the bit-blasted AIG (`axeyum-bv`'s
`evaluate_roots`) evaluates to the **same value** as the original term (the
`axeyum-ir` evaluator). It is the differential complement of model replay: model
replay checks the reduction is sound *for the found `sat` model*, while this
checks the reduction faithfully computes the term *on independent random inputs*
— the regime that matters for `unsat`, where no model exists to replay. A
disagreement is a *definitive* faithfulness bug with a concrete counterexample
(sound bug-detection); agreement across many samples is real, scalable evidence
the reduction did not distort the term. It is deterministic (seeded), so it is
exactly reproducible. It is **not** a proof (sampling cannot certify the absence
of a divergence), so it does not close the gap — it is the cheap, scalable
assurance layer that sits below the staged path (B → A) and would catch most
real bit-blasting bugs long before a verified bit-blaster exists. Tests confirm
faithful arithmetic/bitwise and division/shift terms agree over hundreds of
samples; integer terms report `Unsupported`.

## What "done" means for this note

The bounded slice of track (a) — reduction-free term-level certification for
small instances — is implemented and wired into the evidence envelope, and a
scalable differential *faithfulness check* (above) guards the reduction at large
sizes. The remaining *certification* form is recorded here as an open program
with a concrete, sound, staged path (B → A). No part of it should be faked with
an unsound shortcut: a wrong `unsat` would betray the project's core identity.
