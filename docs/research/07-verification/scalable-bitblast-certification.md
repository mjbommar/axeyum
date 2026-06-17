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

## Delivered: path (B) — the independent-reference miter *certificate*

`axeyum_solver::certify_bitblast_by_miter` implements path (B) for the
bitwise/Boolean/`eq`/`ite` fragment: it builds **one** AIG holding both the
production bit-blasting (`axeyum-bv`, copied in over shared symbol-bit inputs)
**and** a separately coded reference bit-blaster, forms the miter
`OR over output bits (fast_bit XOR ref_bit)`, Tseitin-encodes it, and refutes it
with `solve_with_drat_proof` + `check_drat`. An `unsat` miter is an **exhaustive,
DRAT-checked** proof that the two encodings agree on *every* input — a real
certificate (not sampling) that the production reduction is faithful on that
fragment; a `sat` miter is a faithfulness bug with a witness. It is sound modulo
trust in the reference, which is independent code, so a production bug surfaces as
miter `sat` (the two-independent-procedures pattern, applied to bit-blasting).
Operators the reference does not yet cover (arithmetic, shifts, concat/extract,
extensions) return `NotCertifiable` and fall back to the sampled check. The
`Certified` outcome carries the auditable `(dimacs, drat)` artifact.

The covered fragment now includes **arithmetic** (`bvadd`/`bvsub`/`bvneg`/`bvmul`
— ripple-carry adder, two's-complement, shift-and-add), **all comparisons**
(unsigned via the subtractor's borrow, signed via sign analysis), and **shifts**
(`bvshl`/`bvlshr`/`bvashr` — barrel shifter with SMT-LIB over-shift totality), in
addition to the bitwise/Boolean/`eq`/`bvcomp`/`ite` base. Each reference gadget is
textbook and *independent* of `axeyum-bv`'s code; the miter being `unsat`
(DRAT-checked) for width-4 add/sub/mul/shift/comparison queries confirms the two
agree exhaustively — both certifying the production reduction and validating the
reference.

The reference now covers the **entire supported `QF_BV` operator set**: the
structural operators (concat/extract, zero/sign extension, rotates), unsigned and
signed division/remainder/modulo (a restoring divider with SMT-LIB totality, the
signed forms as sign wrappers), in addition to bitwise/Boolean/`eq`/`bvcomp`/`ite`/
arithmetic/comparisons/shifts. So **path (B) is complete**: any pure-`QF_BV`
query's production bit-blasting is certifiable faithful by a DRAT-checked miter
against the independent reference (only uninterpreted-function `apply` and
quantifiers — which are not bit-blasted — fall outside).

**End-to-end composition.** `certify_qf_bv_unsat_end_to_end` composes the two
DRAT-checked proofs into a single term-level `unsat` certificate: the term equals
its AIG (miter, modulo the reference), the AIG equals the CNF (Tseitin, by
construction), and the CNF is unsatisfiable (DRAT). This is *scalable,
machine-checked, end-to-end* `QF_BV` `unsat` — the goal of track (a) — realized
via path (B); a production bit-blast that diverges from the reference is reported
as a soundness alarm.

**Reference grounded in the evaluator.** The independent reference is itself
exhaustively checked against the trusted `axeyum-ir` ground evaluator at small
width (width 3, all inputs) for *every* covered operator (the
`reference_grounding` tests). So the reference's correctness is anchored in the
**evaluator** — the same spec that anchors `sat` model replay — not in the
production bit-blaster. The trust chain is now: reference ≡ evaluator (exhaustive,
small width) ∧ reference ≡ production (miter, DRAT-checked, any width) ⟹ production
faithful; the only residual gap is a width-specific bug that is simultaneously
*correct at width ≤ 3*, *wrong at the queried width*, and *identical in two
independently written code paths* — which path (A) closes.

**Status — trust parity reached.** Path (B), with the reference grounded in the
evaluator, brings `QF_BV` `unsat` certification to the **project's uniform trust
standard**: every trusted component — the ground evaluator, `check_drat`, and now
the reference bit-blaster — is *exhaustively tested*, none formally proven. A
width-parametric **verified** bit-blaster (path A) would make the bit-blaster
*more* trusted than the evaluator and the DRAT kernel themselves, exceeding the
bar applied everywhere else in the framework. It is therefore recorded as a
distinct, optional, proof-assistant-scale research item (Lean/Coq) rather than a
gap in the framework's own trust model — the genuine fully-trusted frontier, not
a bounded code increment.

## Delivered earlier: scalable faithfulness *checking* (the differential layer)

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

## The external-checker route (Alethe/Carcara, T3.3.1) — confirmed contract

Path (B) above certifies the reduction *in-house* (a DRAT-checked miter against an
independent reference). A **complementary** route is to emit a full QF_BV `unsat`
proof in the **Alethe** format and have the external **Carcara** checker validate
it end to end — the same third-party-referee assurance now in place for EUF, LRA,
and the clausal resolution layer (see `crates/axeyum-solver/tests/carcara_crosscheck.rs`).
This route is **not** a bounded increment; this section records the exact Carcara
contract — *empirically confirmed against the built binary* — so the implementation
proceeds without re-deriving it.

**Carcara's bitblast rules (confirmed).** Carcara checks per-operator `bitblast_*`
steps whose conclusion is a definitional equality `(= <op-term> <bbterm>)` where the
bit-level term uses two special operators:

- `@bbterm` — bundles the per-bit Boolean terms: `(@bbterm b0 b1 … b{n-1})`, LSB
  first. (Carcara operator `BvBbTerm`, spelled `@bbterm`.)
- `(_ @bit_of i) x` — the indexed bit-extraction of bit `i` of a bit-vector term
  `x`. **The spelling is `@bit_of`, not `@bit`** (Carcara `ParamOperator::BvBitOf`);
  `@bit` is rejected by the parser.

Rule names (from `references/carcara/.../checker/shared.rs`): `bitblast_const`,
`bitblast_var`, `bitblast_and`/`or`/`xor`/`xnor`/`not`, `bitblast_comp`,
`bitblast_ult`/`slt`, `bitblast_add`/`mult`/`neg`, `bitblast_equal`,
`bitblast_extract`/`concat`/`sign_extend`. Each rebuilds the expected `@bbterm`
left-to-right from the operands' bits and checks structural equality, e.g.
`bitblast_var` for a width-2 `x` accepts exactly

```
(step s (cl (= x (@bbterm ((_ @bit_of 0) x) ((_ @bit_of 1) x)))) :rule bitblast_var)
```

This step **parses and checks valid** against the binary (the only remaining error
on a lone step is "proof does not conclude empty clause" — Carcara requires the
proof to derive `(cl)` to be a refutation, exactly as for the resolution layer).

**What the implementation needs (the L-sized body):**

1. **IR extension.** `axeyum_cnf::AletheTerm` (`Const | App`) cannot represent a
   list-headed/indexed application like `((_ @bit_of 0) x)` — its `App` head is a
   plain `String` and the parser requires an atom head. Add an indexed-operator
   representation (parse + write + `key()` round-trip) so `@bit_of`/`@bbterm` are
   first-class. `@bbterm` itself is an ordinary `App("@bbterm", …)`; only the
   indexed `(_ @bit_of i)` head needs new structure.
2. **Per-operator emitter.** Mirror Carcara's left-to-right `@bbterm` construction
   for each supported operator, driven by `axeyum-bv`'s lowering (the bits axeyum
   already computes). Carcara holes `bvudiv`/`bvurem`/shifts → emit `hole` for the
   structural step and attach axeyum's **miter certificate** (path B above) as the
   side justification — the place axeyum *leads* Alethe, which has no div/rem rule.
3. **Bridge to the resolution refutation (already validated).** The top-level
   predicate (e.g. an asserted `bvult`/equality) bitblasts to a Boolean formula;
   Tseitin CNF-introduction steps (`and_pos`/`or_pos`/…, already supported by
   `check_alethe`) connect it to the CNF variables, and the
   `lrat_to_alethe` resolution layer (now Carcara-`valid`, T3.3.3) closes to `(cl)`.

This is the third-party-checked analogue of path (B): where (B) trusts an in-house
reference and refutes a miter with `check_drat`, this emits a proof an *external*
checker re-derives. The two are independent and mutually reinforcing.

## What "done" means for this note

The bounded slice of track (a) — reduction-free term-level certification for
small instances — is implemented and wired into the evidence envelope, and a
scalable differential *faithfulness check* (above) guards the reduction at large
sizes. The remaining *certification* form is recorded here as an open program
with a concrete, sound, staged path (B → A), plus the external-checker
(Alethe/Carcara) route with its confirmed contract above. No part of it should be
faked with an unsound shortcut: a wrong `unsat` would betray the project's core
identity.
