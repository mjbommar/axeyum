# ADR-0047: Craig interpolation as a verified proof transform

Status: accepted
Date: 2026-06-22

## Context

Craig interpolation is a first-class feature column in Z3 and cvc5 that axeyum
lacked, and it is the lemma engine the CHC/PDR engine
([P4.6](../../plan/track-4-usecases-frontend/P4.6-chc-horn.md)) will consume to
generalize blocked counterexample frames. The phase plan
([P3.8](../../plan/track-3-proof-lean/P3.8-interpolation.md)) calls for it.

The open question this closes: **how does axeyum produce interpolants without
adding a new *trusted* component?** axeyum's identity is "untrusted fast search,
trusted small checking" — an interpolant produced by a separate bespoke
procedure would be a new thing to trust. But axeyum already produces *checked*
refutations (Farkas certificates for LRA, congruence-closure explanations for
EUF), so an interpolant can be read off the proof we already trust and then
re-verified independently.

## Decision

**Interpolants are derived as a transform over an already-checked refutation and
are themselves re-verified by independent entailment/`unsat` checks before being
returned; any candidate that fails a check is declined (`Ok(None)`), never
returned unverified.** A produced interpolant is therefore sound by construction
of the checker, not by trust in the generator — the generator may be partial.

Concretely:

- **LRA (`lra_interpolant`).** Given an unsat conjunctive `A ∧ B`, take the
  self-checked Farkas certificate (multipliers `λ` over the normalized atoms,
  [ADR-0015](adr-0015-linear-real-arithmetic.md)) and form
  `I := (Σ over A-side atoms λ_i · atom_i) ⋈ 0` (strict iff a used A-atom is
  strict). `A ⇒ I`, `I ∧ B ⇒ ⊥`, and the shared-vocabulary condition all hold by
  construction (A-only variables cancel because the full combination cancels all
  variables and B contributes zero to them). `FarkasCertificate` gained a
  `vars: Vec<SymbolId>` field so the dense atom indices map back to typed terms.

- **EUF (`qf_uf_interpolant`).** Given an unsat `A ∧ B` of equality/disequality
  literals, find the violated disequality `s ≠ t`, explain `s = t` over the
  congruence closure ([ADR-0013](adr-0013-uninterpreted-functions.md) /
  the e-graph `explain_steps`), thread the path, color each edge by partition
  (`Input` by asserting side; `Congruence` by the common color of its argument
  sub-proofs), and summarize the maximal segments opposite the disequality into
  shared-term equalities — lowering a non-shared congruence boundary into its
  argument equalities. `I = ⋀ summary` (diseq in B) or `¬⋀ summary` (diseq in A);
  an empty summary is the degenerate `⊤`/`⊥`.

- **Verify-before-return contract (both).** The three Craig conditions are
  re-checked by the independent in-tree deciders (`check_with_lra` / `check_qf_uf`)
  plus a vocabulary set check; any `Unknown`/failure declines. Overflow in the
  LRA combination declines. This makes a deliberately *partial* generator sound:
  unsupported shapes (mixed-color EUF edges, non-shared input boundaries,
  non-conjunctive structure, a non-disequality conflict) return `Ok(None)`.

- **Surface.** `Solver::interpolant(arena, a_indices)` partitions the active
  assertions and dispatches LRA → EUF. The SMT-LIB `(get-interpolant)` *parse*
  surface is deferred (the `axeyum-smtlib` parser is a coordinated crate); the
  solver-side driver can follow without it.

## Evidence

- 9 LRA integration tests + 10 EUF integration tests, each *independently*
  re-checking the three Craig conditions (or, for `⊤`/`⊥`, the ground value plus
  the side-alone `unsat`). Cover: shared/transitive, A-only-variable cancellation,
  strict, rational coefficients, congruence lowering, nested congruence, shared
  function, sat-declines, and the degenerate one-side-unsat cases.
- The LRA construction reuses the Farkas self-check (`FarkasCertificate::verify`);
  the EUF construction reuses the e-graph explanation already used by the Alethe
  EUF emitter.

## Alternatives

- **A bespoke interpolating solver** (separate search). Rejected: it adds a new
  trusted component and duplicates the decision procedures, against the project's
  trusted-small-checking identity.
- **Trusting the generator without re-verification.** Rejected: a generator bug
  would yield a wrong interpolant silently; the re-check is cheap relative to the
  solve and makes partiality safe.
- **Completing EUF interpolation to McMillan's full algorithm now.** Deferred:
  the verify-guarded partial generator covers the common shapes soundly; the full
  algorithm (arbitrary mixed-color summarization, predicates, multiple conflicts)
  is incremental future work behind the same contract.

## Consequences

- Easier: CHC/PDR (P4.6) can consume `lra_interpolant`/`qf_uf_interpolant` for
  frame generalization; the interpolant inherits the existing proof assurance.
- Harder/revisit: completeness is partial by design — broadening EUF coverage,
  adding the propositional/BV interpolant off the DRAT proof
  ([T3.8.2](../../plan/track-3-proof-lean/P3.8-interpolation.md)) and combined
  LRA+EUF ([T3.8.4]) are tracked follow-ups. The `(get-interpolant)` SMT-LIB
  command awaits coordination on the `axeyum-smtlib` parser.
- The interpolation rows enter the capability ledger
  (`crates/axeyum-solver/src/capabilities.rs`).

## Update (2026-06-22, same session)

The interpolation engine now covers **all seven standard quantifier-free
fragments**, each under the same verify-before-return contract: **QF_LRA**
(`lra_interpolant`), **QF_LIA** (`lia_interpolant`, interpolate the rational
relaxation + clear denominators, verified over ℤ), **QF_UF**
(`qf_uf_interpolant`), **propositional/SAT** (`axeyum_cnf::propositional_interpolant`,
McMillan over the LRAT proof), **QF_BV** (`qf_bv_interpolant`, joint bit-blast +
lifted propositional interpolant), **conjunctive QF_UFLRA** (`uflra_interpolant`,
Ackermannize → LRA interpolant → translate), and **conjunctive QF_UFLIA**
(`uflia_interpolant`, the integer analogue → `lia_interpolant`). `Solver::interpolant`
dispatches LRA → LIA → EUF → UFLRA → UFLIA → BV, and `Solver::interpolant_explained`
classifies `Interpolant | NotInterpolable | Declined`. **The only remaining P3.8
work is the SMT-LIB `(get-interpolant)` command surface** (coordinate
`axeyum-smtlib`).

**Ledger-label correction:** every interpolation row (and `mbp_lra`) is
`Assurance::Validated`, **not** `Checked` — each *re-decides* the three conditions
internally to verify, but emits **no per-query certificate** to the consumer
(`Validated` is exactly "verify-before-return via solver checks, no self-contained
certificate"). The interpolants are not yet Lean-kernel-reconstructed.
