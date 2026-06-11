# Proof Formats And Checkers

Status: draft
Last updated: 2026-06-10

## Purpose

Map the concrete proof-format landscape so the evidence thesis has an
implementation path. The models-proofs-certificates note defines what evidence
is; this note records which formats and external checkers exist and which
Axeyum should produce, consume, or ignore.

## Scope

In scope:

- SAT proof formats, SMT proof formats, checker ecosystem, and Axeyum's
  layered-certificate strategy.

Out of scope:

- Checker implementation details.

## Core Claims

- SAT proofs are a solved interchange problem: DRAT is the competition
  standard, LRAT adds hints for fast checking, FRAT is the solver-friendly
  middle ground that elaborates to LRAT. Verified checkers exist (cake_lpr for
  LRAT), so Axeyum can outsource the trusted base rather than building one.
- SMT proof formats are not yet converged: Alethe (veriT/cvc5), LFSC, and
  cvc5's newer CPC/Ethos line coexist; Z3 proofs are solver-specific. Axeyum
  should consume these opportunistically for oracle cross-checks, and not
  design its own SMT proof format early.
- Carcara, the Alethe proof checker, is written in Rust — a natural
  integration and a proof that Rust-native checking infrastructure is viable.
- For Axeyum's own pure Rust path, an unsat answer is a *layered certificate*:
  each layer's claim is discharged by a different mechanism, and the trust
  story is the composition.

## Layered Certificate For The Pure Rust Path

| Layer claim | Discharge mechanism |
|---|---|
| Rewrites preserve equisatisfiability | Rule IDs + per-rule tests + differential oracle (later: per-rule proofs) |
| Bit-blasting is correct per operator | Exhaustive checking at small widths + differential oracle at large widths |
| Tseitin encoding is equisatisfiable | Construction argument + CNF evaluator round trips |
| CNF is unsatisfiable | DRAT/LRAT proof checked by external/verified checker |

This is weaker than one end-to-end proof but each link is independently
testable, and the weakest links (rewrites, bit-blasting) are exactly where
differential testing concentrates.

## Design Implications

- The SAT trait should reserve a proof-logging hook from v1 even if no
  implementation exists; varisat shows Rust CDCL with proof output is
  practical.
- Emit DRAT first (cheap to produce from CDCL); treat LRAT as an elaboration
  step, possibly via existing tools (drat-trim).
- Record rewrite rule IDs and bit-blaster version in every certificate so
  failures bisect to a layer.
- Exhaustive small-width operator checking (all inputs for widths <= 8)
  should be a standing CI job, not a one-time test.

## Risks

- DRAT proofs can be enormous; streaming output and bounded retention need
  design before enabling by default.
- Inprocessing techniques in adapted SAT solvers may not log proofs; the
  capability model must mark proof-producing configurations explicitly.

## Open Questions

- [ ] Produce LRAT directly from the future custom CDCL core, or always
      elaborate from DRAT?
- [ ] Should Axeyum bundle a small Rust LRAT checker for self-containment, or
      shell out to established checkers?
- [ ] When rewrite rules gain proof obligations, are they checked in Lean, in
      an SMT oracle, or by exhaustive finite instantiation?

## Source Pointers

- DRAT-trim: https://github.com/marijnheule/drat-trim
- FRAT format: https://github.com/digama0/frat
- cake_lpr verified LRAT checker: https://github.com/tanyongkiam/cake_lpr
- Alethe proof format: https://verit.gitlabpages.uliege.be/alethe/
- Carcara Alethe checker (Rust): https://github.com/ufmg-smite/carcara
- cvc5 Ethos checker (CPC/Eunoia): https://github.com/cvc5/ethos
- lean-smt, cvc5 proof replay in Lean: https://github.com/ufmg-smite/lean-smt
- varisat proof output: https://github.com/jix/varisat
