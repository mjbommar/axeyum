# Depth and scope: what this curriculum is and is not

This file states the curriculum's honest ceiling so nobody mistakes the
**map** for the **territory**. A `covered` node is not a claim of textbook-depth
treatment or complete automation of the corresponding field.

## Three different coverage layers

1. **Curriculum map.** The [23-node prerequisite DAG](README.md) gives a stable
   foundation-to-destination spine. Its authority is
   [`curriculum.toml`](curriculum.toml).
2. **Scenario coverage.** `axeyum-scenarios` supplies small, deterministic
   exercises. A `covered` curriculum node names at least one realized family
   whose catalog examples pass `Scenario::self_check`.
3. **Resource depth.** The larger foundational-resource system adds source
   metadata, learner pages, proof routes, solver-reuse links, and validated
   example packs. Its generated
   [curriculum status audit](../foundational-resources/generated/curriculum-status-audit.md)
   reports this axis separately.

Those layers must not be collapsed. A node can have a self-checking scenario
while still needing richer lessons, proof-producing examples, or solver-corpus
reuse.

## What a self-check establishes

Scenario checks have explicit assurance boundaries:

- a SAT exercise carries a concrete witness and evaluates every assertion;
- a small finite UNSAT exercise can exhaust the complete assignment domain;
- an oversized finite UNSAT exercise may use a deterministic sample, which is
  useful regression evidence but not a proof of unsatisfiability.

The broader resource packs add finite/computable replay and, for selected
negative rows, independently checked DRAT/LRAT, Alethe, Farkas, or other
route-specific evidence. Consult the live [capability
matrix](../research/08-planning/capability-matrix.md), [support
matrix](../research/08-planning/support-matrix.md), and [trust
ledger](../research/08-planning/trust-ledger.md) before turning an educational
example into a solver-assurance claim.

## The decidability and proof ceiling

Finite domains, exact computations, and some logical theories admit complete
decision procedures. Real-closed-field formulas are decidable, for example,
but that does not make general real analysis a first-order polynomial problem.
Completeness of the reals, arbitrary functions and sequences, convergence
theorems, and most textbook-level analysis require definitions and proof
structure beyond a bounded algebraic shadow.

The in-tree Lean-core checker and several reconstruction routes now exist; the
old statement that the proof track was only planned is obsolete. Their presence
still does not imply full Lean language, elaborator, tactic, workflow, Mathlib,
or theorem-library compatibility. The [Lean implementation
plan](../plan/lean-system-implementation-plan-2026-07-21.md) and live
[Project State](../PROJECT-STATE.md) keep those bounded achievements separate
from the remaining system-level work.

Accordingly:

- `covered` means a deliberately small decidable or computable exercise slice
  exists;
- `lean-horizon` marks content whose general theorem layer needs proof-oriented
  treatment even when finite or algebraic examples are available;
- `unknown`, replay-only evidence, and sampled checks remain visible rather
  than being promoted to proof claims.

## Honest comparison with canonical texts

| Area | Canonical texts | Axeyum's curriculum slice |
|---|---|---|
| Calculus and real analysis | Spivak, Rudin | Exact finite/algebraic shadows and selected checked inequalities; not the general epsilon-delta, completeness, compactness, or convergence theory. See [the Spivak map](foundational-books/spivak.md). |
| Number theory | Hardy & Wright, Stein | GCD/Bézout, CRT, residues, modular inverses, fixed-modulus exponentiation, parity, and other finite/computable exercises; not analytic or general algebraic number theory. |
| Abstract algebra | Dummit & Foote | Finite groups, rings, fields, maps, quotients, modules, and related table/replay slices; not the full structure theory. |
| Linear algebra | Axler and numerical-linear-algebra texts | Fixed finite matrices, exact rational and finite-field calculations, residuals, and selected checked contradictions; not general dimension, spectral, or numerical-stability theorems. |

Think of this curriculum as a navigable table of contents with verified answer
keys for carefully stated finite, computable, or certificate-backed problems.
It complements textbooks and proof libraries; it does not replace them.

## Validate the boundary

```sh
cargo test -p axeyum-scenarios
just foundational-resources
just parity-docs
```

The first command checks scenario catalogs and graph mappings. The second
validates concept rows, example packs, negative fixtures, and generated
dashboards. The third checks the live capability, support, trust, proof-gap,
SMT-LIB, Lean, and benchmark documentation authorities.

## See also

- [Curriculum index](README.md) — map and status legends.
- [Current curriculum backlog](BACKLOG.md) — remaining teaching/scenario work.
- [Foundational books](foundational-books/README.md) — canonical-text mappings.
- [Foundational resource build sequence](../foundational-resources/MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md)
  — broader content and proof-depth priorities.
- [Formal mathematics tour rationale](../research/08-planning/formal-mathematics-tour.md)
  — design background.
