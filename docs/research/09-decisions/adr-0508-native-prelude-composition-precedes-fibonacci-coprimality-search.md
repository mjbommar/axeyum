# ADR-0508: Native prelude composition precedes Fibonacci coprimality search

Status: accepted
Date: 2026-08-19
Index-summary: Compose native theorems into imported kernels before coprimality search

## Context

The selected Fibonacci coprimality target has a bounded induction proof using
the admitted recurrence plus seven theorems already proved axiom-free in the
native Nat prelude. The imported train environment contains the target's core
definitions and `Nat.rec`, but not those seven theorems.

## Decision

Do not spend a target proof-search budget yet. First implement identity-aware,
transactional composition that reuses compatible imported prelude declarations
and constructs only the missing native theorem layer. Require exact replay of
the seven-lemma surface in the target environment before preregistering a
coprimality execution.

## Evidence

The exact `r082` import contains 261 declarations, 52 theorems, and zero axioms.
All seven required native theorem names are absent. `build_nat_prelude` cannot
currently extend that environment: it rejects immediately with
`DeclarationExists` at `True`. The measurement used only the train stream,
displayed no proof bodies, and performed zero proof searches, target
submissions, evaluation accesses, or ledger writes.

## Consequences

The next work is a library/import composition boundary, not another special
Fibonacci constructor. Composition must compare overlapping declarations
structurally, preserve determinism and theorem-dependency accounting, and be
atomic on failure. Once it works, the bounded coprimality proof can reuse the
native library and should expose only the admitted recurrence as its durable
theorem premise.
