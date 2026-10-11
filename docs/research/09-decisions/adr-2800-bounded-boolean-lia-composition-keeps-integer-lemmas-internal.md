# ADR-2800: bounded Boolean/LIA composition keeps integer lemmas internal

Status: proposed; pending validation and portable integer elaboration
Date: 2026-10-10

## Problem

A Boolean disjunction containing an integer comparison does not reach the
conjunction-only integer proof emitter. Integer contradictions such as `2*x=1`
cannot be justified by real Farkas reasoning. Existing `lia_generic` is checked
in-tree but is not a portable Carcara rule.

## Decision

A private static-script adapter retains original assertions and abstracts at
most eight distinct integer comparisons into fresh propositional atoms. Enumerate
bounded assignments in stable order; for each integer-infeasible assignment,
produce its blocking clause using the existing checked `lia_generic` contract.
Feed those clauses to the existing native propositional proof tail as derived
steps, not source assumptions. Substitute full original comparison expressions
through every proof term, then recheck the complete proof with the existing
arithmetic-aware checker. Source declarations must be Bool or Int constants;
macros, scopes, unsupported commands and arithmetic shapes decline.

Bound source bytes to 64 KiB, assertions to 128, expression visits to 512,
depth to 32, atoms to eight and proof commands to 20,000. Check a shared deadline
between operations. Existing integer solve/check calls are not preemptible;
therefore this slice does not promise complete wall-clock deadline enforcement.
No new certificate format or checker rule is introduced. Proofs containing
`lia_generic` remain explicitly internal-only. Portable integer cuts/branch
elaboration, kernel reconstruction and complete budget enforcement remain required.

## Validation

Require the reported disjunction and integer-only contradictions to emit checked
closed refutations. Preserve original source assumptions, reject changed integer
lemmas and missing premises, and replay satisfiable controls. Do not count
Carcara acceptance with holes as external proof evidence.
