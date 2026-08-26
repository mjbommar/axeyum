# ADR-0587: Partial cube progress is a leaf verdict

Status: accepted
Date: 2026-08-26

## Context

ADR-0543 checks a complete cube-and-conquer refutation, including an independent
proof that the cubes cover every assignment.  Long frontier searches also need
durable intermediate accounting: a solver may finish one leaf days before the
whole cover.  Checking a proof against a dumped leaf CNF is insufficient because
it does not establish that the dump is the intended restriction of the base
formula.  Calling one checked leaf a proof of the base formula would be worse.

This closes the partial-artifact part of the open-problem artifact question in
[`research-questions.md`](../08-planning/research-questions.md#exploration-track-searched-bridge-composition-added-2026-08-01).

## Decision

Axeyum will expose a strict single-leaf checker that regenerates the complete
Boolean-product cover from the base DIMACS and named selectors, selects the
requested cube by its deterministic index, rebuilds `base AND cube`, and checks
the retained textual DRAT with the file-backed backward checker.

Its only successful claim is `leaf-unsat-checked`.  It never claims that the
base formula is UNSAT.  The base result still requires every leaf and the
covering proof through the existing complete-cover checker.

## Evidence

The first PRIMATEs-inverse MC=7 cover cell (index 0 over semantic selector
variables 2 through 6) is immediately UNSAT.  CaDiCaL produced a 413,418-byte
DRAT proof.  The new front door accepted it only after regenerating the five
negative selector units from the base formula and cube index.  A truncated
proof is rejected.

## Alternatives

- Trust the emitted leaf CNF: rejected because base/cube binding would be an
  unchecked provenance assertion.
- Wait to check anything until all leaves finish: sound, but discards useful
  fail-closed progress and delays discovery of malformed proofs.
- Credit a checked leaf as global UNSAT: rejected as false.

## Consequences

Long cube searches can report exact checked progress without weakening the
complete-cover contract.  Artifact packages must keep leaf and global verdicts
visibly distinct.
