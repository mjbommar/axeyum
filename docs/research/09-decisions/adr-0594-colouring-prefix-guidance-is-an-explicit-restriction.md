# ADR-0594: Colouring prefix guidance is an explicit search restriction

Status: accepted
Date: 2026-08-26

## Context

The open-problems programme's five-colour Rado search reached a witness that could no longer be
extended by assigning only the next point. Repair required keeping an initial segment fixed while
letting SAT search recolour the tail. The first successful experiment added DIMACS unit clauses in
a shell loop. That arithmetic was deterministic, but it duplicated Axeyum's variable convention
outside the typed colouring API and made the restriction's logical scope easy to overstate.

## Decision

`ColouringProblem::encode_with_witness_prefix` is the single typed route for prefix-guided
colouring search. It first emits the byte-identical canonical formula and then appends one positive
unit clause per requested prefix point using `ColouringProblem::literal`. It checks the problem
length, witness length, and palette before emitting anything.

The API and its `rado_dump_cnf` consumer describe the result as a restriction, not an equivalent
encoding. A restricted UNSAT result proves only that the named prefix cannot extend. A SAT model
may receive mathematical credit only after complete replay against `ColouringProblem::encode`
without the units and independent replay of the defining family relation.

## Evidence

Two unit tests pin the canonical-clause prefix, exact appended units, satisfying assignment, and
all length/palette refusals. The CLI-generated 404-point, 50-fixed-point formula is byte-identical
to the independently constructed discovery formula: 2,020 variables, 186,337 clauses, SHA-256
`9e1f86ee99658b1448306381f9043027f5818602dfc1c1023da136ef2051f4e4`.

The resulting complete model was separately checked against the unrestricted 186,287-clause
canonical formula and all 36,046 defining triples. This establishes
`R_5(3(x-y)=2z) > 404`; it does not make any restricted UNSAT result an upper bound.

## Alternatives

Keeping the shell clause arithmetic was rejected because it duplicated the row-major variable
mapping. Treating a fixed prefix as symmetry breaking was rejected because the witness prefix is
not proved without loss of generality. Adding a Rado-specific encoder was rejected because the
restriction applies to every `ColouringProblem` consumer.

## Consequences

Tail repair is now reusable across Rado, Schur, van der Waerden, and other colouring families.
Every consumer must preserve the asymmetric evidence rule: restricted SAT can be promoted after
unrestricted replay; restricted UNSAT remains search guidance only.
