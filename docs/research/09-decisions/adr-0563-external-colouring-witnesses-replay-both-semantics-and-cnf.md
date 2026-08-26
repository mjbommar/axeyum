# ADR-0563: External colouring witnesses replay both semantics and CNF

Status: accepted
Date: 2026-08-26
Index-summary: Admit external finite-colouring witnesses only after independent relation replay and regenerated-CNF evaluation

## Context

The Rado frontier ledger described Li's claimed `R_5(3)>296` witness as inaccessible and
unverified. A current search found a public repository containing the exact 296-point
colouring. Its equation `x+3y=3z` has the same unordered monochromatic solution sets as
Axeyum's `3(x-y)=z`, but its zero-based colour names do not necessarily satisfy Axeyum's
first-occurrence symmetry convention. The existing claim checker can replay a committed
witness, while no small generic CLI performed both the family-independent semantic check and
evaluation of the freshly regenerated CNF.

## Decision

Add two reusable colouring operations:

- `Witness::canonicalize_palette` renames colours by order of first occurrence. Its contract
  explicitly restricts use to instances whose entire palette is interchangeable; it is not
  sound across the distinct colour roles of an off-diagonal instance.
- `ColouringProblem::witness_assignment` creates the complete one-hot assignment for an exact
  problem, rejecting domain or palette mismatch.

Add `verify_colouring_witness`, a family-generic command that first invokes the family's
independent defining-relation enumerator, then regenerates the CNF, constructs the assignment,
and evaluates every clause. It refuses palette canonicalization for colour-dependent families.
Neither source metadata nor an upstream `valid` field participates in acceptance.

## Evidence

- Li repository commit `e0b30e52064821312ec6975f77d423f7ca575a74` contains
  `R5_witness_296.json` with SHA-256 `942d4e...ecf`.
- Deterministic zero-to-one-based conversion produces `witness-296.txt` with SHA-256
  `91de1a...775`. The independent relation replay accepts all 296 points, and the canonicalized
  assignment satisfies Axeyum's freshly generated 1,480-variable / 125,222-clause formula.
- Changing only the first colour causes relation replay to exit 1 on monochromatic set
  `[1,22,63]`; completion is not acceptance.
- Unit coverage round-trips a noncanonical palette through canonicalization, one-hot assignment,
  formula evaluation, and model decoding.

## Consequences

- The strongest currently verified `b=1, k=5` bound in Axeyum is now the externally sourced
  `R_5(3(x-y)=z)>296`; Axeyum's earlier 251-point witness is superseded but retained.
- This correction is not a new mathematical result. It prevents the programme from spending
  frontier effort below a public bound and demonstrates a reusable third-party witness boundary.
- A bounded min-conflicts probe at 297 is search telemetry only. Failure to find a colouring
  cannot establish an upper bound.
