# ADR-0582: Exact-budget circuit search must name its lower-bound premise

Status: accepted
Date: 2026-08-26

## Context

The complete multiplicative-complexity encoding decides whether a function has
a circuit with *at most* `k` AND gates. Padded formulas consequently admit zero
operands and dead gates. Those representations are impossible in a minimum-size
circuit, but deleting them is not an unconditional symmetry reduction: a target
of complexity below `k` may have no syntactically irredundant `k`-gate padding.

The PRIMATEs-inverse search has an independently checked DRAT refutation at six
AND gates. Its seven-gate query can therefore use minimum-circuit facts, provided
the formula and command expose that premise rather than silently changing the
meaning of the ordinary at-most-budget encoder.

The reduction is prior art. Soeken's exact abstract-XAG encoding includes
nonconstant linear fan-ins and requires every AND gate and every essential input
to be used. This ADR records an Axeyum trust boundary and integration, not a new
mathematical technique.

## Decision

Keep the ordinary encoding byte-stable and add an explicit exact-budget
irredundancy augmentation whose caller must name the checked budget `k - 1`.

For every AND gate, the augmentation requires both affine operands to contain a
nonconstant basis term and requires the gate output to be selected by a later
operand or a circuit output. A minimum circuit always has this form: an operand
equal to zero or one makes its gate affine and removable, while a gate with no
later use is dead and removable. The augmentation also adds redundant clauses
requiring every truth-table-essential input to occur and every varying output
coordinate to select a nonconstant term.

`MultiplicativeEncoding::formula_with_exact_budget_irredundancy` applies the
restriction to direct CNF routes. `MultiplicativeAnfEncoding` exposes the same
clauses over typed source-selector indices, and the generic Boolean-ANF/CNF
bridge accepts arbitrary validated clauses over its source-variable prefix.
No caller may address the bridge's private extension variables.

The PRIMATEs driver spells the premise as
`--exact-budget-after-checked-lower 6` for a seven-gate query and refuses any
number other than exactly `k - 1`. Pure ANF export refuses this mode because the
additional disjunctions are CNF constraints, not polynomial equations in the
exported source system.

## Evidence

- All eight two-input Boolean functions whose exact multiplicative complexity
  is one remain satisfiable under the direct and portable-ANF/CNF forms; every
  lifted model passes the independent circuit replay.
- Structural controls check that zero-operand and dead-gate clauses address the
  intended selectors. The generic source-clause bridge accepts a valid clause,
  changes its model set, and rejects an extension-variable index.
- The PRIMATEs-inverse seven-gate portable formula has 919 ANF variables, 970
  equations, 20,585 CNF variables, and 69,809 clauses. Its SHA-256 is
  `176513848d1fa511bca2a7b5c50255f6dabe6ebff696eb9f62abcfad0f43ae76`.
- Focused tests, all-target/all-feature Clippy, and warning-denied Rustdoc pass.
- Soeken, “Determining the Multiplicative Complexity of Boolean Functions using
  SAT,” arXiv:2005.01778, Section III-B, documents the prior nonconstant-fanin
  and all-gates/all-essential-variables-used constraints.

## Alternatives

Making the clauses default was rejected because it would change an at-most-`k`
decision problem into an exact-minimum normal form without carrying the lower
bound that makes the transformation complete. Encoding disjunctions as opaque
ANF rewrites was rejected because it would weaken the checked equivalence route.
Treating the reduction as novel was rejected by the primary-source audit.

## Consequences

Exact-budget consumers can reuse a smaller, premise-explicit search space across
all three multiplicative encodings. The lower-budget certificate remains a
separate artifact and must be composed with any eventual seven-gate result. The
new clauses do not themselves decide PRIMATEs inverse: proof-producing CaDiCaL
runs remain uncredited until a complete model or checked refutation exists.
