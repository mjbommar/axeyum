# Proof Certificate Cookbook Roadmap

## Charter

Build a route-by-route guide to Axeyum proof and evidence artifacts. The goal is
not to document every line of proof code. The goal is to make the assurance
story inspectable: what was searched, what was checked, what was trusted, and
where Lean reconstruction is complete or partial.

## Non-Goals

- A full proof theory textbook.
- A substitute for the implementation.
- A claim that every route is already Lean complete.
- A generated dump of large certificates.

## Audience

| Audience | Need |
|---|---|
| Solver user | Understand what proof/evidence artifact backs an answer. |
| Proof contributor | Follow the expected shape for a new certificate route. |
| Reviewer | Audit trust boundaries and rejection behavior. |
| Educator | Teach SAT/SMT certificates with runnable tiny examples. |

## Current Status

First recipe files have landed:

- [QF_BV Bit-Blast Evidence](recipes/qf-bv-bitblast.md)
- [QF_UF Congruence And Alethe Evidence](recipes/qf-uf-congruence-alethe.md)
- [QF_LRA Farkas Evidence](recipes/qf-lra-farkas.md)
- [Array Read-Over-Write Axiom Evidence](recipes/array-row-axiom.md)

Each names a tiny formula, the current evidence artifact, the checker, focused
test commands, trust boundary, Lean status, and links to the atlas/support/trust
docs.

## Recipe Structure

Each recipe should use the same format:

```text
recipes/<route-id>.md
```

Required sections:

1. **Problem shape**
   - Tiny formula.
   - Fragment and operators.
   - Expected result.
2. **Solver route**
   - Which Axeyum route decides it.
   - Which reductions run before the proof artifact is emitted.
3. **Evidence artifact**
   - Artifact type: LRAT, Alethe, Farkas, Diophantine, structural certificate,
     array-elimination witness, or Lean module.
   - Minimal excerpt or schematic shape.
4. **Checker**
   - In-tree checker function or crate.
   - What is re-derived independently.
   - What rejection cases are tested.
5. **Lean reconstruction**
   - Complete, partial, not started, or intentionally out of scope.
   - `#print axioms` expectation when a Lean module exists.
6. **Trust boundary**
   - What is trusted.
   - What is replayed.
   - What downgrades to `unknown`.
7. **Commands**
   - Focused test command.
   - Optional example command or fixture path.
8. **Links**
   - Local implementation paths.
   - Trust ledger row.
   - Capability / atlas row.

## Initial Recipes

### R0: Boolean CNF + LRAT

Purpose: smallest proof object and checker story.

Candidate links:

- `crates/axeyum-cnf`
- `crates/axeyum-solver/src/evidence.rs`
- [trust ledger](../research/08-planning/trust-ledger.md)

Exit criteria:

- Recipe shows a tiny unsat CNF.
- LRAT is parsed or generated.
- In-tree LRAT checker rejects a tampered proof.

### R1: QF_BV Bit-Blast Proof

Status: first recipe landed as
[QF_BV Bit-Blast Evidence](recipes/qf-bv-bitblast.md).

Purpose: show the finite-domain path that most directly expresses Axeyum's
foundation.

Exit criteria:

- Recipe starts from a BV formula, not a raw CNF.
- Shows term-to-AIG-to-CNF route.
- Names bit-blast proof status and Lean reconstruction status honestly.

### R2: QF_UF Congruence / Alethe

Status: first recipe landed as
[QF_UF Congruence And Alethe Evidence](recipes/qf-uf-congruence-alethe.md).

Purpose: explain equality reasoning, congruence, and Alethe reconstruction.

Example shape:

```text
a = b
f(a) != f(b)
```

Exit criteria:

- Recipe shows the congruence step.
- Alethe proof route is named.
- Lean kernel reconstruction status is explicit.

### R3: QF_LRA Farkas

Status: first recipe landed as
[QF_LRA Farkas Evidence](recipes/qf-lra-farkas.md).

Purpose: explain arithmetic certificates independent of SAT traces.

Example shape:

```text
x >= 1
x <= 0
```

Exit criteria:

- Recipe shows multipliers or a schematic Farkas combination.
- Checker re-derives the contradiction from original constraints.
- Lean arithmetic prelude status is linked.

### R4: QF_LIA Diophantine

Purpose: distinguish rational infeasibility from integer infeasibility.

Example shape:

```text
x + y = 0
x - y = 1
```

Exit criteria:

- Recipe explains gcd/divisibility contradiction.
- Checker is independent of the search route.
- Lean gap or reconstruction route is stated honestly.

### R5: Arrays / Read-Over-Write

Status: first recipe landed as
[Array Read-Over-Write Axiom Evidence](recipes/array-row-axiom.md).

Purpose: explain reduction evidence for array reasoning.

Example shape:

```text
select(store(a, i, v), i) != v
```

Exit criteria:

- Recipe distinguishes syntactic ROW simplification, eager elimination, lazy
  select congruence, and warm incremental slices.
- Model replay and proof reconstruction status are explicit.

### R6: Datatype Structural Refutation

Purpose: show constructor distinctness, injectivity, and acyclicity evidence.

Exit criteria:

- Recipe includes a tiny constructor contradiction.
- Checker is named.
- Lean route is linked.

## Validation Checks

Minimum near-term checks:

```sh
./scripts/check-links.sh
cargo test -p axeyum-solver --test evidence
cargo test -p axeyum-solver --test lean_crosscheck
```

The commands can be narrowed per recipe, but every recipe must name the focused
test that proves its current claim.

## Content Rules

- Never call a route "Lean certified" unless a checked Lean artifact exists.
- Distinguish replay-checked, in-tree checked, externally checked, and
  Lean-kernel checked.
- Keep examples tiny enough that a reader can inspect the whole formula.
- Prefer exact file links over vague module names.
- Include at least one rejection or tamper case for every checker recipe.

## Links To Capabilities

Every recipe should eventually point to:

- [SMT Fragment Atlas](../atlas/README.md)
- [capability matrix](../research/08-planning/capability-matrix.md)
- [support matrix](../research/08-planning/support-matrix.md)
- [trust ledger](../research/08-planning/trust-ledger.md)
- [dominance scoreboard](../../bench-results/DOMINANCE.md)

## Graduation Criteria

The cookbook graduates from "incubator" when:

- at least six recipes are complete;
- every recipe has a focused passing test command;
- every recipe names trust boundaries and Lean status;
- the cookbook is linked from user and contributor docs;
- a new proof route cannot be considered done without either a cookbook recipe
  or an explicit reason it does not need one.
