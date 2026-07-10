# ADR-0085: Bounded Structural Array-Class Equations

Status: proposed
Date: 2026-07-10

## Context

ADR-0084 projects ordinary array symbols and fresh array-valued UF result
symbols by final e-class. Structural array terms remain semantic parents without
independent model slots: `store(a, i, v)`, `ite(c, a, b)`, and constant arrays
are values derived from their children.

Observed-read consistency is sufficient for UNSAT transfer but not for every SAT
model. For example, a true equality `store(a, i, v) = b` can constrain all
prepared reads while majority-default projection independently chooses total
arrays for `a` and `b` whose unobserved defaults make original replay fail. The
candidate is satisfiable: choosing `b` to be the concrete value of the store is
enough.

Array-valued ITE equality has a second issue that projection cannot repair. From
`c`, `ite(c, a, b) = d`, and `a != d`, the selected branch equality must reach
the equality bus. Read abstraction lowers each observed ITE read to a scalar ITE,
but independent diff witnesses need not use the same index, so finite
observations alone may not derive the contradiction.

The missing boundary is therefore a bounded combination of exact pre-search
equality decomposition and replay-safe structural model realization. It must not
introduce open-scope e-graph nodes, enumerate an array domain, or weaken the
mandatory original-query replay gate.

## Decision

Canonical finite-scalar ABV/AUFBV will support bounded structural array-class
equations as follows.

### Array-ITE equality decomposition

Before ROW/equality abstraction, recursively rewrite array equalities whose
outer operand is an ITE using the exact identity

```text
ite(c, a, b) = d  <=>  ite(c, a = d, b = d)
```

and symmetrically when the right operand is an ITE. Nested ITEs recurse until the
resulting array equalities have non-ITE outer operands. The expansion is
canonical-only, deterministic, bounded by the existing equality/interface
limits, and completed before `CdclT` opens a theory scope. Each selected branch
equality therefore receives an ordinary equality flag and original e-graph term;
Boolean search chooses the branch through the scalar ITE.

### Structural model realization

Function abstraction records rewritten operands for every array equality, with
array-valued applications replaced by their fresh result-array owners. After
ordinary read/class projection, every candidate-true structural equality is
realized over this function-free term graph:

- assigning a leaf array symbol to a target total array is permitted only when
  every observed read owned by that symbol keeps its scalar candidate value;
- realizing `store(base, i, v)` as target requires `target[i] = v`, then realizes
  `base` as target (making the store idempotent at `i`);
- realizing `ite(c, a, b)` realizes only the candidate-selected branch;
- realizing a constant array succeeds only when it already equals the target;
- other structural forms must already evaluate to the target or the candidate
  declines.

For a mismatched true equality, prefer realizing a direct owner from the value of
the structural side, then try the reverse orientation and bounded structural-to-
structural realization. Iterate all true equations deterministically to a fixed
point because owners may be shared. Re-evaluate every equation after each pass;
non-convergence, an observation conflict, an unsupported form, or failed replay
returns `Unknown`.

False equalities are never repaired directly. Their existing diff-witness
observations remain constraints, and final original replay checks every
disequality after true-equation realization.

The order remains:

1. exact scalar/e-graph search and final class discovery;
2. ordinary observed-read/class projection;
3. bounded structural true-equation realization;
4. function-table projection from the array-complete assignment;
5. original-query replay.

Generic lazy ROW/extensionality and eager/certifying routes remain unchanged.
Admission remains finite Bool/BitVec array components with all existing DAG,
site, equality, interface, CNF, deadline, and iteration caps.

## Soundness Argument

ITE decomposition is denotation-preserving by the semantics of ITE and equality.
It adds no theory assumption: the Boolean skeleton selects exactly the equality
of the active array branch.

Structural realization is only model construction. Assigning a leaf to a target
is rejected if any abstract scalar read would change. For stores, the side
condition `target[i] = v` makes `store(target, i, v) = target`; for ITE, only the
evaluated branch determines the value; constant arrays are accepted only by
direct value equality. Thus each successful local step establishes the equation
under the candidate assignment. A bounded fixed-point recheck catches equations
invalidated through shared owners.

No SAT verdict follows from local realization alone. Function interpretations
are rebuilt from the resulting full values and every original assertion is
evaluated. Any missed dependency, false disequality, unsupported cycle, or
incorrect model choice yields `Unknown`, never `Sat`. UNSAT remains sound because
search sees only a denotation-preserving ITE rewrite plus the existing valid EUF,
ROW, select-congruence, and extensionality consequences.

## Required Validation Before Acceptance

- Focused SAT replay for symbol/store, store/store, symbol/constant-array, and
  array-valued-UF/store equalities with no externally complete read set.
- Focused ITE equality SAT for true/false and nested branches, plus an unselected
  branch disequality that remains SAT.
- Focused ITE equality UNSAT where the selected branch is separately disequal,
  proving branch equality reaches the e-graph rather than relying on projection.
- Store write-index conflict UNSAT and true-equality/false-disequality
  interactions that prove observed reads are preserved during realization.
- Deterministic analytic/front-door matrix with replay of every SAT model and
  direct Z3 comparison under the native feature.
- Existing AUFBV differential fuzz, full solver units, strict clippy, rustdoc,
  link checks, and exact-SHA pre-push validation.

## Alternatives Considered

### Enumerate the finite array domain

Rejected: the admitted index width can be large, so extensional enumeration is
exponential and violates the project resource discipline.

### Give every structural term a synthetic array symbol

Rejected: it duplicates the array theory, requires equality constraints for
every constructor, and introduces model slots whose only correct values are
already derivable from children.

### Repair only after original replay fails

Rejected: replay does not expose a stable, compositional reason for failure.
Using candidate-true equality metadata makes the model equations explicit and
bounded before the final acceptance gate.

### Treat ITE equality only as a projection hint

Rejected: projection cannot soundly turn the selected-branch disequality example
into UNSAT. The exact Boolean equality decomposition is required for decision
completeness on that shape.
