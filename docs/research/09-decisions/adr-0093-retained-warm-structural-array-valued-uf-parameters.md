# ADR-0093: Retained Warm Structural Array-Valued UF Parameters

Status: accepted
Date: 2026-07-10

## Context

ADR-0092 admitted direct finite-array symbols as parameters to retained
array-valued UF parents. That closed `select(f(a), i)`, but still deferred
structural keys such as `select(f(store(a, k, v)), i)`.

The canonical and warm array paths already had the pieces needed for a bounded
structural-key slice:

- ADR-0088 retains array-valued UF parents and projects function tables by full
  argument values;
- ADR-0090 realizes supported structural store/constant/array-ITE owners into
  replayable concrete array values; and
- ADR-0091/0092 provide private relation-flag guards for array-key congruence.

The remaining requirement was to retain scalar dependencies inside the key and
to force the final public model to evaluate the original structural key, not an
unrelated private owner.

## Decision

`IncrementalBvSolver` now admits supported structural finite-array arguments to
retained array-valued UF parents. The supported key language is:

- direct array symbols;
- `const-array` with a retained scalar value;
- `store(base, index, value)` where `base` is recursively supported and
  `index`/`value` stay inside the warm scalar abstraction; and
- array-valued `ite(condition, then_array, else_array)` where the guard is warm
  scalar and both branches are recursively supported.

Nested array-valued `Apply` terms as UF keys remain deferred in this slice.

For each structural key, the warm path retains scalar dependencies inside the
key before solving. It also creates a private structural owner plus a scoped
self-equality that realizes that owner against the original structural term
during SAT projection. The array-valued UF table is still keyed by evaluating
the original structural argument under the final public model.

Application-parent read congruence uses existing retained equality classes
when the structural key owners are already equal. Otherwise it falls back to the
ADR-0091 private relation-flag route, with the false branch carrying an exact
private diff witness.

Admission and limit accounting count structural nodes under array-valued UF
parameters. Oversized structural keys or nested array-valued `Apply` keys are
rejected before partial warm state is committed.

## Soundness Argument

The new Boolean constraints are the same valid congruence consequences used by
ADR-0088/0092, with array-key equality either supplied by an active retained
equality class or guarded by an ADR-0091 relation flag. Structural-key
self-equalities are private projection obligations: they do not assert a new
user fact between distinct arrays; they only force the private owner used for
model repair to match the original structural key before function projection.

For SAT, scalar dependencies inside keys are projected before array-valued UF
tables are constructed. Structural owners are realized by the existing
observed-read-preserving fixed-point machinery, then function tables are built
from the original structural argument values. Final replay evaluates the
original `Apply`/`Select` terms against the filtered public model, so any missed
dependency, key collapse, or owner mismatch rejects the candidate instead of
returning an unsound SAT model.

## Validation

- The retained warm array-UF parent suite now has fourteen tests.
- New structural-key gates cover:
  - `store(a, h(x), v)` as a key, proving scalar UF dependencies inside the key
    are retained and replayed;
  - independent structural keys separated by a private relation flag, replaying
    as SAT with distinct full structural key values;
  - asserted structural-key equality refuting conflicting result reads; and
  - nested array-valued `Apply` as a still-deferred control.
- The existing scalar-key, direct-array-key, relation-flag, structural-parent,
  push/pop, one-shot-core, exact 64/65 cap, check_auto, and Z3 matrix gates
  remain in the same focused suite.

## Consequences

Supported `store`/`const-array`/array-ITE keys no longer force retained warm
array-valued UF parents onto the fallback dispatcher. The remaining boundary is
now narrower and explicit:

- nested array-valued application keys,
- nested/extended array components,
- memory BMC/k-induction integration,
- online array proof logging, and
- broader low-load aggregate timing

remain future work.
