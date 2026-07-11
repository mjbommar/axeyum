# ADR-0094: Retained Warm Nested Array-Valued UF Parameters

Status: accepted
Date: 2026-07-10

## Context

ADR-0092 admitted direct finite-array symbols as parameters to retained
array-valued UF parents, and ADR-0093 admitted supported structural
`store`/`const-array`/array-ITE key expressions. The remaining common warm-path
hole was a key produced by another array-valued application, for example
`select(f(g(a)), i)` or `select(f(store(g(a), k, v)), i)`.

Projecting those keys by evaluating the original nested `Apply` term would
require the inner function table before the outer table is built. That conflicts
with the retained warm projection order, where all array-valued UF function
tables are constructed after array and structural model repair.

## Decision

`IncrementalBvSolver` now admits supported array-valued `Apply` terms as
finite-array keys to retained array-valued UF parents, both directly and under
the supported structural key language from ADR-0093.

The encoding uses two replay-safe cases:

- a direct nested array-valued `Apply` key is encoded by the inner
  application's private projection symbol;
- a structural key is encoded by its rewritten structural term, where any
  nested array-valued `Apply` subterm has already been replaced by that
  application's private projection symbol.

Direct public array symbols are still encoded as themselves. Private projection
and structural-owner symbols are not treated as public array-parameter symbols
during distinct-key synthesis.

Nested array-valued applications are counted under the existing per-root
array-UF parent cap, and their scalar/direct/structural dependencies are
retained before solving. Structural owners remain private model-repair devices:
they are realized against rewritten structural terms before function tables are
projected, but structural keys are not keyed by unrelated private owner values.

During structural owner realization, total-array constraints come from original
user reads plus active false-branch diff-witness reads. Inactive helper reads
from guarded relation observations do not force arbitrary total models.

## Soundness Argument

The Boolean abstraction remains a relaxation of the original query. Nested
array-valued key equality is represented by the existing retained array
relation machinery: active equality classes or ADR-0091 private relation flags
guard application congruence.

For SAT projection, inner array-valued applications first have private
projection arrays in the candidate/model assignment. Outer function-table keys
can therefore be evaluated without recursively needing an already-projected
inner function table. The final public model still contains full `FuncValue`
interpretations for both inner and outer functions; replay evaluates the
original `g(a)` term through the projected inner table, then uses that same
array value as the key to the outer table.

Structural nested keys replay because their rewritten structural terms use the
same private projection values that the nested function tables later expose.
Final original-term replay remains the SAT gate, so any projection-order bug,
key collapse, or missing dependency is rejected instead of returned as SAT.

## Validation

- The retained warm array-UF parent suite now has seventeen tests.
- New nested-key gates cover:
  - direct `f(g(a))` SAT projection with both function tables present and the
    original assertion replaying;
  - asserted equality of nested keys refuting conflicting result reads; and
  - a structural key `store(g(a), k, v)` replaying through the nested
    application base.
- Existing structural-key relation-flag separation, asserted structural-key
  equality, scalar-keyed parents, direct-array-key parents, scope/core, exact
  cap, check_auto, and Z3 matrix gates remain in the same focused suite.

## Consequences

The warm path no longer falls back solely because an array-valued UF parameter
is produced by another supported array-valued UF application. The remaining
boundaries are:

- nested/extended array components,
- memory BMC/k-induction integration,
- online array proof logging, and
- broader low-load aggregate timing.
