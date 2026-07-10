# ADR-0092: Retained Warm Direct Array-Valued UF Parameters

Status: accepted
Date: 2026-07-10

## Context

ADR-0088 retained array-valued UF parents only when every application argument
was scalar. That kept `select(f(x), i)` warm, but still deferred
`select(f(a), i)` when `a` itself was an array parameter. The missing piece was
not function-table storage: ADR-0084 already introduced full-value
`FuncValue` keys. The missing warm pieces were exact array-key congruence and
SAT model projection that does not accidentally collapse unconstrained array
keys to the same default value.

ADR-0091 supplies candidate-sensitive private flags for nested array equality
atoms. That makes array-key congruence usable inside the retained warm Boolean
encoding without exposing raw array equality to the bit-blaster.

## Decision

`IncrementalBvSolver` admits direct finite-array UF parameters for retained
array-valued UF parents:

- function results remain `Array(BitVec, Bool|BitVec)`;
- scalar parameters remain `Bool` or `BitVec` and are abstracted as before;
- array parameters may be direct symbols of sort `Array(BitVec, Bool|BitVec)`;
- structural array-key expressions such as `store(a, i, v)` as a function
  argument remain deferred.

Read congruence for retained application parents becomes:

```text
args1 = args2 and i = j => select(f(args1), i) = select(f(args2), j)
```

Scalar argument equalities are encoded directly. Array argument equalities are
handled in two cases:

- if an active retained equality already puts the two array symbols in the same
  class, the guard is known true; and
- otherwise a private ADR-0091 relation flag guards that array-key equality.

SAT projection is array-first and full-value-keyed:

1. project scalar reads, scalar UFs, candidate-true array equalities, and
   structural owner equations;
2. collect active direct array symbols used as UF parameters;
3. group them by candidate-true retained equality classes;
4. synthesize deterministic concrete array values that keep user-visible
   `select` constraints but do not treat private guarded relation-flag reads as
   public array entries;
5. make non-equal key classes distinct when possible; and
6. project array-valued UF results into `FuncValue::constant_value` tables keyed
   by those full array values.

If projection cannot synthesize distinct key values inside the finite component
sort while preserving user-visible constraints, the result is `Unknown`, not an
accepted SAT model. Original assertion and one-shot replay remains the final
SAT gate.

## Soundness Argument

The only new Boolean constraints are valid congruence consequences. Array-key
equality is either an already-active equality class or a private relation flag
whose true branch merges/project-equal arrays and whose false branch has an
exact diff witness. Therefore UNSAT still follows from the user roots plus valid
EUF/array consequences.

For SAT, function interpretations are full-value maps. Projection gives every
active array-key class a concrete array value before function tables are built,
and candidate-true equality classes share one value. Non-equal classes are made
distinct so independent function points do not collapse merely because their
unconstrained arrays would otherwise default to zero. Since replay evaluates the
original `Apply` and `Select` terms through those full values, any missed user
constraint or projection conflict can only reject the candidate.

## Validation

- The retained warm array-UF parent suite now has eleven tests.
- New direct-array-parameter gates cover:
  - SAT projection of two independent array-key function points with distinct
    result reads;
  - the private relation-flag count for that independent-key congruence path;
  - UNSAT when an asserted array equality forces those keys equal but result
    reads conflict; and
  - clean deferral for structural array-key arguments.
- The existing scalar-key, nested scalar UF, store/ITE parent, Bool/BV256,
  push/pop, one-shot-core, exact 64/65 cap, check_auto, and Z3 matrix gates
  remain green.

## Consequences

Direct array parameters no longer force retained warm array-valued UF parents
onto the fallback dispatcher. ADR-0093 subsequently closes the supported
store/constant/array-ITE structural-key part of the ADR-0088 deferral while
keeping the broader boundary explicit:

- nested array-valued application keys,
- nested/extended array components,
- memory BMC/k-induction,
- online array proof logging, and
- broader low-load aggregate timing

remain future work.
