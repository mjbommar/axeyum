# Lean U2 TL0.6.5 R2 plan — derived comparison outcomes

Date: 2026-07-23  
Status: **preregistered schema correction; no process or parity credit**  
Owner: complete Lean parity lane, TL0.6.5 M1

## 1. Defect and boundary

R1 made every execution, comparison, cell, and population authority
content-bound. It did not make the comparison taxonomy *derived*. Under the R1
schema, two sealed `complete` execution records can still declare
`agree-success` without proving that both sides succeeded or that their
normalized observables agree.

R2 closes that declarative-classification path before any real paired cell
exists. It changes only the synthetic terminal schema and validator. It does
not consume a TL0.6.3 or TL0.6.4 parent, derive a comparison-obligation
authority, implement a layer normalizer, launch official Lean or Axeyum, or
grant population, axis, gate, performance, or parity credit.

## 2. Per-side result class

Each `official` and `axeyum` execution record gains nullable `result_class`:

| Value | Meaning |
|---|---|
| `success` | the selected layer produced its admitted successful semantic result |
| `reject` | the selected layer produced a completed semantic rejection |
| `decline` | the system completed with an explicit supported-fragment decline |
| `timeout` | the selected attempt completed with a validated timeout class |
| `resource-exhaustion` | the selected attempt completed with a validated memory/PID/disk resource class |
| `failure` | the attempt completed but produced another non-semantic failure result |

`record_state = complete` requires exactly one class. `not-run` and `invalid`
require JSON `null`; an untrusted or absent execution cannot publish a semantic
result. The existing `outcome_sha256` remains the exact detailed observed
outcome identity. The class is only its comparison-level projection and is
sealed by `record_sha256`.

## 3. Normalized-observable identities

The comparison gains distinct `official_normalized_sha256` and
`axeyum_normalized_sha256` fields. A non-null value identifies the canonical
selected-observable projection produced under the comparison's exact
`normalization_id`, `normalization_sha256`, and `contract_sha256`.

- a non-`complete` side requires JSON `null`;
- a `complete` side may be null only when the layer normalizer or equivalence
  decision is unavailable, which forces `unadjudicated` whenever normalized
  equality is needed;
- equal digests mean canonical normalized byte equality;
- unequal digests mean a semantic difference for same-class successful or
  rejecting results; and
- comparison sealing binds both normalized identities and both execution
  record seals.

This v1 rule deliberately uses canonical-byte equality. A future equivalence
procedure that accepts distinct canonical bytes requires a separately
specified, independently checkable result—not an opaque boolean added to this
record.

## 4. Exact derived taxonomy

State derivation occurs first:

1. any `invalid` side derives `invalid-run`;
2. otherwise any `not-run` side derives `not-run`; and
3. all remaining classes require two `complete` sides with valid result
   classes.

For two complete sides, the validator derives:

| Official class | Axeyum class | Normalized identities | Derived outcome |
|---|---|---|---|
| `success` | `success` | both present and equal | `agree-success` |
| `success` | `success` | both present and unequal | `semantic-mismatch` |
| `success` | `success` | either absent | `unadjudicated` |
| `reject` | `reject` | both present and equal | `agree-reject` |
| `reject` | `reject` | both present and unequal | `semantic-mismatch` |
| `reject` | `reject` | either absent | `unadjudicated` |
| `success` | any non-`success` class | ignored for direction | `official-only` |
| `reject` | `success` | ignored for direction | `axeyum-only` |
| any remaining valid pair | any | any | `unadjudicated` |

The declared `comparison.outcome` must equal this derived value exactly.
`unadjudicated` is therefore not an escape hatch for a known unequal pair, and
agreement cannot be asserted from completion alone.

## 5. Required controls

The implementation checkpoint must include:

1. positive derivation for all eight terminal outcome classes;
2. different execution-local identities with equal normalized identities
   deriving agreement (the ignored-field control);
3. a changed normalized identity, with every enclosing seal correctly
   recomputed, rejecting stale agreement and deriving `semantic-mismatch`;
4. a changed side result class, with every seal and citation recomputed,
   rejecting a stale directional/agreement claim;
5. a missing normalized identity preventing same-class semantic agreement and
   deriving `unadjudicated`;
6. a result class on `not-run` or `invalid` rejecting;
7. a normalized identity on `not-run` or `invalid` rejecting; and
8. unchanged count/ID/cell-seal authority, G3, and terminal-claim controls.

All controls are synthetic. They validate representation and derivation only;
they do not validate any future layer-specific normalizer.

## 6. Primary references

- Lean v4.30.0's pinned
  [test-suite contract](https://github.com/leanprover/lean4/blob/v4.30.0/tests/README.md)
  separately declares expected exit behavior and expected/ignored output.
- [BenchExec's result classification](https://github.com/sosy-lab/benchexec/blob/main/benchexec/result.py)
  separates a tool's result class from correct, wrong, unknown, missing, and
  error categories.
- The [SMT-COMP 2025 rules](https://smt-comp.github.io/2025/rules.pdf)
  distinguish `sat`/`unsat`, `unknown`, abort, erroneous answers, and validated
  model outcomes rather than treating process completion as correctness.

These are methodology references. R2 neither adopts their exact taxonomies nor
changes Axeyum's accepted execution-evidence policy.

## 7. Exit and nonclaims

R2 exits only when the exact schema, derived classifier, mutation controls,
deterministic generated artifacts, full parity documentation gate, link gate,
and differently rooted detached-worktree replay pass. The final result must
continue to report zero Axeyum outcomes, zero paired cells, zero complete
paired-population authorities, zero satisfied terminal gates, and terminal
parity false.

