# Type-slice receipt foundation

Date: 2026-08-19

## Result

The checked type-slice path now emits a content-addressed v1 receipt after all
three semantic checks succeed:

1. explicit constant generalization in the validated source kernel;
2. root-selected transport and proof-isolated admission in a fresh kernel; and
3. exact source-constant specialization back to the original proposition.

`issue_type_slice_receipt` binds:

- the complete source-stream SHA-256 supplied by the replay boundary;
- Lean, exporter, wire-format, and declaration-identity versions;
- the source target declaration and original goal identities;
- the sliced goal and fresh target identities;
- each binder's position, source declaration content identity, exact universe
  identities, instantiated type identity, and expanded source occurrence count;
- every declaration retained in the fresh producer environment, including its
  kind, content identity, and dependency identity; and
- the successful exact-specialization result.

The receipt SHA-256 covers canonical compact JSON excluding only its own digest.
`has_valid_digest` recomputes it after transport. The executable control mutates
the policy field and observes digest failure.

## Checked control

The synthetic control starts from an exported source environment containing
two axioms, `Source.Carrier` and `Source.value`, plus a concrete equality goal.
The ordinary importer validates that broad source. The slicer turns the two
constants into a dependent telescope, then the root-selected exporter and
statement adapter construct a new kernel in which neither source axiom exists.

The receipt issuer independently observes two expanded occurrences for each
source constant, recomputes their declaration identities from the supplied
kernel, requires the goal to be the exact source target value, verifies the
exact two source arguments, compares the sliced goal identity across kernels,
rejects a wrong bound argument and a forged source manifest, and records only
proof-free declarations in the retained environment.

## Assurance boundary

This remains a receipt foundation, not Mathlib production evidence. The issuer
binds the source-stream digest supplied by its caller; it does not reopen and
hash external bytes. A production replay wrapper must recompute that digest,
re-import those exact bytes, resolve abstraction keys by declaration content
and universe identity, rebuild the slice, and compare the complete receipt.

Automatic selection is also still outside the trusted operation. No nursery
row has been credited and held-out remains sealed. The next measured step is a
train/development-only replay tool that derives candidate abstractions from the
frozen syntactic census, then lets these checked mechanisms accept or decline
each candidate.

## Reproduction

```sh
cargo test -p axeyum-lean-import --test type_slice_generalization \
  receipt_binds_source_abstractions_fresh_environment_and_specialization
cargo clippy -p axeyum-lean-import --all-targets -- -D warnings
```
