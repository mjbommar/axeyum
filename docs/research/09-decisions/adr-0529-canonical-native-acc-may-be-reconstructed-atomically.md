# ADR-0529: Canonical native Acc may be reconstructed atomically

Status: accepted
Date: 2026-08-20
Index-summary: Theorem composition may reconstruct only the declaration-exact canonical native Acc package through the target kernel inductive gate

Related: [ADR-0525](adr-0525-missing-singleton-inductives-are-reconstructed-as-atomic-packages.md),
[ADR-0528](adr-0528-native-nat-mod-lt-uses-the-general-positive-denominator-contract.md),
[ADR-0508](adr-0508-native-prelude-composition-precedes-fibonacci-coprimality-search.md).

## Context

After native `Nat.mod_lt` adopted Lean's general contract, the unchanged
Mathlib r082 `Nat.dvd_gcd` composition control reached `Acc`. ADR-0525 allowed
only non-recursive singleton packages even though Axeyum's trusted
`Kernel::add_inductive` already checks the higher-order recursive field used by
accessibility, enforces positivity and parameter/index structure, generates
`Acc.rec`, self-checks its type, and registers its reduction rule atomically.

Removing the recursive prohibition for every singleton would be a much broader
policy than the measured demand. A source kernel can also assign the spelling
`Acc` to an unrelated recursive family, so matching names and declaration kinds
does not identify the official package.

## Decision

**Theorem-rooted composition may reconstruct the declaration-exact canonical
native `Acc`, `Acc.intro`, and `Acc.rec` package through the target kernel's
atomic inductive gate. Every other recursive or mutual package remains
unsupported.**

The V5 contract is:

1. The kernel-derived source closure must contain the complete family,
   constructor, and canonical recursor. Missing or reordered members decline
   before staging.
2. Recursive authority is restricted to the exact canonical declaration
   identities produced by the checked native logic prelude for `Acc`,
   `Acc.intro`, and `Acc.rec`. A recursive lookalike with the same names is not
   authorized.
3. Composition translates only the family and constructor inputs into a
   private clone. `Kernel::add_inductive` independently checks recursion and
   positivity and generates the target recursor; source recursor metadata is
   never inserted directly.
4. Before any theorem is admitted, the regenerated target identities for all
   three declarations must equal their canonical source identities. Any drift
   returns `ReconstructedInductiveMismatch` and publishes no kernel.
5. The completed receipt binds the ordered package, both identity maps, the
   environment transition, and an axiom-free theorem admitted over the
   package. Receipt schema advances to
   `axeyum.checked-theorem-composition.v5`.
6. Non-recursive singleton behavior remains unchanged. Generic recursive,
   nested, mutual, partial, axiom, opaque, quotient, and direct recursor
   transport remain outside the boundary.

## Evidence

Implementation commit `3d466b45c` adds focused controls for exact `Acc`
regeneration and reverification, incomplete closure rejection, rejection of a
recursive lookalike also named `Acc`, and unchanged caller ownership on error.
The 13 focused composition tests, all importer all-target tests, real-Lean
differential fixtures, Clippy with warnings denied, and formatting pass.

The immutable Mathlib 4.30.0 r082 observation is:

`/nas3/data/axeyum/autogenesis/probes/3d466b45c-canonical-acc-composition-v14/observation.json`

Its SHA-256 is
`9ed5aceb87ffd73797b48069ba38c1f62db8c001f43aa2bb584b3060136076dd`.
Two executions are byte-identical; the directory and observation are mode
`0555` and `0444`.

The dedicated `Acc.inv` control records an empty axiom footprint and exact
source/target identities:

| Declaration | SHA-256 |
|---|---|
| `Acc` | `a7f555ca45514f16479c09c35a226de796b93f9c023662a70b6ce0977cab9389` |
| `Acc.intro` | `355e47d711d54bd979a69cf06f7870dfde696721235e2b289bfaff844fbdecce` |
| `Acc.rec` | `d996fa21de5fff270d18473af734749f43cb3d2973db71ed0addac037883fc45` |

The unchanged `Nat.dvd_gcd` attempt passes this package and now reaches a later
target-kernel check:

```text
AdmissionRejected { name: "Nat.div_mod_exec", error: "TypeMismatch { ... }" }
```

The caller environment identity is unchanged before and after. The probe makes
24 successful kernel submissions across its positive controls, invokes no
proof search, inspects no held-out partition, and writes no ledger fact.

## Alternatives

### Permit every recursive singleton

Rejected. The measured demand is one canonical prelude package. General
recursive and nested families have a larger representation surface and should
earn authority from their own target-kernel and mutation evidence.

### Copy the source recursor declaration

Rejected. Its type and reduction rules are consequences of the inductive
package. Regenerating them is the point of the trusted target gate.

### Accept a same-name structural lookalike

Rejected. Names and coarse metadata do not establish the accessibility
contract. Exact canonical identities make the narrow allowance auditable.

## Consequences

The library/import arrow can now carry the accessibility primitive needed by
native Nat proofs without extending authority to a recursive-inductive class.
This closes the `Acc` boundary and exposes `Nat.div_mod_exec` proof translation
as the next bottom-up seam. That rejection must be diagnosed at expression
level before changing either the theorem or the composition policy.
