# Checked definition composition

## Result

The public theorem-rooted composition boundary now reconstructs demanded
definitions through the target kernel. On the pinned axiom-free Mathlib 4.30.0
`r082` stream, the unchanged `Nat.eq_one_of_dvd_one` root independently admits:

- exact `Nat.mul` with reducibility `regular:2`;
- exact `Nat.dvd` with reducibility `regular:4`;
- the exact `Exists` / `Exists.intro` / target-generated `Exists.rec` package;
- eight dependent theorems, each with an empty kernel-derived axiom footprint.

This closes the definition demand measured by the preceding singleton-package
increment. It does not copy source environment entries: names, universe
parameters, types, values, and reducibility are rebuilt in a private target
clone, then every definition passes ordinary `Kernel::add_declaration` before
the completed clone can be published.

## Exact evidence

The implementation checkpoint is `acade2a4594d217324961a41743f6c36bd90e97f`.
Its immutable observation is:

`/nas3/data/axeyum/autogenesis/probes/acade2a45-definition-composition-v10/observation.json`

The bound identities are:

| Artifact | SHA-256 |
|---|---|
| Probe source | `d67f884e8bf38ce1df694f43a1c3fa86fd9d0d329a01dc0e4324fa4cf21fda40` |
| Composition API source | `3d5990a4a26162d9002d36125d4510cdf0965696679681cc265cce22dfa27fe7` |
| Observation | `099019607493973cc6f4a4cc18b6894fdd4fe836b86318da25d9ee1f4728fd5f` |
| Definition-control receipt | `9ac9ace96e64d1bd9cd8131ebe1f2f7404cc93b4ed9d962ae55ffe51ef200cd0` |

The target environment changes from
`82ac7b0143bdd9891b666a37220fb91b86afc4af4b920d68773d80b5c9348855`
to
`292873e9fc64286387e7932bddd74ea3f781289d0c9e141d2312845ba4668132`.
Both definition declaration digests are identical across source and target.
The receipt also records 18 kernel-type-shape reuses and four translated
definitional-equality reuses; compatibility remains permission to attempt a
fresh target check, not proof credit.

## Trust boundary

[ADR-0526](../research/09-decisions/adr-0526-missing-definitions-are-rebuilt-and-checked-in-dependency-order.md)
fixes the V4 boundary:

- theorem roots select the source closure;
- definitions and theorems follow checked dependency order;
- singleton inductives still use their atomic target gate first;
- any rejection discards the entire private clone;
- axioms, opaques, quotient declarations, recursive/mutual inductives, partial
  packages, and conflicting declarations receive no new authority.

The manifest checker pins the observation's immutability, source/API hashes,
definition names and order, exact declaration identities, reducibility hints,
theorem footprints, compatibility classes, receipt, environment transition,
and authority count. Mutation tests independently break each new semantic
field and require the checker to fail.

## Next measured gap

The larger unchanged `Nat.dvd_gcd` root no longer stops at a missing
definition. It reaches `Bool.rec`, where the imported recursor orders its
`false` branch before `true` and the native recursor type orders those premises
the other way around. The control declines with `TypeShapeMismatch`, and its
target environment digest is unchanged.

That is a representation problem, not a reason to weaken reuse. The next
increment should compare the native Bool package against official Lean's
constructor order, measure the blast radius of correcting it, and retain an
independent target-kernel replay. A generic branch-permutation transport would
be broader than the evidence supports.

## Reproduction

```sh
CARGO_TARGET_DIR=/data0/axeyum/codex-definition-target \
  cargo run -p axeyum-lean-import \
  --example nat_prelude_composition_probe -- \
  /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r082.ndjson \
  /path/to/observation.json

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```
