# Lean recursive induction hypotheses: M3 importer result

Status: complete; M4 pinned computation differential and assurance update are
next

Date: 2026-07-22

Parent:
[TL2.12 execution plan](lean-recursive-induction-hypotheses-tl2.12-plan-2026-07-22.md)

Native prerequisite:
[M2 result](lean-recursive-induction-hypotheses-m2-2026-07-22.md)

Decision gate:
[ADR-0353](../research/09-decisions/adr-0353-preregister-lean-recursive-induction-hypotheses.md)

## 1. Result

The importer now treats Lean's `isReflexive` field as descriptive metadata,
not an admission permission bit. It still requires a syntactically valid
Boolean, but it neither grants nor denies support. The independently translated
family and constructor terms must pass the native kernel's strict positivity,
recursive-shape, recursor-generation, inference, and computation-rule checks.

No other importer policy was widened:

- one family and one exported recursor remain mandatory;
- `numNested` must remain zero;
- unsafe family, constructor, and recursor metadata remains rejected;
- generated constructors and recursors must compare against the official
  export before completion; and
- only EOF after all records publishes `CompletedImport`.

## 2. Exact official product observations

The two preregistered construct streams complete twice. The importer internally
compares generated constructor metadata/types plus recursor universe arity,
type, counts, rule constructors, `nfields`, and rule RHSs against the official
records.

| Stream | N/L/E/D | Admitted | Required completed names | Two-run result |
|---|---:|---:|---|---:|
| recursive-indexed | 34/4/132/4 | 12 | `MiniVector`, `MiniVector.rec`, `recursiveIndexedWitness` | 2/2 complete |
| reflexive/higher-order | 47/3/139/6 | 11 | `MiniAcc`, `MiniAcc.rec`, `reflexiveWitness` | 2/2 complete |

The direct-recursive control is re-imported before every construct row in both
runs and remains exact at 30 names, four levels, 130 expressions, five
declaration records, eleven admitted declarations, and zero axioms.

These target streams contain constructor witnesses, not recursor computations.
They receive exact admission/recursor-comparison credit only. M4 owns the first
Rust product execution of the separate M0 computation streams.

## 3. Bounded well-founded consequence

The mandatory construct-matrix regression exposed one legitimate downstream
transition: the frozen well-founded stream now completes at 160 names, five
levels, 731 expressions, 23 declaration records, 35 admitted declarations, and
zero axioms. Required completed names include `Acc.rec`,
`atomEmptyWellFounded`, and `wellFoundedWitness`.

This is not a source elaborator or general well-founded-recursion claim. The
official stream is already elaborated, and its kernel-level recursive
dependency is the now-supported `Acc.rec`. TL2.14 still owns native frontend
lowering for well-founded and nested definitions. M4 must update the generated
assurance matrix to distinguish this completed pre-elaborated stream from
frontend coverage.

The other non-target boundaries remain unchanged:

- the mutual stream returns `Unsupported` at line 233 with
  `inductive-mutual`;
- the nested stream returns the retained `Malformed` classification at line
  248 because a single-family import currently requires one recursor.

The nested diagnostic remains a separate TL1.8 classification issue; it is not
nested admission.

## 4. Metadata and publication mutations

Synthetic mutations are labeled separately from official-wire evidence.

The metadata-nonauthority test proves:

- changing valid `MiniVector` metadata from `isReflexive=false` to `true` does
  not remove its twelve-declaration completion;
- changing valid `MiniAcc` metadata from `true` to `false` does not remove its
  eleven-declaration completion;
- `numNested=1` still returns `inductive-nested`;
- `isUnsafe=true` still returns `declaration-unsafe`; and
- duplicating the family record still returns `inductive-mutual`.

Late recursor mutations occur after native family admission inside private
staging state and still return no `CompletedImport`:

- changed exported recursor type;
- changed exported minor count;
- changed official rule RHS; and
- changed official rule `nfields`.

All four return exact `Malformed` recursor-comparison diagnostics. Together
with the existing late I/O, record-limit, theorem, quotient, and rule mutations,
this closes the registered `reflexive-metadata-nonauthority` and
`late-failure-no-publication` classes.

## 5. Bounded validation

All commands used one Cargo build job and the repository's 4 GiB wrapper.

| Gate | Result |
|---|---:|
| complete `axeyum-lean-import` tests | 32 integration tests + 1 compile-fail doctest passed |
| construct matrix | 3 tests passed, including two complete runs per row |
| focused all-target/all-feature clippy with `-D warnings` | passed |
| focused rustdoc with `-D warnings` | passed |

The complete importer suite retains declaration identities, official flat,
projection, Nat-literal, and direct-recursive imports, owned completion,
resource/format failures, a 226-case wire mutation corpus, strict-positivity
propagation, and the updated construct matrix.

## 6. Claim boundary and handoff

M3 establishes exact importer completion for the two preregistered construct
streams and the bounded well-founded dependency stream. It does not yet claim
official recursor computation in Axeyum, pinned Lean/Axeyum computation
agreement, source elaboration, mutual groups, nested lowering, or full Lean
parity.

M4 next must reproduce both M0 computation stream identities, import each
twice, execute the selected recursor applications to their registered normal
forms, keep pinned Lean source acceptance separate, and regenerate the
assurance matrix from the new tested facts.
