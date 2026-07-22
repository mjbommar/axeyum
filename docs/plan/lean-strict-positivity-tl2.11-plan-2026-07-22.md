# Lean strict positivity: TL2.11 execution plan

Status: M1 trusted preflight complete; M2 public-family matrix and generated
grammar next

Date: 2026-07-22

Decision gate:
[proposed ADR-0352](../research/09-decisions/adr-0352-preregister-lean-strict-positivity.md)

Current checkpoint:
[M1 trusted-preflight result](lean-strict-positivity-m1-2026-07-22.md)

Parents:

- [Lean implementation plan](lean-system-implementation-plan-2026-07-21.md)
  (TL2.11 before TL2.12);
- [Lean compatibility roadmap](lean-system-compatibility-roadmap-2026-07-21.md);
- [P6.0 kernel trustworthiness](../prover-track/plan/P6.0-kernel-trustworthiness.md)
  (T6.0.2);
- [official construct-matrix handoff](lean-official-construct-matrix-final-2026-07-22.md).

## 1. Objective and boundary

Land the trusted strict-positivity guard that must exist before Axeyum admits
recursive-indexed or reflexive/higher-order inductives. This milestone changes
classification of known-bad families from incidental feature rejection to an
explicit positivity rejection. It does **not** broaden the admitted inductive
fragment.

At completion:

- direct-recursive non-indexed families remain admitted;
- positive recursive-indexed and reflexive families pass the new guard, then
  retain `RecursiveIndexedNotSupported` or
  `ReflexiveOrNestedNotSupported`;
- negative or invalid family occurrences fail before provisional environment
  insertion;
- every failure leaves the public environment unchanged;
- TL2.11/T6.0.2 become DONE, while TL2.12--TL2.14 remain TODO.

## 2. Pinned authority

Use Lean 4.30 at commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`. The implementation authority is
`src/kernel/inductive.cpp`:

- `is_ind_occ`/`has_ind_occ`: identify every occurrence of a family being
  declared by constant name;
- `is_valid_ind_app`: require exact family constant/universe application,
  fixed parameters, complete index arity, and occurrence-free indices;
- `check_positivity`: WHNF, accept no occurrence, reject occurrence in a `Pi`
  domain, recurse through the instantiated codomain, otherwise require a valid
  family application;
- `check_constructors`: apply the rule to every non-parameter field for safe
  inductives.

Axeyum's initial scope has one declared family, no unsafe bypass, and no mutual
group. These restrictions simplify the occurrence set but do not weaken the
rule for the representable profile.

## 3. Executable rule

For family constant `I`, fixed opened parameters `P`, declared index count `k`,
and constructor field type `t`:

```text
positive(t):
  t := whnf(t)
  if I does not occur in t:
    accept
  else if t = Pi (x : d), c:
    if I occurs in d: NonPositive
    else positive(c[x := fresh])
  else if t = I P i_1 ... i_k
          and no I occurs in any i_j:
    accept
  else:
    InvalidOccurrence
```

Occurrence search is structural by family name, matching Lean. Valid-family
application compares the exact family head including universe levels, exact
argument count, and parameter expression identity. WHNF happens at each
recursive step. No general normalization or frontend nested-inductive lowering
is added.

## 4. Ordering and rollback contract

`add_inductive` currently inserts the inductive privately so later constructor
type inference can resolve `Const(I)`, then removes it on failure. TL2.11 adds a
separate preflight after the inductive parameter/index telescope is opened and
before that insertion:

```text
fresh-name/type checks
  -> open fixed parameters and count indices
  -> positivity preflight over raw constructor telescopes
  -> provisional private insertion
  -> existing type/feature/recursor checks
  -> completed admission
```

The preflight does not type-check constructors or claim they are otherwise
valid. Malformed-but-positive constructors continue to fail at the existing
typed checks. The ordering test snapshots the environment before the call and
requires exact equality after every positivity failure.

## 5. Typed result contract

Add two `KernelError` variants:

- `NonPositiveInductiveOccurrence { inductive, ctor, field_index }` for a
  family occurrence in a `Pi` domain;
- `InvalidInductiveOccurrence { inductive, ctor, field_index }` for every other
  containing term that is not a valid recursive application.

`field_index` is zero-based among non-parameter constructor fields. The error
must identify the first failing field in declaration/telescope order. Existing
feature-decline variants retain their meanings and payloads.

## 6. Preregistered case matrix

| ID | Field shape | Expected positivity result | Subsequent product result |
|---|---|---|---|
| `no-occurrence` | `Atom` | accept | ordinary non-recursive admission |
| `direct` | `I P` | accept | existing direct-recursive admission |
| `positive-pi-1` | `(x : A) -> I P` | accept | reflexive feature decline |
| `positive-pi-2` | `(x : A) -> (y : B x) -> I P` | accept | reflexive feature decline |
| `recursive-indexed` | `I P i` with occurrence-free `i` | accept | recursive-indexed feature decline |
| `negative-domain` | `(x : I P) -> A` | non-positive | stop before provisional insertion |
| `mixed-polarity` | `(x : I P) -> I P` | non-positive | stop before provisional insertion |
| `deep-negative` | `(f : (A -> I P) -> A) -> I P` | non-positive | stop before provisional insertion |
| `wrong-parameter` | `I Q`, `Q != P` | invalid occurrence | stop before provisional insertion |
| `nested-application` | `F (I P)` | invalid occurrence | stop before provisional insertion |
| `self-index` | `I P (J (I P ...))` | invalid occurrence | stop before provisional insertion |
| `wrong-index-arity` | `I P` or `I P i j` when `k = 1` | invalid occurrence | stop before provisional insertion |

The matrix will cover `Prop` and `Type`, zero/one parameter, zero/one index,
multiple constructors, first/later failing fields, and deterministic rebuilds.

## 7. Generated adversarial grammar

Add a fixed-seed, deterministic structural generator over:

- leaves: no occurrence, canonical family, wrong-parameter family, family in an
  index, and family nested under a foreign head;
- contexts: positive `Pi` codomain, negative `Pi` domain, application, and
  reducible `let` wrapping;
- depths 0 through 4;
- parameter/index profiles 0/0, 1/0, and 1/1.

The generator carries an independently assigned expected class from the chosen
production, not from the kernel result. It must produce at least 256 unique
cases; repeat the complete run and compare the serialized summary byte-for-byte.
Every negative/invalid case snapshots the environment and checks the exact error
payload. Public-family tests separately ensure the full `add_inductive` path—not
only the traversal helper—enforces the result.

Stop rather than weaken the grammar if a supposedly well-formed control fails
for an unrelated kernel reason.

## 8. Official and importer differential

Reuse the already frozen official sources as immutable controls:

- direct recursion, `MiniVector`, and `MiniAcc` from
  `lean4export-v4.30-construct-matrix.lean` are official-positive;
- `NonPositive` from
  `lean4export-v4.30-construct-matrix-negative.lean` is official-negative.

M0 adds separately frozen negative source cases for mixed/deep polarity before
running them. Pinned Lean must reject them at its kernel positivity gate. The
Axeyum native cases model the corresponding core field shapes and must return
the registered typed errors. Since official Lean does not export rejected
declarations, a synthetic format-3.1 mutation may test importer propagation but
must be labeled synthetic and receives no official-wire credit.

The official cross-check is mandatory locally for milestone acceptance and in
CI under `AXEYUM_REQUIRE_LEAN=1`. Missing Lean fails closed in that profile.

## 9. Milestones

### M0 — preregistration and source freeze

- commit ADR-0352 and this plan;
- freeze added negative source cases, hashes, expected rule classes, exact Lean
  command, and 4 GiB/one-worker policy before running them;
- keep all semantic code unchanged;
- push and verify remote equality.

### M1 — trusted preflight and typed errors

- add the two error variants;
- implement occurrence search, valid-family application, and recursive
  positivity preflight;
- place the preflight before provisional environment insertion;
- add exact unit tests for the executable rule and ordering;
- commit and push.

### M2 — public-family matrix and generated grammar

- cover all registered rows through `add_inductive`;
- add the >=256-case deterministic generator and repeated summary;
- preserve direct recursion and exact existing deferred outcomes;
- run focused clippy/rustdoc/rustfmt under bounded resources;
- commit and push.

### M3 — official/import boundary

- run pinned Lean twice on every frozen source case;
- add the mandatory official differential test;
- add a synthetic importer propagation mutation if it can preserve an exact,
  type-correct format boundary without weakening the source/wire distinction;
- run the immutable official construct-matrix control to prove no outcome drift;
- commit and push.

### M4 — closure and handoff

- accept or reject ADR-0352 from its exits;
- close the research question;
- mark TL2.11 and T6.0.2 DONE only if every gate passes;
- synchronize PLAN, STATUS, project state, both Lean roadmaps, and docs index;
- hand off to the combined TL2.12 recursive-indexed/reflexive implementation;
- commit, push, and verify local/tracking/remote equality.

## 10. Resource and validation gates

- Lean: one worker, `MemoryHigh=3G`, `MemoryMax=4G`, bounded cgroup, exact
  pinned binary;
- Rust: at most two build jobs, 4 GiB wrapper/cgroup where applicable;
- no unbounded workspace-wide run while unrelated dirty work remains;
- kernel unit/integration/doctest suites;
- importer suite and official construct-matrix regression;
- focused clippy with warnings denied, rustdoc with warnings denied, and focused
  rustfmt;
- positivity generator repeated summary;
- parity-document, foundational-resource, and link validators;
- `git diff --check` and explicit staged-file audit.

The known unrelated workspace-wide rustfmt failures remain outside this
milestone and must not be reformatted incidentally.

## 11. Stop conditions

Stop and amend the decision/result before continuing if:

1. pinned Lean disagrees with the registered rule class;
2. a positive deferred official shape fails positivity;
3. a negative/invalid case reaches provisional environment insertion;
4. direct-recursive admission or computation changes;
5. the generated summary is nondeterministic or contains duplicate identities;
6. an error path leaves any inductive/constructor/recursor declaration behind;
7. the checker needs mutual-group information unavailable to the current API;
8. a required gate exceeds 4 GiB or needs unbounded parallelism;
9. unrelated dirty work overlaps a target path.

## 12. Explicit non-claims

TL2.11 does not establish:

- recursive-indexed, reflexive, mutual, nested, or well-founded admission;
- positivity for mutual groups before TL2.13 generalizes the occurrence set;
- native nested-inductive elimination/lowering;
- source parsing or elaboration compatibility;
- full Lean-kernel parity or a consistency proof;
- computation credit from official source acceptance.
