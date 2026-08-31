# Lane l3-d1-declaration-spec — L3 phase D1: declarative declaration spec

<!-- plan-section: lane-status -->

## Status: pilot landed

Task: `docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`,
phase D1. Design and TCB argument: ADR-0965.

## Pilot subsystem

`Nat.squarefreeAux` / `Squarefree` (`crates/axeyum-lean-kernel/src/nat_prelude/squarefree.rs`,
landed 2026-08-30 by a sibling lane, read-only — not edited). Chosen because
it is two `Definition`s with zero theorems, so a spec-driven generator for it
has no proof term to get right or wrong — the kernel's admission gate is the
only place correctness is decided, exactly as for the hand-written version.

## What was built

- `artifacts/declaration-spec/schema.json` — versioned (`spec_version: 1`)
  JSON Schema for a declaration-spec file: names, universes, binders, a
  small typed expression DSL for types/values, dependencies, build phase,
  equations, and the `mirrors_existing` escape hatch (see below).
- `artifacts/declaration-spec/nat-squarefree.json` — the pilot spec,
  describing the same two declarations `squarefree.rs` builds by hand,
  including the exact eta-long recursor-application shape the hand-written
  code uses (see "what the digest comparison found").
- `artifacts/declaration-spec/negative-fixtures/*.json` — five adversarial
  fixtures, each isolating exactly one guard: `dup-name-in-corpus.json`,
  `dup-name-cross-prelude.json` (reproduces the real `Nat.inverseIndex`
  collision by name), `missing-phase.json`, `dependency-cycle.json`,
  `dep-mismatch.json`.
- `scripts/gen-declaration-spec.py` — validates a spec corpus (six guards:
  in-corpus duplicate name, cross-prelude duplicate name against a real
  kernel name snapshot, missing/invalid phase, dependency cycle, phase
  order, dependency/const_ref consistency) and emits generated Python
  types, a generated Rust name/equation constant table, and an inventory
  JSON.
- `crates/axeyum-lean-kernel/examples/declaration_spec_pilot.rs` — the
  generic expression-DSL interpreter (not per-declaration codegen): walks
  the spec's JSON expression trees and calls the same public `NatOps`
  builder methods `squarefree.rs` calls by hand, admits the result under
  shadow names (`<name>SpecGen`) in the SAME kernel instance as the
  hand-built prelude, and compares. `--dump-names` mode builds the Int
  prelude (a superset of Nat that also declares `Nat.inverseIndex`) and
  dumps every declared name for the cross-prelude guard.
- `scripts/check-declaration-spec.py` — the gate: builds the example
  (release), dumps the name snapshot, validates the pilot spec, requires
  each of the five negative fixtures to fail with its OWN guard tag (not
  just "fail"), runs the pilot binary and requires
  `verdict=DIGESTS_IDENTICAL` with nonzero declaration/equation counts,
  and checks generated-artifact freshness.
- `scripts/tests/test_declaration_spec.py` + a `declaration-spec` entry in
  `scripts/tests/mutation_controls.py` — 8 unit tests, 7 of which are each
  the control for exactly one guard mutation.
- Registered as `declaration-spec` in `justfile`'s `check:` recipe (one
  name appended) and as a `step` at the end of `scripts/check.sh`.
- `crates/axeyum-lean-kernel/Cargo.toml`: added `serde_json = "1"` as a
  dev-dependency (JSON parsing for the example only; `sha2` was already
  present from a sibling D2 lane's `structural_index_extract.rs` and is
  reused here for the digest, adding no new dependency).
- `.gitignore`: one line excluding the regenerated kernel-name snapshot
  (a build artifact of the current tree, not a stable pin).

## Digest comparison result: IDENTICAL, measured

`declaration_spec_pilot`'s default run:

```
DECLARATION_SPEC_PILOT|decl=squarefreeAux|is_leaf=true|identical_expr_id=true|identical_digest=true|...
DECLARATION_SPEC_PILOT|decl=Squarefree|is_leaf=false|identical_expr_id=false|identical_digest=true|...
DECLARATION_SPEC_PILOT|order_identical=true|order=["squarefreeAux", "Squarefree"]
DECLARATION_SPEC_PILOT|duplicate_name_refused_by_kernel=true
DECLARATION_SPEC_PILOT|equations_checked=7|equations_passed=7|equations_failed=0
DECLARATION_SPEC_PILOT|verdict=DIGESTS_IDENTICAL|declarations_checked=2|equations_checked=7
```

`squarefreeAux` (the leaf declaration, no dependency on a spec-sibling)
achieves literal `ExprId` identity: because this kernel hash-conses
expressions (`Kernel::intern_expr`), two structurally identical terms built
by two different code paths (the hand-written Rust and the generic
interpreter) intern to the SAME `ExprId`, not merely an equal one.
`Squarefree` (which calls `squarefreeAux`) cannot achieve literal `ExprId`
identity by construction, since the generated copy is declared under a
shadow name to coexist with the hand-written one in the same kernel and so
references a different `NameId` — `identical_digest` (computed after
stripping exactly that one cosmetic suffix, see
`normalize_shadow_names`'s doc comment) is the correct bar for it, and it
holds.

**What the digest comparison actually found, before it was fixed:** the
first version of the pilot spec's `squarefreeAux` recipe was semantically
equivalent to the hand-written version (all 7 equations passed) but was NOT
structurally identical — the hand-written code eta-expands the recursor
result with an extra outer lambda + application
(`fun n => fun fuel => fun k => (Nat.rec ...) k`) that the first spec
recipe omitted (`fun n => fun fuel => (Nat.rec ...)`, arity 2 not 3). This
is exactly the exit criterion doing its job: a semantically-correct-by-
equations, structurally-different generated declaration counts as a
MISMATCH, not a pass, and the fix was to match the hand-written recipe's
exact shape. The equation checks alone would never have caught this
(eta-equivalent terms compute identically); only the identity/digest
comparison did.

## TCB: what is generated, and which side of the line it is on

Nothing generated is a proof term. `Definition`s have no proof body — the
kernel accepts one once its value type-checks against its stated type,
which is true of any well-typed total function whether or not it computes
the intended value (this crate's CLAUDE.md: "the trusted gate cannot tell
you a `Definition` is wrong — only evaluation can"). So:

- **Outside the TCB, pure registration boilerplate:** the JSON spec itself;
  the generated Python dataclasses; the generated Rust name/phase/
  dependency/equation constant table (`nat_squarefree_names.rs`); the
  generated inventory JSON. None of these are consulted by the kernel at
  admission time.
- **Outside the TCB but load-bearing at runtime, same status as any other
  hand-written builder code:** the expression-DSL interpreter
  (`eval`/`parse_node` in `declaration_spec_pilot.rs`). It calls the exact
  same `NatOps` methods a human would; a bug in it produces a kernel
  REJECTION (ill-typed term) or a wrong VALUE (caught by the equation
  checks and the digest comparison), never a false theorem, because there
  is no theorem here.
- **What would have to be true for a generated artifact to enter the
  TCB:** if a future spec described a *Theorem*'s proof term (not just a
  Definition's value, or a Theorem's public signature for accessor
  generation), the interpreter constructing that proof term would need the
  same scrutiny as any hand-written proof — reviewed, and re-checked from
  scratch by `Kernel::add_declaration` exactly as today. This pilot
  deliberately does not attempt that; the schema's `kind` field only
  accepts `"Definition"` and the generator/interpreter both reject anything
  else.

## The three (plus two) pre-construction checks, demonstrated firing

All via `scripts/check-declaration-spec.py`, each against a real adversarial
fixture, before any kernel construction of the PROPOSED content is
attempted:

- **Cross-prelude duplicate name** — `dup-name-cross-prelude.json` proposes
  `Nat.inverseIndex`, reproducing the actual 2026-08-25 collision
  (`int_prelude/wilson.rs` already declares `Nat.inverseIndex` from the Int
  prelude into the Nat namespace; the case CLAUDE.md documents as invisible
  to any check scoped to one prelude's own files). The guard compares
  against a snapshot of the REAL kernel's full name inventory (1,198 names,
  dumped via `--dump-names` from the Int prelude, a superset of Nat), not
  against the spec corpus alone, and refuses with `GUARD:CROSS_PRELUDE_DUPLICATE`
  naming the exact collision.
- **In-corpus duplicate name** — `dup-name-in-corpus.json`, two
  declarations in one file both named `Nat.fixtureDup`; refused with
  `GUARD:DUPLICATE_NAME`.
- **Missing phase** — `missing-phase.json`; refused with `GUARD:MISSING_PHASE`.
- **Dependency cycle** — `dependency-cycle.json`, two declarations each
  depending on the other; refused with `GUARD:DEPENDENCY_CYCLE` (and also
  `GUARD:PHASE_ORDER`, a second guard the same fixture trips — see the
  fixture's own `_comment` for why phase numbers alone are not a
  sufficient cycle check).
- **Dependency/const_ref consistency** (extra, not in the roadmap's named
  three but load-bearing): `dep-mismatch.json`, a declaration whose value
  recipe references a sibling declaration via `const_ref` without listing
  it in `dependencies`; refused with `GUARD:DEP_MISMATCH`.

The pilot spec itself passes all six guards (`mirrors_existing: true` is
set on both its declarations specifically because it deliberately describes
an ALREADY-LANDED subsystem for this digest-parity demonstration — the
field is documented in the schema as never permitted on a spec proposing
genuinely new work, and none of the five negative fixtures set it).

## Absence check

`scripts/check-declaration-spec.py` fails, with a named reason, on: a
failed build; a zero-name snapshot; the pilot spec failing validation; ANY
negative fixture passing validation (guard did not fire) OR failing for the
WRONG guard; the pilot binary reporting anything other than
`verdict=DIGESTS_IDENTICAL`; zero declarations or zero equations checked;
or generated-artifact drift. `gen-declaration-spec.py` itself additionally
fails on an empty spec corpus and on zero total declarations across a
corpus that parsed.

## Guard -> test kill table (mutation-verified, own worktree only)

`python3 scripts/tests/mutation_controls.py declaration-spec`:

| Guard mutated | Kill count | Killed test |
| --- | --- | --- |
| in-corpus duplicate name guard | killed 1 | `DuplicateNameInCorpusGuard.test_fires` |
| cross-prelude duplicate name guard | killed 1 | `CrossPreludeDuplicateGuard.test_fires` |
| dependency cycle guard | killed 1 | `DependencyCycleGuard.test_fires` |
| phase order guard | killed 1 | `PhaseOrderGuard.test_fires` |
| dependency/const_ref consistency guard | killed 1 | `DepMismatchGuard.test_fires` |
| missing-phase guard (reporting line) | killed 1 | `MissingPhaseGuard.test_fires` |
| empty-corpus guard (zero spec files) | killed 1 | `EmptyCorpusGuard.test_fires` |

Baseline: 8 tests green. Every one of the 7 registered mutations kills
exactly 1 test; no mutation is unaccounted for, no guard sits outside this
table. One mutation (`empty-corpus`) initially SURVIVED because the
replacement text I wrote for it accidentally still contained the substring
the control was checking for (`"...no longer says no spec files found"`
still contains "no spec files found") — caught by actually running the
harness rather than assuming the mutation text was adversarial enough, and
fixed before landing.

## Hand-maintained registration surface removed, measured

For this ONE pilot subsystem, the hand-written route
(`nat_prelude/squarefree.rs` + `nat_prelude.rs`) requires editing THREE
separate places per declaration: a struct field
(`pub squarefree_aux: NameId`), a name-interning line
(`squarefree_aux: kernel.name_str(nat, "squarefreeAux")`), and a dispatch
call (`declare_squarefree_all(&mut d, &p)?;`) — 3 surfaces x 2 declarations
= 6 hand-edited sites, in 2 different locations of a 6,000+ line shared
file (`nat_prelude.rs`), per CLAUDE.md's architecture-review citation of
this exact fusion pattern. The spec-driven route needs ONE file (the JSON
spec) and ZERO edits to any shared prelude file — the comparison pilot
deliberately declares under shadow names rather than replacing the hand
declarations, so this session did not remove the 6 existing hand-written
sites (they are read-only, sibling-owned), but a NEW subsystem of this
shape would need 0 of the 3 hand-maintained surfaces instead of 3 per
declaration.

## Does this scale past the pilot?

Only partially, honestly stated. The expression DSL is deliberately narrow
— exactly what this pilot subsystem needs (arrow types, non-dependent
lambdas, one `Nat.rec` shape with a non-dependent motive, and the
primitive `NatOps` arithmetic/boolean operations) — and every subsystem
audited while choosing a pilot (`nth_root.rs`, `matrix_transpose.rs`) uses
at least one construction this DSL does not yet cover (well-founded
recursion, a dependent motive, a different carrier's primitives). Adding
those is mechanical (one more `Node` variant and interpreter arm per
shape) but real work, and a genuinely proof-bearing subsystem is out of
scope by design (see the TCB section) until a separate, harder decision is
made about how a *signature-only* spec for a Theorem would be checked
against its hand-written proof. What DOES generalize immediately: the
guard set (duplicate name — both shapes — missing phase, dependency cycle,
phase order, dependency consistency) is subsystem-agnostic and would catch
the same class of defect for any future spec using this schema.
