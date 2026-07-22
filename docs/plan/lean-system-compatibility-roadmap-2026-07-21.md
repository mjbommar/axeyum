# Lean-system compatibility: evidence audit and staged roadmap

Status: proposed implementation program

Date: 2026-07-21

Decision gate: [proposed ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md)

## Executive conclusion

Axeyum already has an independent, pure-Rust implementation of a meaningful
Lean 4 **kernel-compatible checking slice**. It does not bundle Lean, call into
Lean to type-check terms, or expose Lean FFI objects. Official Lean is an
external differential oracle. On the current representative generated lane,
official Lean 4.30 accepts 71/71 emitted modules. That result is real and useful,
but it is evidence about a selected reconstruction surface, not parity with the
Lean language or ecosystem.

The missing surface is not one bug called “Lean parity.” It is at least eight
separate systems: import, kernel admission breadth, source parsing/macros,
elaboration/unification, interactive tactics, compilation, package management,
and editor services. Mathlib is a ninth and qualitatively different axis: a
large generic theorem and tactic library, not a kernel feature.

The recommended strategy is therefore:

1. preserve the independent Rust checker as the small trusted path;
2. add a versioned, fail-closed `lean4export` NDJSON import path;
3. use import declines to drive kernel breadth, rather than guessing at all of
   Lean's implementation at once;
4. build the existing certificate-first goal/tactic track on that checker;
5. integrate with official Lean, Lake, and the Lean language server through an
   optional sidecar/plugin profile before cloning those systems;
6. treat mathlib as an import/cross-check and tactic-integration target, not as
   something Axeyum should reimplement file for file.

This closes useful portions of the gap without putting the official Lean
runtime in the default TCB, sacrificing WASM, or making “we parsed a file” mean
“we checked its declarations.” A full independent replacement for Lean's
parser, macro expander, elaborator, compiler, Lake, language server, and mathlib
would be a multi-person-year program. It remains a north-star option, not the
next milestone.

## 1. Define the target before measuring it

“Speaks Lean” can mean five materially different things. Every status report
must name which one it means.

| Target | Meaning | Current bounded evidence | Status |
|---|---|---|---|
| Lean-source output | Axeyum renders `.lean` modules that official Lean accepts | fail-closed 71/71 representative-family gate | implemented on a selected reconstruction slice |
| Independent Lean-core checking | Rust code implements names, universes, expressions, environments, reduction, definitional equality, type checking, and selected inductives | `axeyum-lean-kernel`, no runtime dependencies or `unsafe` | substantial selected slice, not complete Lean kernel admission |
| Lean declaration import | consume definitions/theorems from an official versioned interchange and check them independently | Rust format-3.1 reader admits the official flat fixture as 8 checked declarations and direct-recursive `MiniNat`/`MiniList` as 11 more | initial flat/direct-recursive profiles implemented; broad imports open |
| Lean language compatibility | parse, expand macros, elaborate overloaded/implicit source, run tactics, produce information trees | no Lean frontend implementation | absent |
| Lean workflow/ecosystem compatibility | Lake packages, `.olean` cache behavior, editor/LSP, mathlib project workflows, compiler/runtime | no compatible workflow today | absent; adapter-first roadmap below |

The first two rows answer the narrow question “is ours independent?” with yes.
The last three answer “is it a Lean replacement?” with no. Neither answer
invalidates the other.

## 2. What Axeyum actually has

This inventory was taken from the current 22-crate workspace, not inferred from
the README.

### 2.1 Independent kernel and reconstruction

`crates/axeyum-lean-kernel/` contains a Rust implementation of Lean-style:

- hierarchical names, universe levels, and locally nameless expressions;
- deterministic hash-consing with lifetime-free IDs;
- declarations and environments;
- weak-head reduction and definitional equality;
- type inference/checking and local contexts;
- proof irrelevance and selected inductive/recursor checking;
- arithmetic, integer, string, and logic preludes used by reconstruction.

Its crate forbids `unsafe`, has no runtime dependency on Lean, and is adapted
from the independently implemented `nanoda_lib` design rather than wrapping the
official kernel. The existing source module documentation still described the
initial data-structure-only slice and is corrected alongside this roadmap.

The proof producers and reconstruction routes are broader than the kernel crate
alone. `axeyum-solver` emits checked evidence across clausal, arithmetic, EUF,
and selected derived routes; generated Lean modules are accepted locally by the
embedded checker and optionally by an official Lean gate. The current official
gate is deliberately bounded: 71 representative generated families accepted by
Lean 4.30 does not imply all Lean declarations or mathlib are accepted.

### 2.2 Automation assets are present, but they are not Lean tactics

It would be wrong to summarize the repository as having “no automation.” It
has solver search, proof reconstruction, an e-graph explanation layer, a CAS,
and a default canonical rewrite manifest with 56 stable rule entries. The
distinction is that these are not exposed through Lean's tactic elaboration
protocol and most are not yet tactic steps in a `Goal`/`Hole` state machine.

Track 6 already specifies the correct certificate-first layer:

- P6.2: goals, holes, delayed assignment, and pattern unification;
- P6.3: `decide`, introduction/application, counterexample, `simp`, induction,
  and instantiation as proof-producing steps;
- P6.4: a small agent-facing surface;
- P6.5: a specification surface.

That is the native Axeyum proof assistant. The interoperability track in this
document feeds it imported declarations and an optional Lean-facing UI; it does
not replace it.

### 2.3 CAS, rewrite rules, and curriculum versus mathlib

`axeyum-cas` is 13,929 lines of Rust in the current inventory. It implements a
wide set of explicit symbolic algorithms: exact polynomial and rational
normalization, differentiation and selected integration, equation solving,
Sturm isolation, Groebner bases, factorization, matrix normal forms and spectral
operations, number theory, Gosper summation, series, selected ODE/recurrence
methods, and proof/certificate objects for many results. `axeyum-egraph` can
retain explanations; the ordinary `axeyum-rewrite` canonicalizer's application
report is not itself a Lean proof.

The educational corpus is also concrete rather than aspirational:

- 23 curriculum nodes: 19 `covered`, 4 explicitly `lean-horizon`;
- 137 foundational concept rows;
- 173 non-template validated math packs;
- 1,131 expected-result rows: 399 checked, 596 replay-only, 136 Lean-horizon;
- 173 promoted solver-reuse packs;
- 249 files under `docs/learn/math/`.

Those counts measure Axeyum's finite/computable/certificate-oriented learning
assets. They are **not** percentages of mathlib coverage.

Mathlib v4.30.0 contains 8,606 `.lean` files at its tagged tree, including 1,319
under `Mathlib/Algebra`, 1,084 under `CategoryTheory`, 795 under `Analysis`, 689
under `RingTheory`, 665 under `Topology`, 351 under `LinearAlgebra`, and 336
under `Tactic`. More importantly, its content is generic and dependent: theorem
families are abstracted over typeclasses, structures, coercions, and universe
parameters. Axeyum's CAS usually computes in explicit domains and returns a
domain-specific certificate.

The useful relationship is therefore a bridge:

| Axeyum asset | Mathlib-facing opportunity | Missing bridge |
|---|---|---|
| exact arithmetic and `norm_num`-like certificates | discharge closed numerical goals | reification plus Lean proof-term reconstruction |
| polynomial normalization/factorization/Groebner | `ring`-like normalization and algebraic side conditions | generic semiring/ring theorem basis and certificate translator |
| LIA/LRA/NIA/NRA solver evidence | `linarith`/selected `nlinarith`-like goals | proposition reification, hypothesis provenance, kernel term builder |
| 56 canonical rewrite entries and e-graph explanations | `simp` candidates | explicit theorem provenance, orientation/conditions, checked explanation conversion |
| finite model replay and counterexamples | `decide`/`native_decide`-style bounded goals and refutation feedback | CIC-to-IR totality gate and replayed model-to-source mapping |
| curriculum/example packs | selected theorem targets and regression cases | imported theorem identities and no-`sorry` evidence |

The first mathlib milestone is not “implement mathlib.” It is to eliminate the
current 64 prelude axioms where possible, then import and independently check a
small, pinned theorem slice that exercises the CAS/tactic crosswalk.

## 3. What official Lean actually does

The Lean 4 reference describes a pipeline with distinct contracts:

```text
source text
  -> extensible parser
  -> macro expansion
  -> elaboration and tactic execution
  -> fully explicit core terms + information trees
  -> kernel admission
  -> optional compiler/runtime
```

The parser is extensible rather than a fixed grammar. Macros transform syntax;
elaborators resolve notation, implicit arguments, coercions, typeclasses,
overloading, metavariables, and tactics. Tactics are a specialization of term
elaboration. The language server consumes elaboration state and information
trees, so a useful standalone Lean LSP cannot be scheduled independently of the
frontend.

Lake is a Lean-aware build/package system, not just a TOML reader. It compiles
Lean modules and executables, manages facets/configuration, resolves packages,
and participates in the same toolchain environment. Likewise, `.olean` is an
implementation cache tied closely to a Lean build, not a stable interchange
format.

Primary references:

- [Elaboration and Compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
- [Macros](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Macros/)
- [Elaborators](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Elaborators/)
- [Lake reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
- [Lake source guide at Lean v4.30.0](https://github.com/leanprover/lean4/blob/v4.30.0/src/lake/README.md)

At the Lean v4.30.0 source tree, a simple file-count scale check finds 17 files
under `Lean/Parser`, 300 under `Lean/Elab`, 417 under `Lean/Meta`, 45 under
`Lean/Server`, 117 under `Lean/Compiler`, and 160 under `src/lake`. These are not
LOC or complexity estimates; they are a warning against calling each missing
subsystem a small feature.

## 4. The import seam: `lean4export`, not `.olean`

The official `lean4export` project exports one or more modules and transitive
dependencies as versioned NDJSON. Format 3.1.0 includes names, universe levels,
expressions, axioms, definitions, opaque declarations, theorems, quotient
packages, and grouped mutual inductive/constructor/recursor data.

References:

- [`lean4export` v4.30.0](https://github.com/leanprover/lean4export/tree/v4.30.0)
- [NDJSON format 3.1.0](https://github.com/leanprover/lean4export/blob/v4.30.0/format_ndjson.md)
- [Lean comparator's sandboxed export boundary](https://github.com/leanprover/comparator)

The comparator project intentionally avoids loading untrusted `.olean` files
directly and invokes `lean4export` in a sandbox. Axeyum should adopt the same
security boundary:

- official Lean may read its version-coupled `.olean` cache in an external,
  resource-limited process;
- Axeyum accepts only the documented, pinned NDJSON interchange;
- the pure-Rust default path can read a previously exported NDJSON stream with
  no Lean installation;
- malformed, unknown-version, unsafe, partial, or unsupported declarations fail
  closed;
- no `.olean` parser enters Axeyum's trusted path.

### 4.1 Prototype result

The committed
[`lean4export-v4.30-axeyum-probe.ndjson`](fixtures/lean4export-v4.30-axeyum-probe.ndjson)
was produced by official `lean4export` tag v4.30.0 (`a3e35a58...`) under Lean
4.30.0 (`d024af09...`). Its source declares one axiom, one identity theorem,
one flat two-constructor inductive, and one definition.

The research probe
[`scripts/prototype_lean4export_reader.py`](../../scripts/prototype_lean4export_reader.py)
validates metadata, dense index spaces, topological references, known record
kinds, and selected safety/shape constraints. Its current result is:

```text
LEAN4EXPORT_PROBE|format=3.1.0|lean=4.30.0|names=14|levels=2|exprs=43|decls=5|blockers=none
```

Six tests cover both real fixtures, unknown-record rejection, forward-reference
rejection, unsafe/partial-declaration rejection, and blocker classification for
projections, literals, and quotient declarations. The Python probe remains an
inventory oracle; it is not product code.

The follow-on Rust prototype now crosses the assurance boundary. The separate
[`axeyum-lean-import`](../../crates/axeyum-lean-import/src/lib.rs) crate parses
the same stream and sends every supported declaration through
`Kernel::add_declaration` or `Kernel::add_inductive`. It independently generates
the inductive recursor and compares its type and iota rules to the official
export. The measured result is:

```text
LEAN4EXPORT_IMPORT|format=3.1.0|lean=4.30.0|names=14|levels=2|exprs=43|decl_records=5|admitted=8|axioms=P
```

Eleven Rust integration tests include flat and direct-recursive positive fixtures,
theorem-body and recursor-rule tampering, determinism, format drift, topology,
safety, synthetic and official projection/quotient declines, and resource
controls.
See the full
[`Rust import result`](lean4export-rust-import-prototype-2026-07-21.md).
The second official fixture independently admits direct-recursive `MiniNat` and
parametric-recursive `MiniList` as 11 declarations with no axioms. It exposed
alpha-equivalent recursor universe binders (`u_1` versus `u.1`), now compared
after explicit level substitution. These results grant independent admission
credit only to the exact flat and direct-recursive fixtures. They do not grant
`Init`, `Std`, mathlib, literal, projection, quotient, recursive-indexed,
mutual, nested, or reflexive-inductive credit.

The follow-on
[`official blocker census`](lean4export-official-blocker-census-2026-07-21.md)
freezes four dependency closures. Projection is the sole blocker in the
four-declaration structure root and the first importer decline for both the Nat
and String literal roots. The String root spans 290 declaration records and
also reaches Nat literals and recursive-indexed inductives; quotient is a
separate five-record closure. This selects projection as L2 slice 2 with real
dependency evidence, not estimated ecosystem frequency.

## 5. Architecture

### 5.1 Two deployment profiles

**Independent profile (default).** Pure Rust, no official Lean runtime, no C/C++
dependency, WASM-compatible where the existing kernel is. It reads Axeyum's
native proof artifacts and the initial pinned `lean4export` NDJSON profile. It
owns all admission decisions and reports unsupported constructs structurally.

**Official-integration profile (optional).** A version-pinned Lean process or
plugin performs source elaboration, module export, project discovery, editor
integration, and official cross-checking. It is an oracle/workflow adapter, not
the source of independent checking credit. Its outputs are untrusted inputs to
the Rust kernel unless separately accepted by official Lean for a stated gate.

### 5.2 Dependency order

```text
L0 capability/version contract
  -> L1 NDJSON syntax reader
       -> L2 kernel admission breadth
            -> L3 pinned Prelude/Init/Std/mathlib slices
                 -> L4 Goal/Hole/unifier (Track 6 P6.2)
                      -> L5 certificate tactics (Track 6 P6.3)
                           -> L6 selected Lean source surface
                                -> L7 Lake/package adapter
                                -> L8 editor/LSP integration

L2 + existing reconstruction -> optional official-Lean plugin/sidecar
L6/L7 measured demand        -> L9 restricted compiler work, if any
L3-L5                        -> L10 widening mathlib release matrix
```

L8 cannot precede source maps and information-tree equivalents. L9 is not a
proof-kernel prerequisite. L3 must not count an imported record until L2 checks
it.

## 6. Phased roadmap

Sizes use the repository convention: S <=2 days, M about one week, L 2--4
weeks, XL multi-month. They are engineering estimates, not commitments.

### L0 — Freeze the compatibility and assurance contract (S)

Goal: make every later result comparable and prevent the word “parity” from
collapsing independent axes.

Tasks:

1. Accept or revise ADR-0345.
2. Pin Lean and `lean4export` versions, commit export metadata, source hash,
   module list, command, and resource limits.
3. Publish a capability object with separate `parse`, `admit`, `official_check`,
   `source_elaborate`, and `workflow` fields.
4. Correct stale kernel documentation and add a generated kernel feature
   matrix tied to executable tests.
5. Freeze decline codes and the expected-axiom allowlist format.

Exit: the same artifact cannot be called “supported” by one path because it was
merely parsed and by another because it was independently type-checked.

### L1 — Product `lean4export` 3.1 reader (M)

Goal: deterministic Rust ingestion of the official interchange while keeping
parsing distinct from the declarations that subsequently pass kernel admission.

Current result: the separate Rust importer, exact version/field/topology checks,
explicit line/record limits, supported expression translation, and safe flat
and direct-recursive declaration admission are landed. The Python and Rust
readers agree on the flat fixture's 14/2/43/5 and recursive fixture's
30/4/130/5 inventories. L1 remains WIP until the mutation/fuzz, axiom
digest, large-stream publication, and broader wire-profile gates below land.

Tasks:

1. Port the research probe to a small module at the kernel boundary.
2. Decode names, universe levels, all expression variants, and all declaration
   record variants into a separate wire model.
3. Validate metadata, integer bounds, dense IDs, topological references,
   declaration uniqueness, UTF-8/JSON limits, maximum depth/counts, and no
   trailing/unknown fields unless the format explicitly permits them.
4. Reject unsafe/partial declarations by default. Count axioms by stable name
   and type digest.
5. Preserve metadata only as non-semantic annotations; prove erasure does not
   change admission.
6. Add fuzzing, truncation, duplicate-ID, forward-reference, enormous-integer,
   cyclic-dependency, and unknown-version mutations.

Exit: deterministic inventories on committed exports; every malformed mutation
rejects without panic; zero declaration receives `checked=true` from parsing.

### L2 — Kernel admission breadth driven by real declines (L/XL, sliced)

Goal: translate wire records into the existing environment and admit them with
the independent type checker.

Current result: slice 1 is landed on the official flat and direct-recursive
fixtures. The former's five export records become eight checked environment
declarations; the latter's five records become 11 checked declarations for
`MiniNat`/`MiniList` with no axioms. Generated recursor types and rules match the
exports after alpha-renaming universe binders, and a tampered theorem or recursor
rule rejects. These are two selected fixtures, not general kernel admission.

Ordered slices:

1. current expressions/declarations plus flat, parametric-recursive, and direct-
   recursive non-indexed inductives;
2. `Expr.proj` checking and reduction;
3. arbitrary-precision natural literals **before** literal typing, then string
   literals and their reduction rules;
4. quotient package declarations and reduction/equality behavior;
5. recursive indexed inductives;
6. mutual, nested, and reflexive inductive groups;
7. exact universe-positivity, recursor, safety, and opaque/definition behavior
   observed in imports;
8. resource-bounded adversarial checking and differential fuzzing.

Every slice needs positive official exports, malformed controls, an
independent-kernel acceptance result, and a same-or-opposite result from
official Lean. The [Lean Kernel Arena](https://arena.lean-lang.org/checker/still-nanoda/)
is an adversarial corpus source, not an authority that substitutes for local
tests.

Exit: a generated matrix lists each format construct as parsed/admitted/declined
with a stable reason; selected imports pass both kernels; mutations that would
make `False` inhabitable reject.

### L3 — Prelude, Init, Std, and selected mathlib imports (L, then ongoing)

Goal: measure real library compatibility and reduce Axeyum-created axioms.

Order:

1. export and inventory the exact Axeyum reconstruction prelude;
2. classify all 64 current prelude axioms as expected external assumptions,
   derivable theorems, kernel primitives, or defects;
3. discharge derivable axioms and fail on new unregistered axioms;
4. import bounded slices of `Init` and `Std` chosen by construct coverage;
5. import a pinned mathlib smoke slice: basic algebraic structures plus the
   theorem basis needed by one CAS proof translator;
6. grow a release matrix across at most current and previous supported Lean
   releases after one release is sound.

The importer records both syntactic inventory and independent admission. A
mathlib declaration whose dependency graph contains an unsupported declaration
does not count as accepted. Results report declarations and dependency-closed
roots, never only file counts.

Exit: a no-hidden-axiom selected library slice checks independently and against
official Lean, with exact accepted/declined dependency closures.

### L4 — Goal, hole, metavariable, and unification layer (Track 6 P6.2, L)

Goal: make interactive proof state data rather than formatted text.

This is existing Track 6 work, not a second implementation. It must include:

- typed goals and local contexts;
- holes/metavariables with explicit coupling;
- delayed assignment across binder depth;
- occurs checks and scope/depth invariants;
- pattern unification first, general higher-order unification only when demand
  and a sound decline boundary justify it;
- deterministic snapshots and replay.

Exit: `intro` and `apply` can generate/check nested goals without capture,
sibling-goal corruption, or untracked assignment.

### L5 — Certificate-first tactic sweep (L/XL, incremental)

Goal: expose existing Axeyum engines as untrusted proof search whose output the
small checker validates.

Recommended order:

1. `exact`, `intro`, `apply`, assumption;
2. `decide` through existing solver reconstruction;
3. counterexample/refute only after the CIC-to-IR `sat` totality gate;
4. `norm_num`-like exact arithmetic using CAS certificates;
5. `ring`-like polynomial normalization;
6. selected `linarith`/`nlinarith`-like reconstruction;
7. `simp` from theorem-backed rewrite entries and e-graph explanations;
8. induction/instantiation.

This is a capability crosswalk, not a promise of source-compatible tactic
syntax. Each tactic reports proposal time, certificate size, checker time,
trusted assumptions, and official-Lean acceptance where exportable.

Exit: each tactic has positive/negative/tampered certificates and can emit a
kernel term checked by both the independent kernel and the pinned official
kernel on its admitted profile.

### L6 — A selected Lean source profile (XL; bridge-first)

Goal: permit human-authored Lean-like statements without pretending to
implement Lean's open-ended macro/elaboration ecosystem.

Stage 1 uses official Lean as an optional frontend: elaborate ordinary Lean,
export declarations, and independently check the supported core. This gives
immediate language/workflow value without trusting official elaboration for
the final independent admission.

Stage 2, only after importer measurements, may implement a versioned native
subset:

- fixed lexical grammar and source locations;
- declarations, binders, universes, applications, `fun`/`forall`/`let`;
- a fixed notation table rather than user-defined Pratt categories;
- explicit types first, then bounded implicit insertion/coercions;
- pattern unification using L4;
- no arbitrary macros, custom elaborators, or metaprogram execution.

Any source outside the profile declines with a source span and suggests the
official frontend. Differential tests compare parsed/elaborated core terms,
not pretty-printed output.

Exit: the native profile is documented by grammar and capability version;
accepted source produces core terms definitionally equal to the pinned official
Lean result on a mutation-tested corpus.

### L7 — Lake and package interoperability (M/L adapter; clone deferred)

Goal: work in real Lean projects without rebuilding the package manager.

First implementation:

- discover the pinned toolchain and Lake project through official commands;
- ask Lake/Lean for the module closure;
- invoke the pinned exporter in a sandbox;
- content-address NDJSON exports by toolchain/module/source/options identity;
- expose `axeyum check-lean-project` and machine-readable declines;
- optionally package an Axeyum Lake facet or plugin command.

Do not parse arbitrary `lakefile.lean` as configuration or claim compatible
dependency solving. A native package manager is only reconsidered if the
official adapter prevents an independently deployable use case that users
actually need.

Exit: two cloned pinned projects, including one selected mathlib project, export
reproducibly and rerun incrementally without stale-cache acceptance.

### L8 — Editor and language-server integration (M adapter; XL native)

Goal: deliver useful proof feedback in editors after source identity and goal
state exist.

Order:

1. official Lean plugin/custom RPC exposing Axeyum goals, evidence, declines,
   and counterexamples;
2. VS Code/editor client consuming that RPC;
3. narrow Axeyum goal server for the native L6 subset;
4. only then evaluate a broader LSP implementation.

The server must version documents, cancel stale work, preserve source-to-core
maps, and never publish diagnostics from an older snapshot. Full Lean editor
compatibility requires information-tree semantics and is not implied by JSON-RPC
method compatibility.

Exit: stale/cancelled document mutations cannot surface as current proof
results; every diagnostic links to a stable goal/evidence ID.

### L9 — Compiler/runtime (deferred, demand-gated)

Goal: avoid making compilation a prerequisite for checking proofs.

Use the official Lean compiler for Lean metaprograms and generated executables
in the optional profile. The independent kernel remains an evaluator/checker,
not an optimizing compiler. Consider a restricted compiler only for a measured
need such as WASM execution of closed certified functions or proof-producing
partial evaluation.

Exit before admission: a concrete use case cannot be served by kernel
evaluation, Axeyum IR lowering, or the optional official compiler; semantics and
replay are specified; compiler output is outside the proof TCB.

### L10 — Mathlib breadth and release maintenance (ongoing, after L3/L5)

Goal: turn selected interoperability into a maintained compatibility profile.

Track:

- total export records and dependency-closed roots;
- parsed versus independently admitted declarations;
- decline counts by construct, not just first error;
- expected axioms and newly introduced axioms;
- tactic proof acceptance through both kernels;
- per-release regressions and format changes;
- resource distribution and worst cases.

Prioritize theorem slices that retire Axeyum axioms or enable CAS/solver tactics.
Do not optimize for a vanity declaration count by importing leaf constants with
shallow dependencies.

Exit is per release/profile, never “mathlib complete” without a full
dependency-closed import and independent check.

## 7. Gates and scoreboards

### 7.1 Assurance states

Every imported root receives exactly one highest state:

1. `inventory-only` — record decoded;
2. `translated` — wire term mapped to kernel representation;
3. `independently-admitted` — Axeyum kernel checks declaration and closure;
4. `dual-admitted` — independent and pinned official kernels accept;
5. `workflow-reproduced` — source/project rebuild reproduces the admitted
   declaration identity.

States do not collapse. Official-only acceptance is recorded separately and
never promoted to independent admission.

### 7.2 Mandatory negative gates

- unknown format/record/field policy;
- truncation, malformed JSON, duplicate/non-dense IDs, forward references;
- unsafe and partial declarations;
- integer/resource overflow and depth bombs;
- projection, literal, quotient, and inductive mutations;
- undeclared axioms and dependency-closure omissions;
- proof-term mutations, universe changes, constructor/recursor changes;
- source/elaboration differences hidden by pretty-printing;
- stale Lake cache and stale LSP document results;
- the negative objective “independent kernel accepts `False`.”

### 7.3 Performance reporting

Importer/checker performance reports files, bytes, records, dependency roots,
peak RSS, wall time, checker time, and cache state separately. It uses hard
limits and checkpointed output for large imports. A timeout is `unknown` or a
typed decline, never evidence that a theorem is invalid.

## 8. Risks and explicit non-claims

| Risk | Control |
|---|---|
| importer bugs expand the TCB | separate wire validation from kernel admission; fuzz and mutate both seams |
| official exporter becomes an implicit trust root | sandbox it; hash/version outputs; independently check core terms |
| direct `.olean` attack/version coupling | explicit non-goal; official tool alone reads `.olean` |
| library counts become fake parity | dependency-closed admission denominator and assurance states |
| axioms make imported proofs vacuous | stable axiom allowlist, type digest, discharge queue, fail on additions |
| frontend effort consumes the solver/proof program | bridge-first source profile; native frontend after measured imports |
| tactic wrappers trust solver answers | certificate-first steps and checker-only trusted dependency direction |
| CAS called “mathlib” | crosswalk by theorem/certificate families, no coverage percentage |
| LSP ships detached from elaboration state | plugin first; native service after L4/L6 source maps |
| compiler enters proof TCB | keep compilation optional and outputs replay/checkable |
| upstream format churn | pin versions; one reader profile at a time; fail unknown versions |

Non-claims until their gates are met:

- no full Lean parser, macro, elaborator, tactic-language, compiler, Lake, LSP,
  or mathlib parity;
- no direct `.olean` compatibility;
- no mathlib coverage claim from Axeyum curriculum or CAS counts;
- no general Lean-kernel parity from 71 generated modules;
- no independent-checking claim from official Lean acceptance alone;
- no theorem-admission claim from NDJSON parsing alone.

## 9. Immediate next ten actions

1. Review ADR-0345 and the landed separate-crate/TCB boundary.
2. Keep the eight Python and eleven Rust fixture/mutation/census tests in normal
   checks.
3. Preserve the landed projection/Nat/quotient streams and the source/command/
   hash-bound String closure; generate the remaining recursive-indexed, mutual,
   nested, and reflexive fixtures.
4. Preserve byte-identical regeneration of both committed official fixtures and
   carry the direct-recursive positive control beside every recursive-indexed
   negative so the boundary is attributed to indices, not recursion alone.
5. Generate the parsed/translated/admitted/dual-admitted feature matrix from the
   current hand-checked six-profile seed.
6. Add truncation-at-every-record, duplicate-ID, deep-JSON, unknown-field, and
   completed-environment publication mutations.
7. Inventory and type-digest the 64 prelude axioms; choose the first five to
   discharge from existing arithmetic/CAS evidence.
8. Export minimal pinned `Init`/`Std` roots and rank kernel work by aggregate
   dependency-closed admissions gained per slice.
9. Select one mathlib `norm_num` or `ring` theorem basis and implement one
   end-to-end CAS-certificate-to-kernel-term proof.
10. Resume Track 6 P6.0 fuzzing and P6.2 goal/hole work; do not begin a native
    Lean parser, Lake clone, standalone LSP, or compiler before L1-L3 provide
    measured demand.

## 10. Strategic answer

Axeyum is not “far from Lean” in the narrow role it deliberately built: it has
an independent kernel/reconstruction slice and a real cross-check lane. It is
far from Lean as a complete user-facing programming and theorem-proving
environment. The most valuable next step is not to erase that distinction with
a huge rewrite. It is to connect the independent checker to the official
ecosystem through a narrow, auditable import boundary, then let real import and
tactic evidence decide which pieces deserve independent implementations.

That trajectory preserves the project's differentiator: official Lean can be
the convenient frontend and oracle, while Axeyum remains a second,
independently implemented checker for the admitted core.
