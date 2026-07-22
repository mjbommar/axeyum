# Lean-system compatibility: evidence audit and staged roadmap

Status: accepted strategy; implementation active

Date: 2026-07-21

Decision: [ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md)

Active execution breakdown:
[`lean-system-implementation-plan-2026-07-21.md`](lean-system-implementation-plan-2026-07-21.md)

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
   optional sidecar/plugin profile before depending on native replacements;
6. implement native parser/macro, elaborator, tactic, module/package, editor,
   and runtime compatibility as separately gated later profiles;
7. grow from selected mathlib import/cross-check slices to a complete pinned
   native build, without confusing theorem-library breadth with kernel breadth.

This closes useful portions of the gap without putting the official Lean
runtime in the default TCB, sacrificing WASM, or making “we parsed a file” mean
"we checked its declarations." A full independent replacement for Lean's
parser, macro expander, elaborator, compiler, Lake, language server, and mathlib
is a multi-person-year program. It is now an explicit long-horizon
implementation program, not the next milestone and not a prerequisite for
useful checker/import/tactic profiles.

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

The first mathlib milestone is not “implement mathlib.” It is to classify and
then eliminate where possible the current **65** reconstruction-prelude
assumptions (real 30, integer 34, string 1), then import and independently check
a small, pinned theorem slice that exercises the CAS/tactic crosswalk. The
[runtime-derived ledger](lean-axiom-ledger-v1.json) binds every admitted name to
its canonical type; it does not yet prove any row true.

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
LEAN4EXPORT_IMPORT|format=3.1.0|lean=4.30.0|names=14|levels=2|exprs=43|decl_records=5|admitted=8|axioms=P|identity=axeyum-lean-declaration-identity-v1|axiom_ids=1|declaration_ids=8
```

Twenty-eight importer integration tests across three binaries include flat,
direct-recursive, projection,
and Nat-literal positive fixtures; theorem-body, recursor-rule, projection, and
Nat-bootstrap tampering; determinism, format drift, topology, safety, quotient
declines, arbitrary-precision wire values, resource controls, owned completed
publication, five late-failure classes, the 226-case generated TL1.4 mutation
population, and five TL1.7 identity/reordering/mutation gates.
See the full
[`Rust import result`](lean4export-rust-import-prototype-2026-07-21.md).
The second official fixture independently admits direct-recursive `MiniNat` and
parametric-recursive `MiniList` as 11 declarations with no axioms. It exposed
alpha-equivalent recursor universe binders (`u_1` versus `u.1`), now compared
after explicit level substitution. These results grant independent admission
credit to the exact flat, direct-recursive, projection, and Nat-literal
fixtures. They do not grant `Init`, `Std`, mathlib, String-literal, quotient,
recursive-indexed, mutual, nested, or reflexive-inductive credit.

The follow-on
[`official blocker census`](lean4export-official-blocker-census-2026-07-21.md)
freezes four dependency closures. Projection was the sole blocker in the
four-declaration structure root and is now cleared by TL2.2-TL2.4. TL2.6-TL2.7
then clear arbitrary-precision storage and checked constructor/literal semantics:
the committed Nat root translates 90 expressions, admits ten declarations with
zero axioms, and computes to `37`. The unretained String root spans 290
declaration records and also reaches Nat literals and recursive-indexed
inductives, but its current first blocker remains unmeasured; quotient is a
separate five-record closure. These exact closures establish implementation
order, not ecosystem frequency.

## 5. Architecture

### 5.1 Three deployment profiles

**Independent profile (default).** Pure Rust, no official Lean runtime, no C/C++
dependency, WASM-compatible where the existing kernel is. It reads Axeyum's
native proof artifacts and the initial pinned `lean4export` NDJSON profile. It
owns all admission decisions and reports unsupported constructs structurally.

**Native-system profile (staged).** Pure-Rust parser/macros, elaboration,
goals/tactics, modules/packages, editor services, and runtime components are
enabled only as their K2-K6 gates pass. These components may construct terms and
artifacts but do not gain admission authority or create a dependency back-edge
into the kernel.

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
                           -> L6 native parser/macro surface
                                -> L4B native elaborator
                                     -> L7 modules/Lake/packages/`.olean`
                                     -> L8 native editor/LSP

L2 + existing reconstruction -> optional official-Lean plugin/sidecar
L4B + L7                     -> L9 compiler/runtime/metaprograms
L3-L9                        -> L10 full pinned mathlib build/release matrix
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

1. **Done:** accept ADR-0345 together with ADR-0167's single goal/tactic owner.
2. Pin Lean and `lean4export` versions, commit export metadata, source hash,
   module list, command, and resource limits.
3. **Done:** publish a capability object with eight separate parser,
   translation, independent/official admission, source, proof, workflow, and
   runtime fields.
4. Correct stale kernel documentation and add a generated kernel feature
   matrix tied to executable tests.
5. **Partial:** nine current importer decline codes are source-bound; the
   expected-axiom allowlist/ledger is TL0.4.

Current result: the
[`lean-compatibility-v1.json`](lean-compatibility-v1.json) contract and generated
[matrix](generated/lean-compatibility.md) hold 12 exact rows. Six mutation tests
reject illegal assurance combinations, absent evidence, and unregistered or
misapplied declines. Three rows satisfy their exact K0/K1 target; no row claims
a completed K2-K6 native profile.

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
2. classify all 65 current prelude assumptions as expected external
   assumptions, derivable theorems, primitive interfaces, or defects;
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

### L6 — Native Lean parser, syntax extensions, and macros (XL; adapter-first)

Goal: accept the pinned Lean source language with source-mapped syntax,
extensible parser categories, quotations, notation, and hygienic macros.

Stage 1 uses official Lean as an optional frontend: elaborate ordinary Lean,
export declarations, and independently check the supported core. This gives
immediate language/workflow value without trusting official elaboration for
the final independent admission.

Stage 2 implements the native frontend in measured layers: source identities
and lexer; syntax objects and Pratt parser tables; builtin command/term/tactic
categories; user syntax/notation compilation; quotations and hygienic macro
expansion; recovery and canonical printing; then bootstrap of selected frontend
modules. Elaboration is L4B, not hidden inside parsing, and arbitrary
metaprograms wait for the bounded L9 runtime.

Unsupported constructs decline with source spans and stable codes throughout
the climb. Differential tests compare token/syntax identity, expanded syntax,
and eventually elaborated core digests—not pretty-printed similarity. Exact
task order and gates are TL6.1-TL6.13 in the
[implementation plan](lean-system-implementation-plan-2026-07-21.md).

Exit: the supported pinned source profile parses and macro-expands like official
Lean, preserves stable incremental identities, and bootstraps the declared
frontend modules.

### L7 — Modules, caches, packages, Lake, and `.olean` (M adapter; XL native)

Goal: work in real Lean projects immediately through the official adapter and
eventually reproduce their module/package build graph natively.

First implementation:

- discover the pinned toolchain and Lake project through official commands;
- ask Lake/Lean for the module closure;
- invoke the pinned exporter in a sandbox;
- content-address NDJSON exports by toolchain/module/source/options identity;
- expose `axeyum check-lean-project` and machine-readable declines;
- optionally package an Axeyum Lake facet or plugin command.

The native path then implements module deltas and content-addressed caches,
toolchain/manifest/TOML parsing, deterministic Git/path resolution, build
targets/facets/traces, and `lakefile.lean` through L4B/L9. A version-specific
`.olean` reader is deliberately late and remains in the untrusted cache/adapter
layer; it must translate to the same checked environment and produce declaration
digests equal to the `lean4export` path.

Adapter exit: two pinned projects, including one selected mathlib project,
export reproducibly and rerun incrementally without stale-cache acceptance.
Native exit: clean, incremental, and offline builds reproduce module identities,
dependency resolution, and build graphs with no stale artifact acceptance.

### L8 — Editor and language-server integration (M adapter; XL native)

Goal: deliver useful proof feedback in editors after source identity and goal
state exist.

Order:

1. official Lean plugin/custom RPC exposing Axeyum goals, evidence, declines,
   and counterexamples;
2. VS Code/editor client consuming that RPC;
3. native snapshot/cancellation and incremental parser/elaborator services;
4. navigation, completion, semantic data, code actions, widgets, and proof RPC.

The server must version documents, cancel stale work, preserve source-to-core
maps, and never publish diagnostics from an older snapshot. Full Lean editor
compatibility requires information-tree semantics and is not implied by JSON-RPC
method compatibility.

Exit: a selected Lean project can be edited through the native server with
snapshot-correct goals, diagnostics, navigation, completion, and proof actions;
stale/cancelled document mutations cannot surface as current results.

### L9 — Evaluator, compiler, runtime, and metaprograms (XL; checker-independent)

Goal: execute Lean definitions, metaprograms, build scripts, tactics, and
programs natively while keeping compilation outside proof admission.

The optional profile continues to use official Lean first. The native sequence
then freezes erasure/runtime semantics, implements a bounded interpreter,
checked IR/LCNF-like forms, closure/specialization/RC passes, portable C/native
and WASM outputs, controlled FFI, and bounded execution of macros/tactics/Lake
DSL. Each optimization is compared against the interpreter and pinned official
Lean. Compiler output never receives theorem credit without kernel admission or
observable replay.

Exit: the declared runtime profile builds and executes without official Lean,
with zero unexplained differential observations and an explicit runtime/FFI
trust boundary.

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
| direct `.olean` attack/version coupling | late version-specific reader in the untrusted cache/adapter layer; export-digest equivalence; malformed-input fuzzing |
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
- no direct `.olean` compatibility until TL7.9's versioned reader and
  export-digest equivalence gate pass;
- no mathlib coverage claim from Axeyum curriculum or CAS counts;
- no general Lean-kernel parity from 71 generated modules;
- no independent-checking claim from official Lean acceptance alone;
- no theorem-admission claim from NDJSON parsing alone.

## 9. Immediate next twelve actions

1. Review ADR-0345 and the landed separate-crate/TCB boundary.
2. Keep the compatibility/census/ledger tests, 28 importer cases, and the
   bounded native/pinned-Lean kernel gates in normal checks.
3. **TL2.2-TL2.7 DONE:** preserve first-class projection representation,
   checked dependent inference, constructor reduction, exact official-root
   import/computation, and separately gated structure eta with pinned-Lean
   positive/rejecting controls, plus canonical arbitrary-precision Nat storage
   and checked Nat literal typing/conversion. TL1.3 now publishes only an owned
   completed environment after full-stream success. TL1.4 now freezes 226
   mutation cases and labels upstream no-footer prefixes unsealed. TL1.7 now
   publishes canonical declaration/dependency identities; do not generalize
   exact K1 roots or K0 rules to broader native or ecosystem compatibility.
4. Preserve the landed projection/Nat/quotient streams and the source/command/
   hash-bound String closure. The completed
   [official construct-matrix plan](lean-official-construct-matrix-plan-2026-07-22.md)
   covers recursive-indexed, reflexive/higher-order, mutual, nested, and well-
   founded source families. Its [M0/Stage A checkpoint](lean-official-construct-matrix-stage-a-2026-07-22.md)
   reproduced the historical controls and froze seven source cases before
   product observation; its [Stage B checkpoint](lean-official-construct-matrix-stage-b-2026-07-22.md)
   freezes five byte-identical official streams and complete independent wire-
   group inventories before Rust measurement.
5. **M3 DONE:** the [current-product result](lean-official-construct-matrix-product-2026-07-22.md)
   carries ten exact direct-recursive controls beside two stable outcomes for
   every new row. It records kernel/policy declines, the nested format
   misclassification, and completion-only failure without changing semantics.
6. **M4/M5 DONE:** the [assurance result](lean-official-construct-matrix-m4-2026-07-22.md)
   generates the parsed/translated/admitted/computation-separated matrix from
   tests and exact fixtures, and the [final result](lean-official-construct-matrix-final-2026-07-22.md)
   closes bounded gates, ADR-0351, and handoff. The selected-family seed advances
   TL2.16 to PARTIAL but does not complete its full population.
7. **DONE — TL2.11:** [accepted ADR-0352 and its bounded plan](lean-strict-positivity-final-2026-07-22.md)
   close the trusted Lean 4.30 single-family positivity preflight.
   M0 froze negative sources and M1 landed the trusted Lean 4.30 single-family
   preflight before environment insertion. M2 now closes the twelve-row public
   matrix and two byte-identical runs of a frozen 840-case grammar. M3 now adds
   eight pinned-Lean observations, mandatory CI, synthetic importer
   propagation, and the immutable construct-matrix regression. Final bounded
   gates pass and no recursive admission widened. **TL2.12 is now DONE under
   accepted ADR-0353:** direct, indexed, higher-order, and
   combined fields use one `Pi telescope, motive indices (field args)` IH/rule
   construction. [M0 is complete](lean-recursive-induction-hypotheses-m0-2026-07-22.md):
   one explicit-recursor source compiles twice, two root-specific official
   streams repeat byte-identically, and ten fail-closed tests bind their exact
   inventories while forbidding Axeyum product credit. The
   [M1 result](lean-recursive-induction-hypotheses-m1-2026-07-22.md) routes
   direct recursion through the shared recursive-field classifier/reopener and
   stable metadata. The
   [M2 result](lean-recursive-induction-hypotheses-m2-2026-07-22.md) now admits
   all ten positive native rows, retains four typed transactional negatives,
   rejects ten native mutation classes, and repeats the 768-case recursive
   grammar and retained 840-case positivity control. The
   [M3 result](lean-recursive-induction-hypotheses-m3-2026-07-22.md) now
   completes both construct targets twice with exact recursor comparison and
   closes metadata/publication mutations. The pre-elaborated well-founded
   stream also completes through `Acc.rec`; mutual/nested retain typed
   boundaries. The
   [M4 result](lean-recursive-induction-hypotheses-m4-2026-07-22.md) now
   confirms pinned Lean and Axeyum computations twice at the exact Vector/Acc
   normal forms and regenerates a machine-validated matrix with four admitted,
   two computation-checked, and two declined rows. The
   [M5 result](lean-recursive-induction-hypotheses-final-2026-07-22.md) closes
   every registered gate, accepts ADR-0353, and hands off to TL2.13.
   The
   [execution plan](lean-recursive-induction-hypotheses-tl2.12-plan-2026-07-22.md)
   requires both frozen official streams, exact generated-recursor comparison,
   selected computation, a >=512-case grammar, and the existing 840-case
   positivity gate. The nested diagnostic classification is a
   separate bounded TL1.8 hygiene follow-up, not semantic nested support.
8. **TL1.3-TL1.4, TL1.7, and TL2.14 DONE; TL1.5 DEPENDENCY-READY:** preserve owned
   completion-only publication, the 226-case mutation corpus, and canonical
   axiom/declaration/dependency identity when property fuzzing begins. The
   completed nested-inductive kernel path retains every TL2.11-TL2.13 guard.
   **TL2.13 is complete under accepted
   ADR-0354:** one
   ordered atomic group gate owns shared parameters/universes, group-wide
   positivity, per-family indices, all motives/minors, target-family recursive
   calls, mutual-`Prop` elimination, and all-or-nothing publication. The
   [P0--M5 plan](lean-mutual-inductive-groups-tl2.13-plan-2026-07-22.md)
   requires exact official non-indexed/indexed computation, a >=640-case group
   grammar, singleton identity preservation, and the retained 768/840 controls.
   The [M0 source/wire freeze](lean-mutual-inductive-groups-m0-2026-07-22.md)
   is complete: two explicit cross-family computations compile/export twice,
   the machine contract grants no product credit, and it distinguishes source
   family order from dependency-ordered wire recursor arrays. The
   [M1 result](lean-mutual-inductive-groups-m1-2026-07-22.md) adds the public
   ordered family/group path, definitionally checked common parameters,
   per-family index opening, equivalent result-universe preflight, scalable
   insertion-log rollback, exact singleton delegation, and a typed
   multi-family policy decline. The
   [M2 result](lean-mutual-inductive-groups-m2-2026-07-22.md) replaces that
   decline with native complete-group positivity, globally ordered motives and
   minors, target-family IHs/recursor calls, per-family recursors, mutual-
   `Prop` restriction, and atomic rollback. All 18 public rows plus focused
   mutation/late-failure tests pass. The
   [M3 result](lean-mutual-inductive-groups-m3-2026-07-22.md) now repeats 720
   unique public-path cases byte-identically: 432 positive contracts, 288 typed
   rollbacks, direct motive/minor-order and target-rule oracles, and generated
   group-order/target-family mutation teeth. The 768/840 controls remain exact.
   The [M4 result](lean-mutual-inductive-groups-m4-2026-07-22.md) now imports the
   construct and both computation streams twice, compares dependency-ordered
   recursors by checked name, normalizes both selected cross-family applications
   to the registered result, and closes 22 rejecting importer/publication
   mutation classes. The
   [M5 final result](lean-mutual-inductive-groups-final-2026-07-22.md) preserves
   the historical assurance record, records five admitted rows and three
   computation-checked rows with one current decline, removes the obsolete
   live mutual decline, and closes every bounded gate. The
   [post-TL2.13 audit](lean-post-tl2.13-dependency-audit-2026-07-22.md) corrects
   the next boundary: pinned Lean performs nested-inductive expansion inside
   kernel admission, while well-founded source recursion remains TL4.10
   elaborator work. [Accepted ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)
   and the [TL2.14 plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md)
   preregister the exact expansion/restoration path. The
   [M0 result](lean-nested-inductive-elimination-m0-2026-07-22.md) now freezes
   three explicit main/auxiliary recursor computations and one exact negative
   diagnostic, with 114,596 bytes / 2,022 records reproduced byte-identically
   twice and no Axeyum observation. The already-completing 35-declaration
   well-founded core stream remains a control, not new frontend credit. M1
   first establishes typed non-admission. M2 lands structural discovery,
   complete-container copying, fixed-point expansion, atomic checking,
   restoration, and `.rec_N` publication. M3 repeats 640 unique profiles twice
   and closes the restoration mutation surface. M4 imports the construct and
   all three computation streams twice with exact declaration comparison. M5
   checks the registered 3/3/5-successor normal forms twice, appends the
   history-preserving assurance overlay at 7 rows / 6 admitted / 4 computation-
   checked / 0 current declines, and removes only the obsolete live nested
   decline. The
   [M6 final result](lean-nested-inductive-elimination-final-2026-07-22.md)
   closes exits 1--11 and every non-publication component of exit 12; containing-
   commit push/ref equality finalizes accepted ADR-0355 and TL2.14 DONE. Native
   nested/well-founded source elaboration remains
   TL4.9/TL4.10 work; no broad `Init`/`Std`/mathlib or ecosystem credit follows.
9. **DONE (inventory/digest):** retain the runtime-derived, type-digested
   65-row prelude ledger. TL3.2 next classifies the rows, then chooses the first
   five derivable assumptions to discharge from existing arithmetic/CAS evidence.
10. Export minimal pinned `Init`/`Std` roots and rank kernel work by aggregate
   dependency-closed admissions gained per slice.
11. Select one mathlib `norm_num` or `ring` theorem basis and implement one
   end-to-end CAS-certificate-to-kernel-term proof.
12. Resume Track 6 P6.0 fuzzing and P6.2 goal/hole work; after TL0 contracts,
    start TL6.1-TL6.4 as an independent source/syntax lane while L1-L3 drive the
    checker/import critical path. Lake, LSP, compiler, and `.olean` remain
    dependency-gated by their explicit TL tasks rather than globally forbidden.

## 10. Strategic answer

Axeyum is not “far from Lean” in the narrow role it deliberately built: it has
an independent kernel/reconstruction slice and a real cross-check lane. It is
far from Lean as a complete user-facing programming and theorem-proving
environment. The most valuable next step is to preserve that distinction while
executing the complete program in dependency order: connect the checker through
a narrow import boundary, harden/admit the core, build one native goal engine,
and then advance source, workflow, runtime, and mathlib profiles behind their
own evidence gates.

That trajectory preserves the project's differentiator at every milestone:
official Lean remains a convenient frontend and oracle until each native layer
is ready, while Axeyum remains an independently implemented checker and grows
into a complete compatible system without expanding the kernel TCB.
