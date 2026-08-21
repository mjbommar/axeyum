# ADR-0511: The shared development is emitted once as its own Lean module, and the split artefact is weaker than the single file

Status: accepted
Index-summary: A refutation's Lean module may be split into a shared development compiled once to an `.olean` and a per-query module that `import`s it, taking the per-query artefact from ~1.3 MB to a few kilobytes; the single-file rendering stays the default because the split is a **strictly weaker** artefact for a third party (it needs `--root` and `LEAN_PATH`), and the split is only claimed where a real-Lean suite runs the published recipe with a no-`LEAN_PATH` negative control
Index-status: accepted

Date: 2026-08-18

Related: [ADR-0512](adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md),
[ADR-0514](adr-0514-the-pinned-lean-toolchain-is-the-one-that-runs.md),
[ADR-0458](adr-0458-lean-modules-declare-whether-they-contain-reasoning.md).

## Context

The shipped front door reconstructs over the **constructed** reals and a
refutation rests on zero carrier axioms — the headline result. It costs module
size. Measured 2026-08-18 through `examples/front_door_carrier.rs`:

| fixture | over `Real` | over `CReal` |
| --- | --- | --- |
| strict-bound `x<0, 0<=x` | 8,135 B, 12 carrier axioms | 1,304,276 B, **0** |

A previous lane took the `CReal` figure from 2.6 MB to 1.3 MB with scope-aware
`let` sharing, and established the ceiling for anything the writer can do alone:
the mass is the prelude's proof **bodies** (`theorem` 213 blocks / 2,510,020 B),
the renderer already emits only reachable declarations (445 in the context, 280
in the module), and **the final theorem term is 4,193 bytes — 0.16%**. The
scope-correct sharing ceiling is 7.7x of which ~2x is realisable, because a share
reference costs more bytes than the nodes it replaces.

So 99.84% of a query module is a development that is *byte-identical for every
query over that carrier*. The remaining order of magnitude is not better sharing;
it is emitting that development once.

Doing so breaks the single-file contract every real-Lean suite assumes
(`lean_crosscheck`'s 77 families, `lean_module_fixtures`,
`int_inequality_lean_reconstruct`, `regex_emptiness_lean_reconstruct` each hand
**one file** to `lean`), and needs an `.olean` build with `LEAN_PATH` set. That
is why it is a decision and not a refactor.

## Decision

**The split module layout is supported and measured, and it is additive: the
self-contained single file remains what the front door emits.**

Two renderers, both on `Kernel`:

- `render_lean_prelude_module(module_name, roots) -> LeanPreludeModule` — every
  declaration reachable from `roots` (declaration **names**), in dependency
  order, with no theorem and no `#print axioms`. It is a development, not a
  claim.
- `declarations_reached(&[goal, proof])` — the closure a module rendering those
  expressions would have to declare, so a caller can compute the root set below
  rather than guess it.
- `render_lean_module_compact_importing(theorem, goal, proof, real_inductives,
  &LeanPreludeModule)` — the same query module the compact writer produces, with
  the shared declarations **skipped** and `import <name>` in their place.

Three properties are decided rather than left implicit:

1. **The `@`-application set is computed over the whole reachable set, never
   over the subset a file writes out.** Whether a constant needs `@` is a
   property of the constant (Lean makes an inductive's parameters and a
   recursor's motive implicit), not of which file declares it. A query module
   that imports `Or` must still write `@Or.rec`.
2. **Lean's compiler-internal constants (`lcErased`, `lcAny`, `lcVoid`) are
   declared exactly once across a module set** — in the shared half. Twice is
   `has already been declared`; never is `Unknown constant lcErased` under a
   toolchain that runs codegen over a Prop-valued inductive carrying data.
3. **The elaborator options are repeated in both halves.** `set_option` and
   `noncomputable section` are module-scoped in Lean and do not travel through
   an `import`.

**And the root set is the union of what the query family REACHES, not the whole
carrier environment.** This is the one design point that a measurement, rather
than taste, decided — see the finding below.

### The finding that forced it: the carrier context contains declarations Lean rejects

The obvious root set is "every declaration in the carrier context". It does not
work, and why is worth recording because nothing in the repository could have
predicted it. Measured 2026-08-18 on `LraReconstructCtx::try_new_over_constructed_reals`:

* the context holds **465** declarations; a refutation reaches **343** of them
  (the union over the three front-door fixtures);
* rooting the shared module at all 465 emits a 2,343,888-byte file that **Lean
  4.30.0 refuses**, at `CReal.Equiv.not_zero_one` and `CReal.not_le_one_zero`
  (plus two theorems that cite the first, which then fail with
  `unknown constant`);
* the in-tree kernel admits all four. They had simply never been in an emitted
  module, because no refutation reaches them — the renderer has always emitted
  only the reachable slice, so 122 declarations of this carrier have never been
  handed to any Lean;
* it is **not** a rendering artefact of the sharing pass: re-emitted with
  scope-aware `let` sharing off (7,187,035 bytes) Lean gives the same two
  rejections at the same declarations, and raising `maxHeartbeats` to 0 does not
  move them either.

That divergence is a real defect in the constructed-real development and it
belongs to the lane that owns that prelude; this ADR does not fix it. What it
decides is that the shared module is **rooted at the reached union**, which is
both emitted-once (one set for the whole family) and checkable — measured below.

The general shape is this repository's own: *a tool pointed at a subject it had
never covered reports something new, and the new thing is not always good news.*
Splitting the module is what pointed Lean at those 122 declarations for the
first time.

**And the cost is stated, not hidden behind the byte count.** A self-contained
module is checked by `lean Query.lean` and nothing else. The split needs

```text
lean --root <dir> -o <dir>/<Name>.olean <dir>/<Name>.lean
LEAN_PATH=<dir> lean --root <dir> <dir>/Query.lean
```

`--root` is not optional: Lean derives a module name from the file's path
relative to the root directory, which defaults to the working directory, so
without it the compile step dies with `input file … must be contained in root
directory`. That recipe is **generated from the artefact**
(`LeanPreludeModule::check_script`) rather than copied into prose, so it cannot
drift from the module name, and it is the recipe the gate actually runs.

## Evidence

`crates/axeyum-lean-kernel/tests/real_lean_shared_prelude_crosscheck.rs` hands
the pinned Lean 4.30.0 four invocations on a refutation whose case split carries
an inductive, its constructors **and** its recursor across the import boundary:

1. compile the shared development to `.olean` — must succeed;
2. check the query module against it — must succeed, and its `#print axioms`
   must still report the query's own hypotheses (`#print axioms` traverses
   imported proofs, so the axiom-freedom claim is untouched);
3. **negative control**: the same query module with `LEAN_PATH` set to the empty
   string must FAIL. Without this, "Lean accepted the query module" would be
   consistent with the import having done nothing;
4. **negative control**: a module that re-declares what its import supplies must
   FAIL — so the suppression is load-bearing rather than cosmetic.

The environment is set to `LEAN_PATH=""` and not merely left alone, or an
inherited value from a developer's shell would make control 3 pass for the wrong
reason.

`crates/axeyum-solver/examples/shared_prelude_module.rs` measures the layout on
the front door's own fixtures and makes its exit status depend on the finding
(`--require-split`): every query module at least 50x smaller, the shared module
**byte-identical across fixtures** (the property that makes "emit once, import
many" sound rather than merely convenient), and the kernel footprint covered.

| fixture | self-contained | split |
| --- | --- | --- |
| strict-bound `x<0, 0<=x` | 1,304,276 B | **5,056 B** + 1,715,764 B shared (257x) |
| three-row `x+y<=0, 1<=x, 1<=y` | 1,330,091 B | **14,567 B** (91x) |
| sos-square `x*x<0` | 1,442,247 B | **1,954 B** (738x) |

And the real artefact was handed to the pinned Lean, not only the suite's toy:
the 1,715,764-byte shared module compiles in **14.4 s** to a 3,786,256-byte
`.olean`, after which the query module checks in **0.102 s** and prints

```text
'axeyum_refutation' depends on axioms: [axeyum.reconstruct.lra.hyp._1,
 axeyum.reconstruct.lra.hyp._2, axeyum.reconstruct.lra.x._0]
```

— the query's own three hypotheses and no carrier axiom, which is the headline
claim unmoved. With `LEAN_PATH` cleared the same file is rejected
(`unknown module prefix 'AxeyumCarrier'`).

The footprint check is **not** a line count over the two halves summed. The
shared module is rooted at the union over a query family, so it legitimately
carries axioms a given refutation never reaches, and a sum would exceed the
footprint for a module set that is perfectly correct. What is asserted instead is
coverage in both directions: every footprint entry is declared by one of the two
halves, and the query half declares no `axiom` outside the footprint.

Comparing those two sets needs one more thing that is easy to get wrong and was:
`Kernel::display_name` and `Kernel::lean_name` are **not the same string**. A
numeric name component is not a legal Lean identifier on its own, so
`axeyum.reconstruct.lra.x.0` is emitted as `…x._0`, and the kernel's
computational naturals are rooted at `AxNat` so they do not shadow Lean's `Nat`.
The first draft of the check compared display names against module text and
reported "footprint not covered" for an artefact that was entirely correct.
`Kernel::lean_name` is public for exactly this comparison.

## Alternatives

**Make the split the default and change the front door's return type.** Rejected
for now. `prove_unsat_to_lean_module` returns one `String`, and 17 real-Lean
suites hand that string to `lean` as a complete file. Switching them all would
mean every one of those suites acquires an `.olean` build step, and the
project's strongest artefact — "here is one file, run `lean` on it" — would be
retired in exchange for a byte count. The split is available to any caller that
wants it and is measured; making it the default is a separate decision that
should be taken when a consumer needs it.

**Push harder on in-file sharing.** Measured and exhausted by the previous lane:
the named-DAG ceiling is 7.7x, of which about 2x is realisable, and 2.01x was
realised. The remaining factor is not there.

**Emit the development as a `lake` package.** Heavier: it adds a build system to
the reproduction recipe. Two `lean` invocations are the smallest thing that
works, and they are what the gate runs.

**Root the shared module at the whole carrier environment.** Rejected by
measurement, not by preference: the resulting file does not compile. See the
finding above.

## Consequences

Easier: a corpus of refutations over one carrier costs one copy of the
development plus a few kilobytes each, instead of ~1.3 MB each.

Harder: anything consuming a split artefact must carry the `.olean` and the
`LEAN_PATH`, and must say so. A published split module without its shared half is
not checkable, and a claim resting on one is weaker than the same claim resting
on a single file — this ADR is where that is written down, so the byte count is
never quoted without it.

Also harder, and newly visible: the shared module's root set is a **choice**, and
a wrong one produces an artefact Lean refuses for reasons unrelated to the
refutations importing it. `declarations_reached` exists so that choice is
computed rather than assumed.

Revisit when a consumer (a corpus export, a public artefact drop) actually needs
the split by default; that is the point at which the 17 suites' single-file
assumption should be re-costed rather than before. Revisit sooner if the
constructed-real lane fixes `CReal.Equiv.not_zero_one` and
`CReal.not_le_one_zero`, at which point the whole-environment root becomes
available and the "reached union" restriction can be reconsidered.
