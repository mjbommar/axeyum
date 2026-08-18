# Lane notes: `agent-lean-prelude-module` — the shared development as a module

The previous lane's conclusion
([`64-module-size.md`](64-module-size.md)) was that the remaining order of
magnitude is a **shared prelude module**, and that it is ADR-sized because it
breaks the single-file contract 17 real-Lean suites assume. This is that
increment.

## What landed

`Kernel` gains four things, all additive. `prove_unsat_to_lean_module` is
untouched and still returns one self-contained file.

| API | what it does |
| --- | --- |
| `render_lean_prelude_module(name, roots) -> LeanPreludeModule` | the development reachable from `roots`, emitted once; no theorem, no `#print axioms` |
| `render_lean_module_compact_importing(…, &LeanPreludeModule)` | a query module with those declarations skipped and `import <name>` in their place |
| `declarations_reached(&[goal, proof])` | the closure a module would have to declare, so a caller computes the root set rather than guesses it |
| `lean_name(NameId)` | a name as an emitted module spells it — **not** `display_name` |

`LeanPreludeModule::check_script(dir, query_file)` generates the two-command
recipe from the artefact, so the published instructions cannot drift from the
module name.

## The measurement

`cargo run -p axeyum-solver --features full --example shared_prelude_module`,
over `LraReconstructCtx::try_new_over_constructed_reals`:

| fixture | self-contained | query half | shared | factor |
| --- | --- | --- | --- | --- |
| strict-bound `x<0, 0<=x` | 1,304,276 B | **5,056 B** | 1,715,764 B | **257x** |
| three-row `x+y<=0, 1<=x, 1<=y` | 1,330,091 B | **14,567 B** | (same) | 91x |
| sos-square `x*x<0` | 1,442,247 B | **1,954 B** | (same) | 738x |

The shared module is **byte-identical** across all three. That is the property
that makes "emit once, import many" sound rather than merely convenient, and it
is asserted rather than assumed.

It is also **larger than any single self-contained module**, so the split only
pays from the second query onward. Said here because the byte table above
invites the opposite reading.

### Real Lean, on the real artefact

Not only the suite's toy. The pinned Lean 4.30.0
(`commit d024af099ca4bf2c86f649261ebf59565dc8c622`):

```text
lean --root <dir> -o <dir>/AxeyumCarrier.olean <dir>/AxeyumCarrier.lean   14.4 s  -> 3,786,256 B .olean
LEAN_PATH=<dir> lean --root <dir> <dir>/Query.lean                         0.102 s
  'axeyum_refutation' depends on axioms: [axeyum.reconstruct.lra.hyp._1,
   axeyum.reconstruct.lra.hyp._2, axeyum.reconstruct.lra.x._0]
LEAN_PATH= lean --root <dir> <dir>/Query.lean                              REJECTED
  unknown module prefix 'AxeyumCarrier'
```

`#print axioms` traverses the imported proofs, so the axiom-freedom claim is
unmoved: the query's own three hypotheses and no carrier axiom.

`--root` is not optional and cost a gate run to learn: Lean derives a module
name from the file's path relative to the root directory, which defaults to the
working directory, so `lean -o /tmp/x/M.olean /tmp/x/M.lean` run from the crate
directory dies with `input file … must be contained in root directory`.

## The finding: 122 declarations no Lean had ever seen

The obvious root set for the shared half is "every declaration in the carrier
context". **It emits a file Lean refuses.**

```text
AxeyumCarrier.lean:792: error: Application type mismatch: …
  in the application AxNat.not_succ_le_zero AxNat.zero (And.rec …)      CReal.Equiv.not_zero_one
AxeyumCarrier.lean:828: error: Application type mismatch: …
  in the application AxNat.le_of_succ_le_succ …                         CReal.not_le_one_zero
AxeyumCarrier.lean:881: error: (kernel) unknown constant 'CReal.Equiv.not_zero_one'   (cascade)
```

The in-tree kernel admits all four declarations. The reason nobody had seen it:
the renderer has **always** emitted only the reachable slice, a refutation
reaches 343 of the context's 465 declarations, and the other 122 had therefore
never been handed to any Lean. Splitting the module is what pointed Lean at them
for the first time.

Two things it is **not**:

- not a rendering artefact of the scope-aware `let` sharing — re-emitted with
  sharing off (7,187,035 B) Lean gives the same two rejections at the same
  declarations;
- not an elaborator budget — `set_option maxHeartbeats 0` does not move it, and
  `maxRecDepth` is already 65536.

It belongs to the lane that owns the constructed reals and is **not fixed
here**. What it decided here is that the shared module is rooted at the
**reached union**, which `declarations_reached` exists to compute.

This is the repository's own shape one more time: *a tool pointed at a subject it
had never covered reports something new, and the new thing is not always good
news.*

## The trap that cost the most, and is invisible

`Kernel::display_name` and `Kernel::lean_name` are **not the same string**. A
numeric name component is not a legal Lean identifier on its own, so
`axeyum.reconstruct.lra.x.0` is emitted as `…x._0`; and the kernel's
computational naturals are rooted at `AxNat` so they do not shadow Lean's `Nat`.
The first draft of the footprint check compared display names against module
text and reported **"footprint not covered: false"** for an artefact that was
entirely correct — a false alarm that reads exactly like a real regression.
`lean_name` is public for this comparison and says so in its doc comment.

The footprint check itself is **coverage, not a summed line count**: the shared
half is rooted at a union over the query family, so it legitimately carries
axioms a given refutation never reaches and a sum would exceed the footprint for
a module set that is perfectly correct. What is asserted is that every footprint
entry is declared by exactly one half, and that the query half declares no
`axiom` outside the footprint.

## Mutation checks

`cargo test -p axeyum-lean-kernel --lib lean_pp` (25 tests) plus
`--test real_lean_shared_prelude_crosscheck` (3 tests, 4 real-Lean checks):

| mutation | tests that died |
| --- | --- |
| drop `set_option maxRecDepth` from the importing banner | **exactly 1** — `both_halves_set_the_module_scoped_elaborator_options` (24 passed, 1 failed) |
| compute the `@`-application set over the emitted subset instead of the whole reachable set | 2 — `the_split_moves_the_development_and_keeps_the_theorem` and the real-Lean suite; **0 unit tests died**, so the Rust-side guard on `@Or.rec` is the only thing between this and a module Lean rejects |
| declare the codegen constants in BOTH halves | 5 (mechanism) |
| drop `provided.contains(name)` from `write_decl_blocks` | 5 (mechanism) |

The last two remove the split itself rather than a guard, so many deaths is the
expected signature; the first shows a guard isolates. The second is the
interesting one: it is a real defect class (Lean makes an inductive's parameters
and a recursor's motive implicit, so an *imported* constructor still needs `@`)
that no unit test caught before this lane, and the assertion added for it now
does.

## What is left

- **The split is not the default.** Making it so means every one of the 17
  real-Lean suites acquires an `.olean` build step, and retires the project's
  strongest artefact — "here is one file, run `lean` on it". ADR-0482 says to
  take that decision when a consumer needs it, not before.
- **`CReal.Equiv.not_zero_one` and `CReal.not_le_one_zero` are rejected by
  Lean.** Until they are fixed the whole-environment root set is unavailable.
  Worth a fact of its own once the owning lane has looked at it; this lane
  recorded the measurement rather than guessing at the cause.
- **No corpus consumer uses the split yet.** The example measures it and the
  crosscheck gates it; nothing ships it.
