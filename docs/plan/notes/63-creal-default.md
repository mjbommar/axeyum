# agent-creal-default — detail

Companion to [`../status/63-creal-default.md`](../status/63-creal-default.md).

## Slice A — `PreludeKey::CReal`

`build_creal_prelude` had no cache key, and its cost was the stated reason the
default carrier had not moved. It is now split into a cached front and
`build_creal_prelude_uncached`, which registers the package under
`PreludeKey::CReal`; `prelude_cache::slot`/`template` gained the arm.

Measured with `examples/prelude_build_timing` (which now also times `rat` and
`creal`), 3 iterations, this host:

| profile | construction (iter 0) | reuse (iter 1, 2) |
|---|---|---|
| debug, before | 83.52 s / **43.97 s** | — (no template) |
| debug, after | 47.60 s | **0.1494 s**, 0.1497 s |
| release, after | 4.688 s | **0.0674 s**, 0.0677 s |

`templates_built` moves 4 -> 5, which is how the run proves it cached rather
than that the number simply fell. Second-order: the crate's `creal`+`complex`
test selection went 33 tests / 166.82 s wall / 15m12s CPU to 35 tests /
122.48 s / 9m56s CPU, and the two added tests include the ~90 s one that builds
`CReal` twice on purpose.

`rat` is still uncached at ~1.43 s per call. It is the obvious next key and was
left alone deliberately: `creal` is 30x larger and one change at a time is
mutation-checkable.

### The mis-wiring the coordinator flagged

A slot wired to the wrong builder would hand back the axiomatized `Real`
package under the name `CReal`, and every "did it build?" check would pass.
`the_creal_slot_restores_the_constructed_reals_and_nothing_else` asserts the
restored `PreludeValue` variant, an empty trusted surface, the presence of
`CReal`/`CReal.Equiv`/`CReal.add`/`CReal.le`, and the **absence** of `Real`.
Checks 2-4 are not redundant with check 1: a mis-wire to any other axiom-free
prelude passes the surface check and fails the presence check.

Measured, release, this worktree: `nat_axiom_inventory --include-constructed`
gives `creal: axiom=0`, `complex: axiom=0`, `real: axiom=30`, byte-identical
across three runs and byte-identical with `AXEYUM_PRELUDE_CACHE=0`. That
differential is no longer manual —
`scripts/check-prelude-reuse-equivalence.sh` now takes `binary[:args]` entries
and runs `nat_axiom_inventory:--include-constructed`. Without it the gate ran a
command that never built the constructed carriers, which is the standing
"empty result from a tool never pointed at your subject" trap. Note the
`creal`/`complex` evidence there is entirely on **stderr** (they have no axiom
rows to print), so the gate's per-entry line reports both streams.

## Slice B — the carrier flip

`RingSignature: From<CRealPrelude>` and `EqualitySlot: From<CRealPrelude>` move
the construction that lived in `examples/ordered_ring_refutation.rs` into the
library. `LraReconstructCtx::try_new_over_constructed_reals[_reporting]` builds
it and adopts the equality slot. `reconstruct.rs::lra_ctx()` is the single
carrier decision, shared by `lra_farkas_reconstruction_certifies` (the
classifier) and the three dispatch arms, so the two cannot disagree about which
carrier a query was accepted on.

`refutation_axiom_footprint` + `carrier_axioms_of` are the measurement:
`Kernel::axiom_footprint` of the proof admitted as `Theorem : False`, minus the
`axeyum.reconstruct.` namespace. The example also counts the emitted module's
`axiom` lines and requires the two to be EQUAL per fixture, so neither can drift
alone: 3, 5 and 2 over `CReal` against 15, 22 and 10 over `Real`.

That count corrects a claim recorded the same day on
`F:farkas-refutation-over-constructed-reals`, that "a module for the closed
False over CReal would emit the entire nat/int/rat/CReal development as axioms
and defeat the claim". It does not. `write_lean_module_impl` collects **every
reachable inductive** and emits it as a real Lean `inductive`, so the
construction contributes zero axiom lines; `real_inductives` is a request, not
the whole set. That fact's note is wrong and I have not edited another lane's
fact to say so.

### The renderer defect the carrier flip found

The flip's first run **failed the real-Lean gate**: 5 of 77
`lean_crosscheck` families rejected, `Unknown constant Int.natAbs` and a cascade
of `Invalid field notation`. Cause: `reachable_decl_order` ordered an inductive
by `decl_deps`, which is its own type — `Sort 1` for `Rat`, depending on nothing
— while the renderer writes the family's **constructors inline**, and
`Rat.mk`'s type mentions `Int.natAbs`. The module emitted `inductive Rat` at
line 255 and `def Int.natAbs` at line 365. The `Real` package could never expose
this: its only inductives are the propositional connectives, whose constructors
mention nothing that is not already above them.

Fixed with a renderer-local `render_deps` (`decl_deps` plus every constructor's
type), used in the reachability closure and the topological sort.
**Deliberately not in `decl_deps` itself**, which `Kernel::axiom_footprint`
shares: a constructor's type is not something a proof rests on, and widening it
there would move the headline metric. After the fix: 77 of 77 checked by
lean 4.30.0, 0 failed, and the golden Lean fixtures are byte-identical.

Two kernel unit tests guard it, one per half, because `lean_crosscheck` **skips
itself** when no `lean` binary is installed and proves nothing on most hosts.
The first version of the ordering test passed under mutation — the walk starts
from a `BTreeSet<NameId>`, so with the bug present the order is still right
whenever the dependency happened to be interned earlier. Interning the inductive
first is what makes it bite.

## What is left

- **The `Real` package is unused by these routes, not retired.**
  `LraReconstructCtx::new`/`try_new` still build it; it is still the `Real`
  control in three tests and the example, still the carrier of
  `ProofFragment::IntFarkas` (which abstracts it away and instantiates at Z, so
  that route was already carrier-axiom-free), and still `real: axiom=30` in the
  ledger.
- **`IntFarkas` was deliberately not flipped.** It generalizes with
  `RingTelescope::FullInterface` (30 binders) and instantiates at the integer
  model; over `CReal` it would need `SetoidInterface` (39) and nine more model
  witnesses. That is a separate slice.
- **Module size.** ~2.6 MB per shipped module is the price of the constructed
  carrier. `render_lean_module_compact` and `render_lean_module_with_inductives`
  (which emits real `inductive` commands instead of `axiom`s) are the two
  levers, and neither has been tried on this route.
- **`arithmetic-sum-of-squares.lean`** now pins the explicit `Real` render
  rather than the shipped route, so the golden fixture stays 2.4 kB instead of
  becoming a 2.5 MB review surface. `the_shipped_sos_route_is_carrier_axiom_free`
  is what covers the shipped route's carrier instead.
