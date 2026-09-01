# ADR-1415: the divergence registry is swept against module docs, not written once

Date: 2026-09-01
Status: Accepted
Lane: `divergence-registry-sweep`

Index-summary: `artifacts/autogenesis/mirror-divergence-registry.json` recorded 4
diverging constructions and kept offering mirrors its own tree already refused
in prose. Swept `nat_prelude`'s module docs for the mirror-flip criterion's own
vocabulary ("stays open", "different type", "not definitionally identical") and
registered 5 more: `Squarefree` (codomain, Prop vs Bool), `Nat.nth`,
`Nat.findGreatest`, `Nat.floorRoot`, `Nat.ceilRoot` (all definitional). Found and
explicitly declined two traps: `Max.max`/`Min.min`, whose own module doc's
"stays open" claim is CONTRADICTED by a later file in the same directory
(`minmax_lemmas.rs`) that proved all twelve mirrors honest — registering it
would have failed the registry's own G3 guard; and `Nat.Abundant`/`Deficient`,
a real divergence with zero matching `ml430` facts yet, which would fail G1.
Measured before/after: 11 -> 12 in the `blocked` bucket, 20 -> 19
`DISPATCHABLE` (only `Squarefree`'s mirror actually moved; the other four
constructions block mirrors already `held-out`, which is not decorative --
`--screen` and G3 still see them, and a future re-partition cannot silently
route them to `dispatchable`).
Index-status: Accepted

## Context

`docs/research/11-design-review/2026-08-29-the-mirror-population-is-consumed.md`
built the registry and its consuming gate
(`scripts/check-dispatchable-frontier.py`) from four constructions found on
2026-08-29: `Nat.testBit`, `Nat.multichoose`, `Nat.minFac`, `Nat.fastFib`. That
snapshot was correct the day it was written and went stale the moment a later
lane declared a fifth diverging construction and wrote the refusal into a
module doc rather than into the registry. `squarefree.rs` (landed after
2026-08-29) documents its `Bool`-vs-`Prop` divergence, and its own precedent
citation, `nth.rs`, documents an arity/domain divergence -- neither reached
the registry, so `check-dispatchable-frontier.py` kept counting
`F:ml430-nat-squarefree-ext-iff-7218327d` as dispatchable, and a lane spent
real effort re-deriving a refusal already written in the first forty lines of
`squarefree.rs`'s module doc.

The registry has no mechanism that notices this drift: it is a hand-maintained
list, and nothing runs a module-doc sweep against it. This ADR is not a new
mechanism (that would be its own, larger project) -- it is this sweep's
record of what a manual pass found, and the two traps it is worth naming so a
future sweep does not re-fall into them.

## What was registered

Read against the pinned Mathlib source at commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (v4.30.0) directly, not from
paraphrase (a blobless mathlib4 checkout is at
`/data0/axeyum/lean-import-toolchain/mathlib4`, no ssh needed):

- **`Squarefree`** (class `codomain`) -- Mathlib's is `Prop`-valued
  (`Mathlib/Algebra/Squarefree/Basic.lean:41`); ours is an executable
  `Bool`-valued decision procedure (`nat_prelude/squarefree.rs`), deliberately
  with no bridge theorem (ADR-0653). `codomain_witness_regex` is
  `Squarefree\s+\S+\s*→`, matched against the mirror's own pinned statement --
  a `Prop` is the only thing that can appear immediately before `→` as an
  implication antecedent, which re-derives Mathlib's codomain from the
  statement text rather than trusting this row, the mirror image of
  `Nat.testBit`'s `= true/false` witness.
- **`Nat.nth`** (class `definitional`) -- Mathlib's is `noncomputable`,
  decided by `Classical.propDecidable` and `Nat.Subtype.orderIsoOfNat`
  (`Mathlib/Data/Nat/Nth.lean:60`); ours is a fuel-bounded search with an
  extra explicit `bound` argument and a `Bool`-decidable predicate
  (`nat_prelude/nth.rs`). Surface form is `"Nat.nth "` WITH the trailing
  space -- `"Nat.nth"` bare is a literal substring of the unrelated,
  already-honest `Nat.nthRoot` family and false-matched
  `F:ml430-nat-nthroot-zero-left-8560aafb` on the first attempt.
- **`Nat.findGreatest`** (class `definitional`) -- Mathlib elaborates its
  `DecidablePred` witness as an instance implicit; this kernel has no
  instance implicits, so ours takes it as an explicit argument
  (`nat_prelude/find_greatest.rs`). Bodies agree extensionally; types differ.
- **`Nat.floorRoot`**, **`Nat.ceilRoot`** (class `definitional`, two entries)
  -- Mathlib defines both as a product over `a.factorization : Finsupp`
  (`Mathlib/Data/Nat/Factorization/Root.lean`); this kernel has no
  `Finsupp`/`Finset`, so `nat_prelude/factorization_root.rs` uses an
  extensionally-equal bounded search, verified against the closed form by
  simulation over 400 `(n, a)` pairs before any Rust was written.

Every matched `ml430` mirror for all five entries was confirmed `open` (never
`proved`) against the live fact ledger before writing the entry -- the G3
false-positive control the gate itself runs, checked by hand first because a
registry entry that blocks a settled mirror is a false claim about a
proposition this project has already established.

Full reasoning, the pinned-source excerpts, and the exact before/after gate
output: `docs/research/11-design-review/2026-09-01-divergence-registry-gaps-closed.md`.

## What was found and declined, and why that matters more than what was added

**`Max.max`/`Min.min`.** `nat_prelude/minmax.rs`'s own module doc says a
mirror "stated against Mathlib's REAL, typeclass-elaborated `Max.max`/
`Min.min` stays `open`". Taken at face value, this is a sixth candidate. It is
wrong: `nat_prelude/minmax_lemmas.rs`, in the same directory, is an explicit
correction reading the pinned Lean toolchain rather than paraphrasing it --
`Init/Prelude.lean:1311`/`Init/Data/Nat/Basic.lean:873` show Lean's `max`/
`min` at `Nat` reduce to exactly this prelude's `if a <= b then b else a` /
`if a <= b then a else b`, decided by `Nat.decLe`. Same function; only the
typeclass delivery differs, which is elaboration, not content. All twelve
`Init.Data.Nat.MinMax`/`Init.Data.Nat.Lemmas` mirrors this unblocked are
**already `proved`** (`F:ml430-nat-max-comm-a9a3642b` and eleven siblings).
Registering this construction would have tripped the registry's own G3 guard
(blocks a settled mirror) the moment the gate ran -- caught here by checking
the ledger status before writing the row, which is exactly the discipline
CLAUDE.md asks for and exactly the direction ("over-blocking removes real
work from the queue silently") it calls the expensive error.

**`Nat.Abundant`/`Nat.Deficient`.** `nat_prelude/abundant_deficient.rs`
documents a genuine divergence (body provably equivalent to, not
definitionally identical with, Mathlib's proper-divisor-sum phrasing;
ADR-1100). But zero `ml430` mirror facts exist for either name yet --
`Mathlib.NumberTheory.FactorisationProperties` has not been drawn into the
nursery. Registering it now would trip G1 (a blocker matching nothing is
stale) on the next gate run. Left unregistered, and recorded in the
design-review doc so whoever preregisters that module's mirrors adds this row
in the same commit, rather than re-discovering the divergence and the
staleness trap separately.

## What was found and correctly left open, not registered

`Nat.lt_xor_cases` (`nat_prelude/xor_order.rs`) and the Stirling-number
mirrors (`nat_prelude/stirling_lemmas.rs`) both use "stays open" language in
their module docs, but for the ordinary reason: the statement is expressible
and true here and simply unproved. Stirling's own doc says its ten mirrors
"flip honestly" once proved; `lt_xor_cases` needs a highest-differing-bit
`testBit` induction nobody has built yet. Neither belongs in a registry whose
entire purpose is propositions that can NEVER honestly flip.

`F:ml430-nat-fermat-primefactors-one-lt-58343c6f` is the same shape at a
larger scale: blocked on missing infrastructure (multiplicative order mod
`p`, Fermat's little theorem via Lagrange, a quadratic-residue argument), not
a divergent construction. It stayed `DISPATCHABLE` in the after-measurement,
correctly. A mechanism for "blocked on infrastructure" already exists
(`scripts/gen-infrastructure-frontier.py`/`check-infrastructure-frontier.py`,
ADR-0845) but populating it needs the graph-join/declaration-graph generation
pipeline and was out of this sweep's scope; the category is recorded in the
design-review doc rather than left implicit.

## Consequence

A registry entry for a mirror already in the `held-out` partition changes
nothing in `check-dispatchable-frontier.py`'s reported buckets today
(`classify()` checks the held-out/mutation partition before it ever consults
the registry), which is why 4 of the 5 new entries moved the `blocked` count
by zero. Register such constructions anyway: the registry is also the input
to `--screen`/`--statable` candidate screening, to G3's false-positive
control the moment a producer tries to close one of these mirrors, and to
whatever gate exists the day one of these 31 mirrors is repartitioned out of
`held-out` -- at which point an already-present entry routes it straight to
`blocked` instead of `dispatchable`, silently, which is the entire point of
the registry existing before that day rather than after it.
