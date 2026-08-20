# ADR-0522: The axiomatized reals are renamed `AxReal` before they are retired

Status: accepted
Index-summary: The `Real` package's 30 axioms are dangling — no shipped route reaches them, and the negative control they were retained for was replaced by one assumed law over a constructed carrier. Retirement is mechanical but multi-step, so the package is FIRST renamed `Real` -> `AxReal`, following the existing `AxNat` precedent: `CReal` contains `Real` as a substring and does not contain `AxReal`, so the rename permanently kills a confusion already worked around in code, and converts every surviving reference from an accident into a deliberate statement.
Index-status: accepted

Date: 2026-08-19

Related: [ADR-0509](adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md),
[ADR-0512](adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md),
[ADR-0515](adr-0515-a-negative-control-is-one-assumed-law-over-a-constructed-carrier.md).

## Context

The trusted surface, re-derived by `scripts/gen-lean-axiom-ledger.py --check`:

    complex 0 · creal 0 · integer 0 · logic 0 · nat 0 · rat 0 · string 0 · real 30

`real` is the axiomatized ordered-field package and the only nonzero row. Two
reasons were given for retaining it. One is now false and the other is weaker
than it sounds.

**"It is the negative control."** Discharged. `build_control_carrier`
(`crates/axeyum-solver/src/reconstruct/arithmetic/control.rs`) constructs ℤ and
assumes exactly **one** law, and ADR-0515 records why that is *stronger* than
thirty: the single assumed axiom is provably redundant — its discharge sits
beside it as a footprint-empty theorem — which the 30, being merely relatively
consistent, are not. Measured while building it: **nine of the 30 are reached by
no fixture at all**, and only three (the carrier, `lt`, `lt_irrefl`) are reached
by all five. Even as a control the package was mostly dead weight.

**"The relative-consistency models need it."** True but circular now.
`arith_model.rs`, `creal_model.rs` and `rat_prelude/model.rs` build the package
in order to prove its 30 axioms satisfiable. That mattered while reconstruction
*assumed* them — it said the thing being assumed is consistent. Since no shipped
route reaches them (ADR-0509), it is a consistency proof about a package nothing
uses. Historically it discharged ADR-0456's "the only model was Int"; it is not
protecting anything today.

## Why the count cannot simply be reduced

`Real`'s carrier is **opaque**: nothing over it is definable, so every operation
and every law must be assumed. There is no subset of five from which the other
twenty-five follow, because there is nothing to derive *from*. **30 is the floor
for an axiomatized ordered field, not a choice.** An earlier instruction to
"shrink the control from 30 axioms to one" was therefore structurally impossible
as written, and the answer was to invert the design rather than shrink the
number — construct the carrier, assume one law.

So the question is not "how many axioms should the package have" but "should
there be an axiomatized package at all", and the answer is no.

## Decision

**Rename before retiring, in that order.**

1. `Real` -> **`AxReal`**, following the convention `lean_pp.rs` already
   established for `AxNat`, where our computational naturals are renamed so they
   cannot collide with Lean's builtin `Nat`. The same collision exists here and
   is already worked around in code —
   `crates/axeyum-solver/examples/front_door_carrier.rs:169` reads *"`CReal.`
   also matches a `contains(\"Real.\")` test, so the carrier is decided by the
   carrier DECLARATION"*. `CReal` contains `Real`; it does not contain `AxReal`.
1b. **And the prelude LABEL, not only the declarations.** Landed
   2026-08-19 as a correction, because step 1 as first executed renamed the
   declarations and left the ledger filing them under prelude `real` — so the
   table a referee reads said `real 30` about thirty rows every one of which is
   named `AxReal.…`. That is not a smaller version of the problem this ADR
   describes; it is the problem, with the two halves now openly disagreeing and
   only the misleading one on screen. The lesson generalises past this rename:
   **a rename is not landed until the thing that PUBLISHES the name has moved.**
   Renaming declarations is the half a compiler checks and therefore the half
   that gets done.

   Landed atomically per Consequences below — four Rust labels, `SOURCE_PATHS`,
   `EXPECTED_PRELUDES`, the 30 committed entries and the count-claim groups in
   one commit — and the total read 30 before and 30 after, never 31.

   The generated ledger now also carries a paragraph stating what `axreal` is,
   that ADR-0509's *declared* is not *reached*, and that the `creal`/`complex`
   rows beside it at zero are what the shipped route uses. The table previously
   assumed its reader already knew all three.

2. Then retire: the three model developments re-expressed as telescope
   instantiations, two standing facts restated, a new home for
   `arith_prelude_builds()`, and the ledger population swap.

   **Known blocker, recorded 2026-08-19:** `axeyum-lean-kernel` depends on no
   other axeyum crate, but `generalize_over_ordered_ring` — the telescope the
   re-expression needs — lives in `axeyum-solver` while the models live in the
   kernel. Step 2 therefore needs a layering decision (move the telescope down,
   invert the dependency, or re-express without it) before it can start, and
   that decision is ADR-sized in its own right. Step 1/1b do not depend on it,
   which is why they are landed and this is not.

## Why this order

The rename is mechanical and its value does not depend on the retirement
finishing. It converts every surviving reference from an accident into a
deliberate statement, so what still depends on the axiomatized package can be
*read off* rather than grepped for a word that matches two different things.
And if the retirement stalls partway — it touches ~29 `.rs` files — what remains
in the tree is unambiguous rather than confusing, which is the failure mode the
rename exists to prevent.

## Consequences

The ledger population swap must be **one change**. Done in two steps it
publishes `real 30 + control 1 = 31` — a trusted surface larger than today's,
which is worse than not starting. (Step 1b above was the first exercise of this
rule and honoured it: `total=30|axreal=30|…`, with no intermediate state in
which both labels existed.)

Retiring the package must not remove the ability of any axiom-freedom
measurement to fail. `front_door_carrier`, `ordered_ring_refutation` and
`signature_tests` all read a non-empty comparison; the constructed control
carries that now, and the retiring lane must **demonstrate** it rather than
assume it.

The honest headline afterwards is "trusted surface zero", with no asterisk about
a retained package. Until then the two numbers stay published separately:
declared 30, reached 0.
