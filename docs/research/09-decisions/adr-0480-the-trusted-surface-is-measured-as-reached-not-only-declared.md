# ADR-0480: The trusted surface is measured as *reached*, not only as *declared* — and the `Real` package is retained as a specification and a control

Status: accepted
Date: 2026-08-18
Index-summary: `real: axiom=30` is the last nonzero row of the axiom ledger, and no shipped route rests on it — but the ledger publishes what is DECLARED, so deleting the package is the only thing that moves the number. Deleting it is refused: those 30 axioms are the kernel-checked, digest-pinned statement of the ordered-ring interface that three constructed carriers are checked against, and the NEGATIVE CONTROL for every axiom-freedom measurement here. A second number is published instead — *reached*, counted at `build_arith_prelude` itself, gated, and **0** across all four shipped arithmetic arms. The route to declared = 0 is named: move the interface statement to the axiom-free 30-binder telescope the abstraction already produces, and shrink the control from 30 axioms to one.
Index-status: accepted

## Context

Measured 2026-08-18, `nat_axiom_inventory --include-constructed`:

```text
logic: 0   nat: 0   integer: 0   rat: 0   string: 0   creal: 0   complex: 0
real:  axiom=30 opaque=0 quotient=0 total_trusted=30
```

One nonzero row, and it is 30 of 30 rows of `docs/plan/lean-axiom-ledger-v1.json`.
[ADR-0468](adr-0468-real-is-constructed-as-a-setoid-over-the-rationals.md) built
`CReal` at zero trusted declarations and `a6ee37c6a` moved the shipped LRA/SOS
front door onto it, so the axioms are unnecessary for the route that ships. The
obvious next step is to delete them.

Two things had to be established before that step could be taken or refused.

**What still reaches the axioms.** The `RingSignature` seam (ADR-0468 phase R3)
already made the carrier a parameter, and the `Real` package is one instance of
it. Re-measured on 2026-08-18, 30 `.rs` files name the package (a prior survey
said 38, counting docs). Only three call sites in non-test `src` build it:
`LraReconstructCtx::try_new`, and the three relative-consistency models
(`build_int_model_of_arith`, `build_rat_model_of_arith`,
`build_creal_model_of_arith`), each of which builds it **by design** — an
obligation computed from the axioms as they stand in the environment needs the
axioms it is relative to.

**What the ledger measures.** It measures *declared*. That is deliberate and
right: `--check` cross-checks two independent inventories, pins every row's
canonical type by SHA-256, and reports the direction of any move
([ADR-0465](adr-0465-the-axiom-ledger-is-derived-not-transcribed.md)). A referee
can check it in one command and a competitor cannot inflate it. But it means the
published trusted surface does not distinguish an axiom a theorem rests on from
an axiom nothing rests on, and the whole of this repository's remaining 30 are
the second kind.

## Decision

**The trusted surface is published as two numbers, and only one of them is the
axiom ledger's.**

1. *Declared* stays exactly as it is: the axiom ledger, unchanged, `real: 30`,
   digest-pinned, gated by `gen-lean-axiom-ledger.py --check`. It is not
   redefined, not scoped, and no prelude is removed from its population to
   improve it.
2. *Reached* is a new, separately gated number: how many times a route asks for
   the axioms. It is counted at `build_arith_prelude` itself — a process-global
   `arith_prelude_builds()` — and read through `prove_unsat_to_lean_module` on
   one fixture per shipped arithmetic arm. It is **0**.

**The `Real` package is retained**, for two reasons that are not "migration is
work":

- it is the **specification**: 30 kernel-checked declarations whose canonical
  types are SHA-256-pinned in the ledger, and which three constructed carriers
  are checked against by interpretation, with the obligations *computed from the
  axioms* rather than restated. `ArithModel.identical` reports `true` for all 22
  laws at ℤ, so the two developments say the same thing symbol for symbol; and
- it is the **negative control**. `examples/front_door_carrier.rs
  --require-axiom-free`, `examples/ordered_ring_refutation.rs --require-empty`
  and `signature_tests` all measure "zero carrier axioms over the constructed
  carrier" *beside* the same measurement over `Real`, and all of them fail if the
  `Real` column comes back empty. Delete the package and every axiom-freedom
  claim in this repository loses the thing that proves the measurement can be
  non-zero. That is the failure this project has already audited itself for: a
  checker that cannot fail is worse than no checker.

## Evidence

`F:shipped-front-door-reaches-no-real-axiom`, seven evidence rows, each verified
by `scripts/new-fact.py` to fail on mutated output before the fact was written:

```text
FRONT_DOOR_REACH lra          | fragment=Lra            arith_prelude_builds=0
FRONT_DOOR_REACH sos          | fragment=Sos            arith_prelude_builds=0
FRONT_DOOR_REACH disjunctive  | fragment=DisjunctiveLra arith_prelude_builds=0
FRONT_DOOR_REACH int-farkas   | fragment=IntFarkas      arith_prelude_builds=0
FRONT_DOOR_REACH control      |                         arith_prelude_builds=1
```

The fourth row is the reason this ADR is not a formality. Until 2026-08-18
`ProofFragment::IntFarkas` — shipped, on the front door — built the `Real`
package, refuted there, abstracted all 30 constants back out with
`generalize_over_ordered_ring`, and instantiated at ℤ; the scan
(`int_farkas_reconstruction_certifies`) trial-builds the module to classify, so
an integer query paid for it **twice**. Every footprint-shaped check passed the
whole time, because the finished term genuinely named no `Real` axiom. And the
gate for exactly this claim, `front_door_carrier --require-axiom-free`, has three
fixtures, all real-typed: they route to `Lra` and `Sos` and never reach the
integer arm. A correct empty answer to a question the tool was never asked.

That is the case for *reached* being a distinct number rather than a restatement
of the footprint: for one day the two disagreed, and only the footprint was being
watched.

The mutation check: restore the old body of
`reconstruct_int_farkas_to_lean_module` and **exactly one** test dies, the new
one. All nine tests of `tests/farkas_over_the_integers.rs` — the suite named for
that route — pass under the mutation, because they assert on the module and the
footprint and both were already clean.

Making the integer arm axiom-free needed no new mathematics. `IntPrelude`
already carries all 30 signature fields under the same names with every law
proved, so `RingSignature: From<IntPrelude>` (commit `47b71d2e9`) is the
interface at ℤ with the kernel's own `Eq` as ring equality — the corner neither
other instance occupies, since `Real` has `Eq` at the cost of 30 axioms and
`CReal`'s equality is the defined `CReal.Equiv`. Measured: all 30 integer
declarations have an empty `axiom_footprint`, against 30 non-empty for `Real` in
the same test; the four integer tests run in 1.0 s where the `CReal` tests beside
them take 98 s.

## Alternatives

**Delete the package.** Rejected, for the two reasons above, and with a cost
that is not the reason but is real: it makes
`F:real-axioms-modelled-by-constructed-setoid` unstatable, along with the ℤ and
ℚ models. Those are results — a machine-checked relative consistency for the
package, and the discharge of ADR-0456's "ℤ is not ℝ" caveat.

**Redefine the ledger to publish `reached` instead of `declared`.** Rejected.
The declared number is the auditable one; replacing it with a number derived from
a set of fixtures would trade a digest-pinned inventory for a coverage claim, and
this ADR exists precisely because a coverage claim was wrong for a day. Publish
both, and let the gap be visible.

**Remove `real` from the ledger's prelude population** (it is no longer a
*reconstruction* prelude, so it does not belong in a "reconstruction prelude axiom
ledger"). Rejected as the same move wearing a definition: nothing about the
declarations changes, and the total falls to zero. If the population ever changes
it goes through `--accept-population-change`, which files departed rows as
*retired* rather than deleting them.

**Re-base `Real` on ℤ as definitions** (`Real := Int`, each law a theorem). It
would take declared to 0 with no deletion, and it is wrong: it names ℤ "Real",
and a reader — or a later lane — would take a refutation over it for a statement
about ℝ. The repository already carries the honest version of that under its own
name.

## Consequences

**Easier.** The trusted-surface question now has an answer that a gate enforces
rather than an argument: a route that reintroduces a dependency on the axioms
fails a test, regardless of what its proof term's footprint says. New carriers
are cheap — the interface has three instances and adding a fourth is a `From`
impl plus `validate_in`.

**Harder.** Two numbers must be kept honest instead of one, and the *reached*
number is only as good as its fixture coverage — which is exactly how the
previous gate failed. `tests/front_door_reaches_no_real_axiom.rs` pins the
fragment each fixture routes to, so a fixture that stops covering its arm fails
rather than passing quietly; that pinning is load-bearing and must not be relaxed.

**The route to declared = 0, named so it is not rediscovered.** Both retention
reasons are dischargeable, in this order:

1. *The specification.* `generalize_over_ordered_ring(_, RingTelescope::FullInterface)`
   already produces a kernel term whose type binds the carrier, the seven
   operations and the 22 laws as Π-binders, with an empty axiom footprint. That
   term **is** the interface, stated in the kernel and assuming nothing. Moving
   the ledger's digest pin onto it — and re-expressing the three models as
   instantiations of it rather than as interpretations of 30 axioms — removes the
   first reason.
2. *The control.* A control needs *an* assumption with a non-empty footprint, not
   thirty. One deliberate `axiom` declared for the purpose, named as a control and
   excluded from no count, does the job that 30 do today.

Once both are done the package's population goes to zero through
`--accept-population-change`, which publishes the 30 rows as retired rather than
deleting them — a reduction in the trusted surface stated as a reduction. Neither
step was attempted here; both are bounded and neither needs new mathematics.

**Revisit when** a shipped route needs an ordered *field* (the current package has
no inverse and no division, so a division-using certificate has no destination),
or when the ledger grows a second nonzero row — at which point the
declared/reached split has to be stated per prelude rather than for `real` alone.
