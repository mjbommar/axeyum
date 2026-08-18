# ADR-0486: A negative control is **one assumed law over a constructed carrier**, not thirty over an opaque one

Status: accepted
Date: 2026-08-18
Index-summary: ADR-0480 retains the 30-axiom `Real` package for two reasons and calls both dischargeable. Measured here: the *specification* reason is discharged — the 30-binder interface telescope read off the **axiom-free** `Int` development renders byte-identical to the one read off `Real`, 30 of 30, so the ledger's digest pins do not need the axioms. The *control* reason is discharged differently than expected: an opaque carrier cannot be shrunk at all (nothing is definable over it, so every operation and law must be assumed), so the control is rebuilt the other way round — construct the carrier, assume exactly ONE law. `build_control_carrier` is the `Int` development with `lt_irrefl` assumed; it is reached by every Farkas chain, checked in both directions, and **provably redundant**, which `Real`'s 30 relatively-consistent axioms are not. Retiring the 30 ledger rows still needs the three relative-consistency models re-expressed as instantiations; that is not landed and is not free.
Index-status: accepted

## Context

[ADR-0480](adr-0480-the-trusted-surface-is-measured-as-reached-not-only-declared.md)
(numbered 0473 when written) publishes the trusted surface as two numbers,
*declared* and *reached*, and refuses to delete the `Real` package. It gives two
reasons and names both as dischargeable "with no new mathematics":

1. the package is the **specification** — 30 kernel-checked declarations whose
   canonical types the axiom ledger pins by SHA-256; and
2. it is the **negative control** — `front_door_carrier --require-axiom-free`,
   `ordered_ring_refutation --require-empty` and `signature_tests` all measure
   "zero carrier axioms over the constructed carrier" *beside* the same
   measurement over `Real`, and all of them fail if the `Real` column comes back
   empty.

This ADR is the attempt to discharge both, and it reports where the named route
holds and where it does not.

## Decision

**Both reasons are dischargeable, and the second one is discharged by inverting
it rather than by shrinking it.**

### 1. The specification moves to the telescope, and the move is *measured*

`generalize_over_ordered_ring(_, RingTelescope::FullInterface)` produces a
theorem whose type opens into 30 `∀`-binders carrying exactly the 30 statements
the `Real` package assumes. Its 30-binder prefix is a function of the
signature's declaration *types* alone, so
[`ring_interface_telescope`](../../../crates/axeyum-solver/src/reconstruct/arithmetic/ordered_ring.rs)
computes it from any `RingSignature` without a refutation to generalize.

ADR-0480 asserted that the telescope "is the interface, stated in the kernel and
assuming nothing". That is only true if the telescope read off an **axiom-free**
development says the same thing as the one read off `Real` — and that is a
measurement, not a definition. `examples/ring_interface_pin.rs` makes it:

```text
ring interface telescope: 30 binders, 30 identical, 0 differing
```

Read off `Real` (30 axioms) and off `Int` (30 theorems, trusted surface `0`), the
abstracted binder types render **byte-identical**, because abstraction replaces
`Real`/`Int` and their operations by the *same* bound variables. So the ledger's
30 digest pins can be carried by a development that assumes nothing, and the
specification reason is discharged. A differing row would not have been a bug in
the example — it would have been the honest report that pinning onto the
telescope is a silent weakening.

This also subsumes part of what `build_int_model_of_arith` says: "ℤ is a model of
the interface" and "the ℤ telescope is the same 30 statements" are the same
measurement seen from two sides.

### 2. The control is **one assumed law over a constructed carrier**

ADR-0480 says "one deliberate `axiom` declared for the purpose … does the job
that 30 do today". The obvious reading — keep `Real`, delete 29 of its axioms —
**cannot be done, and not for want of effort**:

> `Real` is an *opaque* carrier. Nothing can be defined over an opaque type, so
> every operation and every law over it has to be assumed. The floor for an
> axiomatized ordered commutative ring with `1` is the whole signature: a
> carrier, seven operations, and every law any consumer invokes.

So the control is built the other way round. **Construct the carrier; assume
exactly one of its laws.**
[`build_control_carrier`](../../../crates/axeyum-solver/src/reconstruct/arithmetic/control.rs)
builds the `Int` development — 30 declarations, all proved, measured trusted
surface `0` — declares one deliberate `axiom` with the type of `Int.lt_irrefl`,
and returns the interface with that one slot swapped. It is a genuine
`RingSignature`; `validate_in` accepts it; `reconstruct_lra_proof` runs over it
unchanged.

**Why `lt_irrefl`.** It is the step a Farkas chain *ends* on — the derivation
exists to reach `lt t t` and contradict it. Measured over the five fixtures of
`examples/ordered_ring_refutation.rs`, `lt_irrefl` is one of only three
declarations — with the carrier and `lt` — that **all five** reach; nine of the
30 are reached by none of them. So the control is reached by the shape of the
route rather than by luck.

**Why one is honest.** Three properties, and the third is the one that makes the
smaller control *better* rather than merely cheaper:

- **It is checked in both directions.** The control asserts that its axiom is
  present in the carrier footprint *and* that it is the only carrier axiom
  there. An empty footprint means the measurement stopped seeing assumptions or
  the route stopped deriving its contradiction; an extra name means the carrier
  acquired an assumption nobody declared. "The measurement broke" and "the
  measurement is trivially satisfied" are different failures and neither may
  read as green — which is exactly the property a control is judged by.
- **It is coupled to the route.** The control is the *same reconstruction*, over
  a carrier that has an assumption in it — not a footprint computed beside the
  route. A control decoupled from the route would still report non-zero if the
  reconstruction degenerated to a stub, and would therefore not be a control at
  all.
- **It is provably redundant, and the proof is exhibited.**
  `ControlCarrier::discharge` is a theorem of the control axiom's exact type,
  valued `Int.lt_irrefl`, admitted through the same trusted gate with a
  measured-empty `axiom_footprint`. `Real`'s 30 axioms are only *relatively*
  consistent (`build_int_model_of_arith` exhibits a model). So shrinking the
  control removed the last way the control itself could make the system unsound,
  while keeping the only thing it is for.

Building a control on a law that is itself **assumed** is refused: handed the
`Real` package's interface, the discharge rests on `Real.lt_irrefl` and
`control_carrier_over` declines. A control standing in for an assumption would
*grow* the trusted base rather than merely be visible in it.

## Evidence

Measured 2026-08-18 on this host.

```text
nat_axiom_inventory --include-constructed  (baseline, unchanged by this ADR)
  logic 0  nat 0  real axiom=30  integer 0  rat 0  string 0  creal 0  complex 0

ring_interface_pin
  ring interface telescope: 30 binders, 30 identical, 0 differing

control_tests
  the control environment carries exactly one axiom            -> ["axeyum.control.assumed_lt_irrefl"]
  a refutation reaches the control axiom / nothing over the integers
      control carrier : carrier_axioms_of == ["axeyum.control.assumed_lt_irrefl"]
      Int development : carrier_axioms_of == []
```

`-p axeyum-solver --lib --features full`: 1208 passing at the start of this
lane, 1212 after (three telescope tests, four control tests, one pre-existing
failure from another lane's uncommitted `reject_self_refuting_module` present
both with and without these changes).

**Mutation checks**, each killing exactly one test:

| mutation | test killed |
|---|---|
| control axiom points at `le_trans` (a law no fixture reaches) | `a_refutation_reaches_the_control_axiom_and_nothing_over_the_integers` |
| discharge-is-axiom-free guard deleted | `a_control_built_on_an_assumed_law_is_refused` |
| signature slot not swapped (control declared, never used) | `a_refutation_reaches_the_control_axiom_and_nothing_over_the_integers` |

The third is the one that matters: a control that is *declared and not reached*
looks exactly like an axiom-free run, and that is the failure this design exists
to make loud.

The discharge guard was **not** killable before `control_carrier_over` was split
out — the first version of it killed **zero** tests, because nothing could reach
a control whose discharge was not axiom-free. A guard no test can kill is this
repository's standing audit finding, so the split is load-bearing and must not
be folded back in.

## What this ADR does **not** do, stated so it is not assumed

`real: axiom=30` is **unchanged**. Retiring those rows through
`gen-lean-axiom-ledger.py --accept-population-change` needs
`build_arith_prelude` to stop declaring them, and that is blocked on work this
ADR did not do:

- **the three relative-consistency models.** `build_int_model_of_arith`,
  `build_rat_model_of_arith` and `build_creal_model_of_arith` each interpret the
  30 axioms *as axioms*. Re-expressed as instantiations of the telescope they
  survive, but they are three developments and two standing facts
  (`F:real-axioms-modelled-by-constructed-setoid` and its ℤ/ℚ siblings), not an
  edit;
- **`arith_prelude_builds()` and `F:shipped-front-door-reaches-no-real-axiom`**
  become unstatable when the package they count builds of is gone; the *reached*
  number of ADR-0480 needs a new home;
- **the ledger's own control.** The ledger's claim is "seven of eight preludes
  are axiom-free", and `real: 30` is what shows the inventory can report
  non-zero. Taking it to zero requires the control carrier to become a prelude
  the ledger measures, so that the population is seven axiom-free preludes plus
  `control: axiom=1` — a *replacement*, in one change, not a removal followed by
  an addition. Landing the control as a new ledger row on its own would push the
  published trusted surface from 30 to **31**;
- 29 `.rs` files name the package.

None of this needs new mathematics — ADR-0480 was right about that, and the
telescope measurement above is the evidence for the part that was most in doubt.
It is not, however, "bounded" in the sense of a single increment.

## Alternatives

**Shrink `Real` in place to one axiom.** Impossible; see the Decision. This is
the correction to ADR-0480's phrasing, which reads as though the 30 could be
thinned.

**Re-base `Real` on ℤ as definitions.** ADR-0480 rejects this because it names ℤ
"Real". The objection is about the *name*, and it dissolves once the artifact is
called a control rather than a carrier for ℝ — which is what this ADR does. The
control is `Int` with one assumed law and is named `axeyum.control.*`; nothing
about it invites a reader to mistake it for the reals.

**A control decoupled from the route** — one axiom, a theorem over it, and
`carrier_axioms_of` reporting it. Rejected: it catches a broken footprint filter
but not a degenerate reconstruction, and would report a healthy non-zero while
the route it is a control for produced nothing.

**Assume a law every fixture happens to use today, without checking.** Rejected,
and the repository has already paid for the general version of this: a
transposed `le_refl := Int.le_trans` type-checks and kills exactly one test, and
without that test it kills none. Reachedness is asserted per run, not designed
in.

## Consequences

**Easier.** Every axiom-freedom measurement can now be paired with a control
that costs one axiom, one theorem and a fresh `Int` development (four control
tests run in 0.55 s; the `CReal` tests beside them take 98 s). New carriers stay
cheap — a `From` impl plus `validate_in`.

**Harder.** There are now two artifacts that must agree about what the ordered
ring interface *is*: the `Real` package's 30 axiom types and the telescope's 30
binder types. `ring_interface_pin --require-identical` is what keeps them
agreeing, and it must run in the aggregate gate before the ledger's pin is moved
onto the telescope, not after.

**Revisit when** the three models have been re-expressed as instantiations — at
which point the population change is a single change that swaps `real: 30` for
`control: 1`, and the departed rows are published as retired.
