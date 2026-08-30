# ADR-0631: a closure licenses a constant only if the proof mentions it — label the ones it does not

Status: accepted
Date: 2026-08-30
Index-summary: A closure licenses a bridge constant only if our proof mentions it; measured blast radius is 2 of 24 statable open propositions, the stricter rule was implemented and REFUSED because it costs 24 of 24, so the bridge is labelled and the conservative count published beside the headline

Related: ADR-0624 (the vocabulary is generated, not maintained), ADR-0619 (the
pool grows by declaring kernel constants), ADR-0542 (held-out isolation)

Lane: bridge-elision

## Context

`artifacts/autogenesis/mathlib-statable-vocabulary-v1.json` is the positive
screen for *statable in this kernel*. Its admissible set is

    admissible = env     names read from kernel.environment()
               | bridge  {Lean constants in the pinned Mathlib statements of
                          SETTLED ml430 mirrors} \ env

ADR-0619 records the rule that the pool grows by DECLARING kernel constants and
never by widening the screen; ADR-0624 makes the artifact generated rather than
maintained. Neither examines the inference the bridge rests on, which is:

> if we proved a mirror whose pinned statement mentions constant `C`, then `C`
> is expressible here, so other pooled propositions mentioning `C` are statable.

**That inference fails whenever a mirror is closed by ELIDING the constant
rather than expressing it.** `F:ml430-nat-log-antitone-left` pins

    ∀ {n : ℕ}, AntitoneOn (fun b => Nat.log b n) (Set.Ioi 1)

and closing it took the bridge from 70 to 72 by promoting `AntitoneOn` and
`Set.Ioi`. Our theorem renders as

    Nat.log_antitone_left :
      ∀ x0 x1 x2, Le x1 x2 → Lt 1 x1 → Lt 1 x2 → Le (log x2 x0) (log x1 x0)

— no `AntitoneOn`, no `Set.Ioi`, and no kernel `Set` type at all. The lane that
closed it says as much in `docs/plan/status/337-log-clog-finish.md`. What that
closure established is that *this proposition* has an equivalent pointwise
form. It did not establish that `Set.Ioi` is expressible here.

The harm is a wasted lane dispatched at a goal it cannot state, and an inflated
statable count feeding ADR-0619's headroom argument. It is **not** a wrong entry
in the fact ledger: the proof is correct and axiom-free, and nothing here
reopens or reclassifies it.

## Measurement, taken before any machinery was built

Method: join each settled catalogued mirror to its fact's
`formal.kernel_statement` — the rendered kernel type, already in the ledger, so
no cargo run is needed — and ask, per bridge constant, whether any mirror that
promoted it mentions it. Reproduce with
`scripts/measure-bridge-elision-radius.py`.

    bridge 72 = elaboration 50, expressed 2, elided 8, unrendered 12
    open pooled propositions 28, statable 24
      admitted ONLY via an elided constant     2
        Nat.clog_antitone_left    via AntitoneOn, Set.Ioi
        Nat.coprime_of_lt_minFac  via Nat.Coprime, Ne
      admitted ONLY via an unrendered constant 3
      conservative statable                   19  (headline 24)
    positive control: statable under env alone 0

`F:ml430-nat-clog-antitone-left` is LIVE in the frontier's DISPATCHABLE set and
is the direct sibling of the incident. `Nat.coprime_of_lt_minFac` is already
blocked by the divergence registry over `Nat.minFac`, so exactly one of the two
would have cost a lane. On the nursery-v2 extension the effect is larger: 72 of
260 preregistered candidates are elision-backed.

## Decision

**Keep promoting; label the reason.** The vocabulary carries a derived
`bridge_provenance` block classifying every bridge constant, and the frontier
publishes the statable count with and without the elision-backed portion. The
bridge itself is unchanged at 72. Nothing is refused on this basis.

Four classes, all derived, none hand-kept:

| class | meaning | licenses |
| --- | --- | --- |
| `elaboration` | a Lean instance (`instHAdd`, `Nat.instDvd`) or class projection (`HAdd.hAdd`, `LE.le`) | notation, not vocabulary — the rendered-type test is meaningless and is not applied |
| `expressed` | some settled witness's rendered kernel type mentions it | the bridge inference holds outright |
| `elided` | every settled witness that HAS a rendered type fails to mention it | promotion rests on an equivalent restatement |
| `unrendered` | no settled witness carries `formal.kernel_statement` | the ledger cannot say |

Two guards, deliberately duplicate implementations rather than one shared
module — the generator already refuses to import the gate's `SETTLED` on the
ground that a change to either would silently change the other, and the
argument is stronger in this direction, because a gate consuming the producer's
classification cannot catch the producer computing it wrongly:

- **V5** (`gen-autogenesis-statable-vocabulary.py`): the recorded block must be
  its derivation.
- **S7** (`check-dispatchable-frontier.py`): the same, re-derived independently.
  Not evaluated when S1–S4 have already fired, since S7 derives from the bridge
  and the row set and would otherwise double-fire on every membership control.

## Alternatives considered

**Promote only what the rendered kernel type mentions.** This was the obvious
candidate and it is REFUTED by measurement, not by argument. Mathlib's pinned
`type_repr` is 50/72 elaboration constants — `OfNat.ofNat` with 73 witnesses,
`instOfNatNat` 61, `instHAdd`/`HAdd.hAdd` 32 — which have no typeclasses to
correspond to in this kernel and can never appear in a rendering by name.
Applying the rule takes the statable open pool from **24 to 0**, against a
measured defect worth 2. The cure is roughly twelve times the disease, and it
would be the mirror-image of the error being fixed.

**Fold `unrendered` into `elided`.** Refused: 139 of 174 settled mirrors carry
no `formal.kernel_statement`, so silence is not evidence of elision. Calling an
unmeasured thing a defect is the same mistake pointing the other way. The
separate class also makes the missing ledger field visible, and shrinks
honestly as mirrors record their rendered types.

**Refuse elision-backed candidates in `--statable`.** Refused. `elided` is a
PRECISION flag, not a defect flag, and the code says so. `Monotone` is elided
and entirely safe — it unfolds to a pointwise arithmetic statement over env
vocabulary, which is exactly what this gate's docstring already says about
`Nat.fib_mono`. `Set.Ioi` is elided and thin, because it unfolds through a
`Set` type we do not have. This classifier cannot separate those two and does
not claim to; publishing the pair is honest where enforcing either half is not.

## Consequences

- ADR-0619's headroom can be quoted as 24 or 19 with the difference named,
  instead of silently as 24.
- A constant with many witnesses (`Nat.Coprime`, 22) and one with a single thin
  witness (`AntitoneOn`, 1) are no longer indistinguishable, because the block
  records witness counts alongside the class.
- The `elided` set will shrink as mirrors record `formal.kernel_statement`, and
  `unrendered` shrinks with it. Neither number is a ratchet and neither should
  become one without a further decision.

## Two findings worth carrying past this ADR

**Lean's all-caps class names decapitalize whole.** The projection of class `LE`
is `LE.le`, not `LE.lE`, so a decapitalize-first-character rule misclassifies
`LE.le` and `LT.lt`. Caught by controlling the predicate rather than trusting
it. Both constants land in a safe tier either way, which is a robustness
property worth having noticed: `elaboration` and `expressed` are both
non-suspect, so the boundary between them does not move the conservative count.

**A mutation harness against a fully DERIVED artifact does not isolate.** V5
compares the whole derived block against the committed file, so any edit to the
derivation function invalidates that file in every test case and V5 fires
throughout — 20 to 25 cases per mutant, against 5 for deleting V5 itself. That
is correct behaviour and it is not coverage; the kill counts are reported as
measured in `docs/plan/status/342-bridge-elision.md` rather than dressed up. The
frontier's S7 does isolate, because there the subject is a fixture.
