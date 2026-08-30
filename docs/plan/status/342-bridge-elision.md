# 342 — bridge elision: a closure licenses a constant only if the proof mentions it

<!-- plan-section: lane-status -->

**Lane:** `bridge-elision` · **Date:** 2026-08-30 · **Status:** landed
**Decision:** [ADR-0631](../../research/09-decisions/adr-0631-a-closure-licenses-a-constant-only-if-the-proof-mentions-it.md)

## The deficiency

The statable-vocabulary bridge promotes a Mathlib constant whenever a mirror
whose pinned statement mentions it closes. That inference fails when the mirror
was closed by **eliding** the constant. `F:ml430-nat-log-antitone-left` pins
`AntitoneOn (fun b => Nat.log b n) (Set.Ioi 1)` and promoted both constants
(bridge 70 → 72); our theorem is the pointwise
`Le x1 x2 → Lt 1 x1 → Lt 1 x2 → Le (log x2 x0) (log x1 x0)`, mentioning
neither and needing no `Set` type. Precision problem, not soundness — nothing
in the fact ledger is wrong and nothing was reopened.

## Blast radius, measured before building anything

Method: join each settled catalogued mirror to its fact's
`formal.kernel_statement` (the rendered kernel type, already in the ledger — no
cargo run needed), then ask per bridge constant whether any mirror that
promoted it mentions it. Reproduce: `python3
scripts/measure-bridge-elision-radius.py`.

    bridge 72 = elaboration 50, expressed 2, elided 8, unrendered 12
    open pooled propositions 28, statable 24
      admitted ONLY via an elided constant     2
        Nat.clog_antitone_left    via AntitoneOn, Set.Ioi
        Nat.coprime_of_lt_minFac  via Nat.Coprime, Ne
      admitted ONLY via an unrendered constant 3
        Nat.testBit_land / _ldiff / _lor        via Bool.and / Bool.not / Bool.or
      conservative statable                   19  (headline 24)
    positive control: statable under env alone 0

`F:ml430-nat-clog-antitone-left` is LIVE in the frontier's DISPATCHABLE set —
the direct sibling of the incident. `Nat.coprime_of_lt_minFac` is already
blocked by the divergence registry over `Nat.minFac`, so exactly one of the two
would actually have cost a lane. On the nursery-v2 extension the reach is
larger: **72 of 260** preregistered candidates are elision-backed.

The 8 elided constants, with the evidence behind each promotion:

    AntitoneOn    1 witness  (1 rendered)     Nat.Coprime  22 (10)
    Set.Ioi       1          (1)              Nat.ModEq    19 (1)
    Monotone      4          (2)              Nat.Prime    15 (2)
    Nat.cast      9          (1)              Ne           10 (1)

Detail moved to [`../notes/342-bridge-elision.md`](../notes/342-bridge-elision.md).

