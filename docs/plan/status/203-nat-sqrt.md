# Lane: nat-sqrt — `Nat.sqrt` exists, so the largest single frontier blocker shrinks by 2

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, nat-sqrt, 2026-08-28).**

`scripts/fact-frontier.py` reported 14 open facts as `BLOCKED — statement
names undeclared kernel definition(s): Nat.sqrt`, the largest single blocker
on the frontier. `Nat.sqrt` now exists, with two boundary theorems
(`sqrt_zero`, `sqrt_one`), both admitted through `Kernel::add_declaration`
with an empty `axiom_footprint`. Two new facts (`F:nat-sqrt-zero`,
`F:nat-sqrt-one`) are `proved`; the 14 `F:ml430-nat-sqrt-*` mirror facts stay
`open` — see "not attempted" below.

**The obstacle, and how it was cleared.** Mathlib v4.30 `Nat.sqrt` is a
Newton's-method iteration under well-founded recursion (`iter (n guess) := let
next := (guess + n/guess)/2; if next < guess then iter n next else guess`).
That is not structural, and the Lean equation compiler's route to
well-founded recursion carries `Quot.sound`/`propext` — fatal to this
project's axiom-freedom metric, and exactly the trap `Nat.log` (landed an
hour earlier, `docs/plan/status/199-nat-log.md`) sidestepped the same way.

This file follows `log.rs`'s established pattern — **structural recursion on
a fuel argument** — but the recursion shape itself did not transfer verbatim,
because `Nat.sqrt` has one argument to `Nat.log`'s two and its "state" is an
accumulator that only ever grows, not a shrinking second argument:

```text
Nat.sqrtAux n 0        ≡ 0
Nat.sqrtAux n (succ f) ≡ let c := Nat.sqrtAux n f
                         in if (succ c) * (succ c) <= n then succ c else c
Nat.sqrt n             := Nat.sqrtAux n n
```

The target `n` is a captured free variable, not threaded through `Nat.rec`'s
motive at all — the motive here is the plain `fun _ => Nat` (an accumulator
fold), simpler than `logAux`'s `fun _ => Nat -> Nat` (which needed a
function there because `log`'s recursive argument, `n / b`, genuinely
changes per fuel level; `sqrt`'s target never does). `n` always suffices as
fuel: the accumulator starts at `0` and grows by at most `1` per step, and
the greatest `m` with `m * m <= n` is itself `<= n`.

Both equations are **definitional** (β/δ/ι) — no equation lemmas, no
`WellFounded`, no `Quot.sound`, no `propext`, no new kernel machinery.

Detail moved to [`../notes/203-nat-sqrt.md`](../notes/203-nat-sqrt.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-sqrt | `Nat.sqrt` by structural fuel recursion (accumulator fold, not the `logAux` shape) — 2 definitions, 2 theorems, all axiom-free; 2 facts closed (`F:nat-sqrt-zero`, `F:nat-sqrt-one`); 14 `F:ml430-nat-sqrt-*` mirror facts left open, sized for the next tier |
