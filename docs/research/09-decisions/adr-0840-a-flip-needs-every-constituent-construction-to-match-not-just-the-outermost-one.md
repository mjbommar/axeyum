# ADR-0840: A mirror flip needs EVERY constituent construction to match Mathlib's, not just the outermost recursion principle

Status: accepted
Date: 2026-08-30
Index-summary: `F:ml430-nat-fastfib-eq-cde11774` was recorded as blocked by
one obstruction (`Nat.binaryRec` needing a dependent motive a fuel encoding
cannot supply). This ADR corrects that framing twice over: (1) the kernel
already has a computing, DATA-motive `WellFounded.fix` (proved by
`nat_strict_well_foundedness_drives_generic_strong_recursion`), so a
well-founded `binaryRec` is buildable; and (2) it would not matter if it
were built, because Mathlib's `fastFib` is a CHAIN of two independently
divergent constructions (`binaryRec`'s recursion principle AND `Nat.fib`'s
own recurrence device), and a flip needs the whole chain to match, not one
link. The mirror stays open either way; the honest outcome is a new local
fact, and building one is ordinary, unblocked work.

## Context

`docs/plan/status/250-nat-fastfib-minfac.md` (2026-08-29) sized
`F:ml430-nat-fastfib-eq-cde11774` and, separately, CLAUDE.md's Gotchas
record a same-day correction: an earlier over-generalization ("any mirror
whose Mathlib definition is `WellFounded.fix` with a dependent motive is
permanently blocked") was refuted by `F:ml430-nat-base-induction` closing
with the kernel's actual `WellFounded.fix.{u,v}` primitive. That correction
left the narrower claim standing: "a FUEL encoding's non-dependence is
forced," and concluded `fastFib` is "blocked on a `binaryRec` built the
well-founded way rather than the fuel way, which is ordinary work."

This lane (`blocked-mirror-divergences`) was briefed to verify that
narrower claim in-tree before relying on it, per the standing rule that a
handoff's "blocked on X" is a claim about one route, not the target.

## What was verified

1. **`Nat.binaryRec` (fuel-based, `nat_prelude/binary_rec.rs`) already
   exists**, with signature `Π (alpha : Type 0), alpha -> (Bool -> Nat ->
   alpha -> alpha) -> Nat -> alpha` — non-dependent, exactly as the prior
   analysis described, plus a checked `binary_rec_succ` equation
   (`binaryRec … (succ m) = f b half (binaryRec … half)`).
2. **Mathlib's `fastFibAux` instantiates `binaryRec` at a NON-dependent
   motive.** Read directly at the pinned commit
   (`Mathlib/Data/Nat/Fib/Basic.lean:170`, `c5ea0035…`):
   `def fastFibAux : ℕ → ℕ × ℕ := Nat.binaryRec (fib 0, fib 1) fun b _ p =>
   …`. The motive is `fun _ => ℕ × ℕ`, constant in `n`. So the "fuel forces
   non-dependence" obstruction the prior analysis named does not actually
   apply to THIS mirror — `fastFibAux` never needs a dependent motive.
3. **The kernel already has a genuinely computing, DATA-valued
   `WellFounded.fix`.** `nat_prelude_tests.rs`'s
   `nat_strict_well_foundedness_drives_generic_strong_recursion` builds a
   closed `Nat -> Nat` function via `WellFounded.fix` with family `fun _ =>
   Nat` (a `Sort` motive returning actual data, not a `Prop`), whose value
   at the immediate predecessor is USED (a countdown identity), and the
   test asserts it computes through the recursor. This directly extends
   what CLAUDE.md's Gotchas already established for `Prop`-valued
   `WellFounded.fix` uses (`gcd`, `bezout_witnesses`, `modeq`, `wilson`,
   `F:ml430-nat-base-induction`): the primitive is not restricted to
   propositions.
4. **Even granting (2) and (3), `Nat.fib` itself is ALSO a divergent
   construction.** `nat_prelude/fibonacci.rs`'s own module doc: `Nat.fib`
   is built via a CURRIED-ACCUMULATOR fuel recursion (`fibAux i a b`, `fib n
   := fibAux n 0 1`) specifically because this kernel has no tuple type —
   not Mathlib's own two-step `Nat.rec`/well-founded recurrence. This is
   independent of the `binaryRec` question entirely.

## Decision

**A flip requires every constituent construction in the statement's
dependency chain to match Mathlib's `def`, not merely the outermost
combinator.** `Nat.fastFib_eq`'s statement mentions `fastFib` (which
unfolds through `binaryRec`) AND `Nat.fib` (a second, independently
divergent construction). Building a true well-founded `binaryRec` — now
confirmed feasible per (3) — would remove ONE of two obstructions and still
leave the mirror unflippable, because `fib`'s curried-accumulator recursion
does not match Mathlib's `fib` either. This generalizes the existing
`Nat.multichoose`/`Nat.minFac` mirror-flip criterion (CLAUDE.md's "WHEN IS
FLIPPING AN `ml430` MIRROR HONEST" gotcha) from a single construction to a
COMPOSED statement: check every named function's construction against the
pinned source, not just the head symbol's.

`F:ml430-nat-fastfib-eq-cde11774` stays `open`. Per the established
pattern for `Nat.testBit`/`Nat.multichoose`/`Nat.minFac`
(`F:nat-lt-of-testbit`, `F:nat-testbit-xor`, `F:nat-testbit-land`,
`F:nat-testbit-lor`, `F:nat-multichoose-one`, `F:nat-coprime-of-lt-minfac`),
the honest path is a NEW local fact stating the SAME extensional content
(`fastFib n = fib n`, or an equivalent closed-form correctness statement)
over our own constructions, once built — not attempted in this lane for
time reasons, but no longer correctly describable as "blocked."

**Sizing, for the next lane, corrected from `250`'s framing:** the fuel-based
`binaryRec` already in `binary_rec.rs` is SUFFICIENT to build `fastFibAux`
(its own motive is non-dependent, matching exactly what `fastFibAux` needs)
— a true well-founded `binaryRec` is NOT a prerequisite, because it buys
nothing extra here (point 4 above): the mirror cannot flip either way. The
real remaining work is: (a) define `Nat.fastFibAux := binaryRec Nat.Pair
(Nat.Pair.mk (fib 0) (fib 1)) step` with `step b _ p := if b then … else …`
mirroring Mathlib's arithmetic (needs `Nat.sub` truncation care per the
`fib_two_mul` identity noted in `250`), (b) prove `∀ n, fastFibAux n =
Nat.Pair.mk (fib n) (fib (succ n))` by STRONG induction on `n` (the
recursive call lands at `half(succ m)`, which can be much less than `m`,
so ordinary `Nat.rec` does not supply a usable IH — this needs the SAME
`WellFounded.fix`-over-`Nat.lt` device `base_induction.rs` already uses for
its `Prop`-valued strong induction, instantiated as its own wrapper since
`nat_strict_well_foundedness_drives_generic_strong_recursion`'s usage is
low-level and not yet a reusable helper), handling the `b = true`/`false`
cases via `binary_rec_succ` plus `fib_add`'s doubling identities (already
proved, see `250`'s notes). Comparable in scope to this session's
`testBit_land`/`testBit_lor` pair, plus the strong-induction wrapper.

## Consequences

- The mirror-flip criterion in CLAUDE.md should be read compositionally:
  for a statement naming two or more Mathlib constructions, each is checked
  independently at the pinned source, and ANY one divergence keeps the
  mirror open regardless of the others' status.
- `nat_strict_well_foundedness_drives_generic_strong_recursion`'s technique
  (a computing, non-Prop `WellFounded.fix`) is reusable infrastructure for
  any future genuinely well-founded (non-fuel) `Nat`-valued recursion this
  prelude needs — it should not be re-discovered as novel by a future lane
  reading only the "fuel forces non-dependence" Gotcha entry.
- Do not read "blocked on `binaryRec`" in any prior status doc as current
  without re-deriving it against the pinned Mathlib source, per the
  standing "verify a blocker still exists before treating it as one" rule
  — this is the second correction to this exact fact's sizing in two days.
