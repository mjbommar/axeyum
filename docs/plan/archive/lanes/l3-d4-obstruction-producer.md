# Status: L3 D4 obstruction-to-producer compiler

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, l3-d4-obstruction-producer, 2026-08-30).** See
the detail below.

**Track:** L3 definition-discovery-efficiency-roadmap — phase D4
**Phase:** compiler built, two producer contracts compiled and mutation-tested; gate registered
**Date:** 2026-08-30

## Summary

## What landed

- `scripts/gen-obstruction-producers.py` — the compiler. Classifies every
  open obstruction it can find primary-source evidence for into
  `producer` / `new-construction` / `not-removable` (ADR-0602), and
  compiles a falsifiable producer contract ONLY for the `producer` class.
  `--check` re-derives everything from the fact ledger, the mirror-
  divergence registry, and `nat_prelude/` source on every run and fails on
  drift.
- `scripts/check-obstruction-producers.py` — the gate (G1-G10): freshness,
  nonempty classification, at least one live plural producer, no `proved`
  field anywhere (recursive scan), applicability nonempty, plurality
  enforced per-contract (kind=producer needs >= 2 targets or must be
  `capsule`), targets exist and are `open`, negative controls present and
  real, obstruction schema + evidence for `not-removable` claims,
  applicability bounded by its own obstruction's population.
- `artifacts/obstruction-producers/obstructions.json` — 7 obstruction
  records: `nat-testbit-bool-codomain` (new-construction, 5 facts),
  `nat-testbit-list-bool-getI` (not-removable, 1 fact),
  `nat-multichoose-definitional-divergence` (not-removable, 3 facts),
  `nat-minfac-algorithmic-divergence` (not-removable, 1 fact),
  `nat-fastfib-recursion-principle` (not-removable, 1 fact, corrected
  mid-session per ADR-0840), `nat-bitwise-cross-operator-proof-gap`
  (producer, 2 facts), `nat-bitwise-extensional-duplicate` (producer,
  3 facts).
- `artifacts/obstruction-producers/producers/extensional-duplicate-close.json`
  and `.../pointwise-bit-extensionality.json` — the two compiled producer
  contracts. Applicability sizes 3 and 2, mean 2.5.
- `scripts/tests/test-obstruction-producers.sh` — 13 cases, one per guard
  (plus co-firing consequences), mutation-verified by hand (see commit
  `12e77ee91`'s kill table).
- `docs/research/09-decisions/adr-0920-obstruction-to-producer-compiler-classifies-before-it-compiles.md`.
- Gate registered in `justfile` (`check:` recipe) and `scripts/check.sh`
  (additive lines only).

## Corrections made mid-session (kept in the compiler's own comments)

- `Nat.minFac`'s coprime mirror looked like a fourth
  `extensional-duplicate-close` target (same predicate symbols as an
  already-proved native analogue) and is explicitly excluded: both
  `nat_prelude/min_fac.rs`'s module doc and the native fact's own `notes`
  field say flipping it would not be honest. Kept as a denylist entry and
  a negative control.
- `nat-fastfib-recursion-principle` was drafted as `new-construction`
  (needs a well-founded `binaryRec`), then corrected to `not-removable`
  after CLAUDE.md's Gotchas surfaced ADR-0840 mid-session: Mathlib's
  `fastFibAux` only needs a non-dependent motive (the fuel `binaryRec`
  already here suffices), and the real, un-removable blocker is that
  `Nat.fib` itself independently diverges from Mathlib's recurrence.
  Independently re-verified by reading `fibonacci.rs` before writing the
  correction back into the classifier. Commit `66bf497f4`.

## Absence checks

`python3 scripts/check-autogenesis-holdout-isolation.py` before and after:
`held_out=136, files_scanned=1110, references=0, verdict=PASS` both times
-- unchanged, no held-out contamination introduced.

## What was refused

A producer for `Nat.testBit`'s Bool-codomain mirrors and for `Nat.fastFib`
was refused: both are real capability gaps but not yet buildable
(`Nat.testBitBool` and a reconciled `fastFib`/`fib` pair don't exist), so
no producer is evaluable today. Compiling one anyway would have been
exactly ADR-0602's dispatch-table failure mode. `Nat.multichoose` (3
facts) and `Nat.minFac`'s remaining mirror were refused outright: both are
documented, in-tree, as different propositions from Mathlib's.

## Next steps for a future lane

- Once `Nat.testBitBool` (Bool-valued codomain) is built, re-run the
  compiler to check whether a producer becomes evaluable for the 5
  remaining `Nat.testBit` mirrors.
- Once a reconciled `fastFib`/`Nat.fib` pair exists as new local facts
  (per ADR-0840's sizing), re-run to check the same for `fastFib`.
- The `extensional-duplicate-close` shape (restate via an already-proved
  twin or bare declaration) likely generalizes beyond the `land` family
  once other prelude modules are scanned the same way; not attempted here
  for scope.
