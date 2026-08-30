# Notes: blocked-mirror-divergences

Detail moved out of [`../status/blocked-mirror-divergences.md`](../status/blocked-mirror-divergences.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

All four `ml430` testBit mirrors correctly stay `open` (Bool-vs-Nat
codomain mismatch, verified against the pinned Mathlib source at each
site). `scripts/gen-autogenesis-bitwise-family-projection.py --check`
requires `testbit_land`/`testbit_lor`/`testbit_ldiff` to stay open
regardless of provability, independent of the codomain reasoning — verified
this still applies.

Axiom footprint: both new theorems are `nat: axiom=0 opaque=0 quotient=0`,
read from `nat_axiom_inventory --require-axiom-free nat` (which measures
the whole `nat` environment, so it bounds every declaration in it,
including these two).

## `Nat.multichoose` (definitional) — 3 facts, already fully resolved

Verified against `Mathlib/Data/Nat/Choose/Basic.lean` at the pinned commit
`c5ea0035…` myself (not trusting the registry's prose): Mathlib's
`multichoose` is a genuine three-case DOUBLE recursion (`multichoose n
(k+1) + multichoose (n+1) k`), and `multichoose_eq : multichoose n k = (n +
k - 1).choose k` is a **proved theorem** about it, confirmed at the source
line. Our `Nat.multichoose n k := choose (pred (add n k)) k` DEFINES that
theorem's RHS as the body — we define what Mathlib proves, about a
structurally different `def`. Already resolved by a prior lane:
`F:nat-multichoose-one`, `F:nat-multichoose-one-right`,
`F:nat-multichoose-zero-right` are all `proved`, and the three `ml430`
mirrors correctly stay `open`. Nothing further needed; confirmed, not
re-derived.

## `Nat.minFac` (algorithmic) — 1 fact, already fully resolved

Verified against `Mathlib/Data/Nat/Prime/Defs.lean` at the pinned commit
myself: Mathlib's `minFacAux` is well-founded recursion on `sqrt n + 2 - k`,
testing only ODD candidates from 3 with an early `k*k > n` exit. Ours
(`min_fac.rs`) is fuel-structural, testing every candidate `2, 3, 4, …`
with no skip and no early exit. Same values, different construction —
confirmed by reading the actual Rust source, matching the registry's
classification exactly. Already resolved by a prior lane:
`F:nat-coprime-of-lt-minfac` is `proved`, axiom-free, and
`F:ml430-nat-coprime-of-lt-minfac-0f79bdba` correctly stays `open`. Nothing
further needed; confirmed, not re-derived.

## `Nat.fastFib` (recursion-principle) — 1 fact, sizing corrected, not built

**The prior sizing ("blocked on a well-founded `binaryRec`, which is
ordinary work") was itself stale, in a way that matters for a future
lane.** Verified in full — see **ADR-0840**
(`docs/research/09-decisions/adr-0840-…md`) for the complete derivation.
Two findings, both new:

1. Mathlib's `fastFibAux` instantiates `binaryRec` at a **non-dependent**
   motive (`fun _ => ℕ × ℕ`), confirmed by reading
   `Mathlib/Data/Nat/Fib/Basic.lean:170` at the pinned commit. So the
   FUEL-based `Nat.binaryRec` already built in `binary_rec.rs` (whose own
   non-dependence was previously read as disqualifying) is actually
   SUFFICIENT for this specific mirror — no well-founded `binaryRec` is a
   prerequisite.
2. **It would not matter if one were built anyway.** `Nat.fib` itself
   (`fibonacci.rs`) is ALSO a divergent construction (a curried-accumulator
   fuel recursion, built because this kernel has no tuple type) — a second,
   independent obstruction Mathlib's own construction chain carries.
   `Nat.fastFib_eq`'s statement names both `fastFib` and `fib`, and a flip
   needs BOTH constructions to match Mathlib's, not just the outermost
   combinator. This mirror cannot flip regardless of `binaryRec`'s
   construction. Also confirmed: the kernel already has a genuinely
   computing, DATA-motive `WellFounded.fix`
   (`nat_strict_well_foundedness_drives_generic_strong_recursion`), so a
   well-founded `binaryRec` IS buildable if ever wanted for a different
   mirror — the earlier "fuel forces non-dependence" framing does not
   generalize to "WellFounded.fix cannot produce data," and this test
   already refutes that reading.

**Not built in this lane**, for time — ADR-0840 leaves a corrected, precise
plan for the next lane (define `fastFibAux` over the EXISTING fuel
`binaryRec`, prove correctness by strong induction using
`base_induction.rs`'s `WellFounded.fix`-over-`Nat.lt` device, generalized
into a reusable wrapper; comparable in size to this session's
`testBit_land`/`testBit_lor` pair plus the wrapper). `F:ml430-nat-fastfib-eq-cde11774`
stays `open`, correctly, either way.

## Holdout isolation

Before: `AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1110|settled=0|references=0|verdict=PASS`
After: `AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1110|settled=0|references=0|verdict=PASS`
(unchanged — `artifacts/autogenesis/` was not touched, per scope).

## Verification run (this lane)

`cargo test --release -p axeyum-lean-kernel --lib nat_prelude::` — 224 -> 226
passed, 0 failed (2 new tests:
`test_bit_land_applies_at_a_concrete_discriminating_instance_and_symbolically`,
`test_bit_lor_applies_at_a_concrete_discriminating_instance_and_symbolically`).
`every_nat_declaration_is_checked_and_axiom_free`,
`the_nat_prelude_declares_no_axioms`, `the_build_is_deterministic` all still
pass. `cargo clippy -p axeyum-lean-kernel --lib -- -D warnings` clean.
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` fails on
TWO pre-existing lint errors in `tests/real_lean_replay_census.rs` and
`tests/real_lean_creal_carrier_kernel_replay.rs` — neither touched by this
lane (confirmed via `git diff --stat`), not fixed (out of scope; flagging
for whoever owns those files). `python3 scripts/validate-facts.py`: 2276
facts, 0 errors (2 new facts added; `depends_on` corrected via
`scripts/check-fact-depends-derived.py --fix` against the actual proof
term graph, not hand-guessed).

Workspace-wide gate NOT run (coordinator re-verifies per standing rule).
Not pushed.

## For the next lane

If more time goes to this area, `Nat.fastFib` is the one with real
remaining construction value (ADR-0840 has the precise plan). The
`testbit_eq_inth`/`List` gap and the `multichoose`/`minFac` divergences are
permanent — do not re-derive them; cite ADR-0840 and this file instead.
