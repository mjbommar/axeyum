# ADR-2141: A property test's box must reach the counterexample class — and no generator hands out a raw LCG state

Status: proposed
Index-summary: The ADR-2134 `sign_at` incident generalized. An audit of every
box-sampling property test and differential fuzz in six crates (599 rows,
measured by running replicas of the generators for their configured seeds)
found that 328 rows cannot reach a known class of counterexample to the
property's negation. Most of them share ONE mechanism, not a small box: every
hand-rolled fuzz generator is the MMIX LCG and most returned the raw state, so
`flip()`, `below(2)`, `below(4)` at a fixed draw offset are constants — the
P0 fuzz's div-by-zero corner was asserted in one polarity for all 80 of its
seeds, 0 of 600 quantified-BV bodies mentioned a bound variable, `mod` was
never emitted by the NIA fuzz, and the production faithfulness sampler gave
every symbol a low bit of 0 on every sample at every seed. Decision: a
generator's output is mixed, never raw (a gate pins the remaining sites and
the count can only fall); every box-sampling test carries a reachability probe
that CONSUMES the generator and asserts the class is present in the configured
run; a probe is registered as a mutation control whose revert kills exactly
it.
Index-status: proposed

## Context

ADR-2134 found a wrong sign in `RealAlgebraic::sign_at` behind a green
property test: the test's coefficient box (`c0, c1 ∈ −5..=5`, `c2 ∈ −3..=3`)
had no integer solution for the shape that exposed the defect. Improvement-list
item 5 (2026-09-16) asked whether that was one test or a pattern.

The audit (`bench-results/proptest-box-audit-20260916/`) enumerated every
test in `axeyum-ir`, `axeyum-arith`, `axeyum-bv`, `axeyum-cas`, `axeyum-cnf`
and `axeyum-solver` that samples inputs from a box — hand-rolled LCG loops,
exhaustive literal-range sweeps, fixed seed lists; there is no `proptest!` or
`quickcheck` in these crates — and for each row named one concrete input of
the class of counterexample the property's negation needs, then asked whether
the box can generate it. Where the answer was not a direct read of a branch,
the generator was replicated (the LCG is `u64` wrapping arithmetic) and run
for its configured seed range and instance count, and the class was counted.

**599 rows. 244 reachable, 328 not, 27 not applicable.**

### The mechanism behind the bulk of the 328

Every fuzz generator in the six crates is the same generator:
`state ← state · 6364136223846793005 + 1442695040888963407 (mod 2^64)`, and
81 files returned the state itself from `next_u64` (or its closure or
free-function equivalent). Bit `k` of an LCG modulo `2^64` with odd multiplier
and odd increment has period `2^(k+1)`. So:

* `state & 1` and `below(2)` strictly alternate on every draw;
* two consecutive `below(2)` draws are anti-correlated with certainty;
* `below(4)` cycles with period 4, `below(8)` with period 8
  (`[1,4,3,6,5,0,7,2]`);
* any binary decision at a fixed draw offset from the seed is a fixed function
  of the seed's parity — and when the seeds of a corner are congruent modulo an
  even number, it is the SAME value for every one of them.

Measured consequences (each a class the fuzz's doc comment claimed):

| generator | what could never happen | measured |
| --- | --- | --- |
| `qf_lia_differential_fuzz` | the SATISFIABLE `(div p 0) = c` shape (the a946f925 defect's own shape); `DivZeroCongruence`'s "companion sat pair"; `ExtremeConstant`'s `i64::MIN`/`i32` arms; `StrictTightening` in the positive or `>` form | `neg == true` 80/80 seeds; `a ≠ b` 80/80; `i64::MAX` arm 80/80 |
| `quantified_bv_differential_fuzz` | a body that depends on a bound variable; the `NotForall` polarity shape | 0/600 bodies; 0/400 shapes |
| `nia_differential_fuzz` | `mod`; a negative divisor | 0/2500 each (`div`, positive: 692) |
| `qf_uf_differential_fuzz` | `x = y` between variables; `f(f(x))`; any congruence pair | four atom shapes in the whole sweep |
| `qf_dt_differential_fuzz` | a positive `v0 = v1`; a negated tester | 0/1500 each |
| `abv_differential_fuzz` | a select over a nested store | 0/2500 |
| `vivify` (5 tests), `cdclt.rs`, `cdclt_{lia,lra}_online` | a clause with both polarities | 0 of 2800+, 0/7019, 0/3488 |
| `gf2.rs` reason-subset fuzz | two distinct rows in one system | 3 distinct systems in 4000 iterations |
| `wide.rs` (3 tests) | any pair but one at widths 1 and 2 | `(0,0)` 200/200; `(2,0)` 200/200 |
| `check_qf_bv_faithfulness` (PRODUCTION) | a symbol with low bit 1; a zero divisor at width 6 | never, at every seed |

The last row is the one that changes the category of the finding: the
faithfulness sampler is not a test, it is an evidence producer whose seed is
part of its certificate, and it structurally could not see a lowering defect
confined to bit 0.

### What the rest of the 328 are

Structural box gaps of the ADR-2134 kind, each recorded with its excluding
literal: width lists that stop at 8 (so `w = 128` overflow classes are
unreachable), divisor magnitudes drawn from `2..=4` (never 0), monomial factor
caps of 2 (never a cube), string alphabets of `{a, b}` (never a `\u{…}`
escape or a code point above `0xFF`, the class CLAUDE.md's hard rule names),
all-UNSAT instance lists (a wrong-UNSAT is unobservable), a positive literal
planted in every clause (all-true satisfies everything), and solver-produced
DRAT proofs that are RUP-only (every RAT path in every checker is exercised by
hand examples alone).

## Decision

1. **No generator hands out a raw LCG state.** The state update stays (seeds
   remain seeds); the OUTPUT passes through SplitMix64's finalizer, so every
   output bit depends on the whole state. `scripts/check-lcg-raw-state.py`
   pins the remaining sites in `scripts/lcg-raw-state-baseline.txt` with their
   counts; a new site fails, a grown count fails, and a stale entry fails (the
   number ratchets down honestly). It runs in the pre-push L0 block,
   `check.sh` and `just check`, and its five guards are mutation controls that
   each kill exactly one test.

2. **Every box-sampling test carries a reachability probe.** A
   `the_generator_reaches_<class>` test regenerates the configured population
   by CALLING the fuzz's own generator (a probe over a replica stays green
   while the shipped generator regresses — the faithfulness probe was first
   written that way and rewritten), counts the previously-dead classes, and
   asserts a floor the old generator fails. The probe calls no solver, so it
   runs in every feature configuration.

3. **A probe is registered as a mutation control.** Reverting the generator
   fix (the finalizer) must kill exactly the probe. Where a natural subject
   mutant exists that only the reached class can observe, it is registered
   too (the bit-0 carry defect in the adder; `bvsdiv` by zero of a negative
   dividend).

4. **Widening a structural box is a separate, per-row decision**, recorded in
   the inventory and not made silently in this pass. The seed-class rule
   already in CLAUDE.md (an underspecified operator's degenerate argument is
   emitted deliberately) is the mechanism; `wide.rs` shows the shape
   (`degenerate_pairs` ahead of the random draws in every width). One such
   class found a defect in a test's own REFERENCE (`sb.abs()` at `i128::MIN`),
   which is the point: a class that was never formed was never checked on
   either side.

## Consequences

* Every fuzz population that was fixed CHANGED. The suites were re-run against
  their oracles after the change (the status file records which, with counts
  and wall times) and no verdict disagreement appeared — but that is the
  measured statement, not a theorem, and it is the reason each re-run is
  listed by name.
* The pinned `disagree_zero` gates now cover the classes they were documented
  as covering. A doc comment that lists an operator the generator cannot emit
  is now detectable by its probe.
* A fuzz whose seeds are congruent modulo an even number (`seed % 12` corner
  scheduling) was the worst case, because parity was constant across the whole
  corner. Mixing the output removes the dependence; the scheduling can stay.
* The checker recognises the tail-return shape (struct method, closure, free
  function). A generator that returns `state >> 33` is not flagged — its low
  bits are period `2^34`, adequate for these run lengths — and one that mixes
  is not flagged. The gate is a ratchet on the idiom, not a proof of
  randomness.

## Alternatives rejected

* **Widen every box.** Most of the 328 rows are one mechanism; fixing the
  mechanism is one line per file and fixes them together. Box widening is
  per-row work with its own cost (slower suites) and is left as recorded
  decisions.
* **Replace the LCG with a library PRNG.** A dependency for what is one
  finalizer, and the seeds in committed expectations would change. The
  finalizer keeps the seeds.
* **Only document the idiom.** Prose did not stop the 81st copy. A gate whose
  exit status depends on the count did.

## Evidence

* `bench-results/proptest-box-audit-20260916/inventory.tsv` — the 599 rows;
  `README.md` beside it — the counts, the controls, the mutants.
* `scripts/tests/mutation_controls.py` — suites `proptest-box-*` and
  `lcg-raw-state`.
* `docs/plan/status/ax-proptest.md` — which suites were re-run, with counts.
