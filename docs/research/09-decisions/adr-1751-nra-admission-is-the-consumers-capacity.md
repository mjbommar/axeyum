# ADR-1751: The NRA abstraction's admission bound is the consuming engine's capacity, not a cross-product count

Status: accepted
Index-summary: Admission for the NRA linear-abstraction route is the consuming engine's distinct-LRA-atom capacity, not a cross-product count of 2. Re-measured on the 62 QF_NRA parity files the 2026-09-06 census attributed to that count: ZERO memory aborts in 124 runs and peak RSS 3,315 vs 3,316 MiB against an 8 GiB cap, so the bound protected WALL TIME, never memory; and on 25 of the 62 it protected nothing, the abstraction being refused one layer down by `MAX_ONLINE_LRA_ATOMS` in the same time and memory. The producer metered in cross-products while the consumer meters in atoms and refuses above 1,024 — 15x apart in different units, and the ratio between them is not a constant (13.1 to 30.3 atoms per cross-product on real input), so admission counts the atoms of the system it is about to hand over rather than converting. Below the legacy line of 2 the path is byte-identical; above it the existing cheap refutations still run first and the relaxation gets half the remaining deadline, because `unknown` is a fall-through for the QF_NIA and UF+NRA callers.
Index-status: accepted
Date: 2026-09-07

## Context

`crates/axeyum-solver/src/nra.rs` refused any query with more than **2**
distinct-operand cross-products, returning `Unknown(ResourceLimit)` before
building the product lemmas. The 2026-09-06 QF_NRA loss census
(`bench-results/parity-losses-20260906/`) attributed **62 of 77** reference-only
losses (80.5%) to that refusal — the largest single named cause on the parity
board.

The bound was introduced by `9a8b09220` (2026-06-19) as an **OOM guard**. Its
commit message is the only first-hand record of what it was built to stop:

> ≥3 distinct-operand cross-products generate a dense disjunctive monotonicity +
> sum-of-squares lemma set whose DPLL(T)/exact-rational LRA relaxation blows up
> *inside a single solve call* — so the per-round / per-node wall-clock checks
> never get a turn — and bounds do NOT tame it (the bounded variant SIGABRT'd at
> the 64 GiB cap).

Two things had to be established before touching it, and both were.

**It is not a soundness bound, and this does not rest on the comment.**
Admission gates *reachability*, never correctness: the abstraction is a
relaxation, so only `unsat` transfers, and every `sat` is replayed against the
original assertions by the ground evaluator in `check_with_nra`'s outer guard.
Both arguments are independent of the count. Raising the bound cannot produce a
wrong verdict; it can only cost memory or time.

**Which of memory or time it protects was re-measured, not inherited.** One
binary, two arms differing only in an env override, the 62 census files, 24 s /
8 GiB, `taskset -c 0-7`, arms interleaved, on s6 (load 1.03 before, 2.06 after).
Full record:
[`docs/research/12-performance/nra-admission-bound-2026-09-07.md`](../12-performance/nra-admission-bound-2026-09-07.md).

- **Zero memory aborts in 124 runs.** Every run exited 0. Peak RSS across the
  whole population was **3,315 MiB** with the bound on and **3,316 MiB** with it
  lifted — 1 MiB apart, against an 8 GiB cap. The largest single-file increase
  was 967 MiB, still an eighth of the cap.
- **It protects wall time.** Lifting it cost **+502 s** over 62 files
  (583 → 1,085) and bought **2 new `sat`**, both agreeing with cvc5, with **zero
  disagreements** and zero verdict regressions.
- **On 25 of the 62 it protects nothing at all.** Those files cost no more than
  0.2 s extra with the bound lifted — no additional search happened, because the
  abstraction they produce is refused one layer down by
  `lra_theory::MAX_ONLINE_LRA_ATOMS`, in the same time and the same memory. On
  `mbo_E1.smt2` the decline message changes from "771 cross-products exceed the
  deterministic admission bound of 2" to "online CDCL(T) LRA atom cap exceeded
  (23385 > 1024)" — same 0.83 s, same 101 MB.
- The 2026-06 blowup mechanism has an independent guard now: `too_large_to_refine`
  (`REFINE_BOUND = 2^31`, `nra.rs:647`) and overflow-safe `Rational`
  (`7a323853e`), neither of which existed when the count bound was written.

So the producer was metering in **cross-products** while the consumer meters in
**distinct linear-real atoms** and refuses above 1,024 — two numbers 15× apart in
different units, with the tighter one turning away work the engine could take.

The conversion between the units is not a constant, which rules out simply
rescaling the count. Measured across four census files: 2,562 atoms at 96
cross-products (26.7×), 10,620 at 396 (26.8×), 8,356 at 638 (13.1×), 23,385 at
771 (30.3×). Any single conversion factor is wrong by up to 2.3× on real input.

## Decision

1. **Admission is decided by the consumer's capacity, measured.**
   `admission_fits_consumer` counts the distinct linear-real atoms of the system
   the relaxation is about to be handed — plus an explicit `McCormick`/SOS
   allowance for the atoms added per branch-and-bound node — and admits iff it
   fits `lra_theory::MAX_ONLINE_LRA_ATOMS`. It **counts rather than converts**,
   for the reason above. The walk is over terms that are already built: the
   sign/zero and threshold-1 lemmas are constructed on the decline path today
   regardless, so the count costs one linear pass and no construction.

2. **`LEGACY_ADMISSION_CROSS_PRODUCTS = 2` stops being a gate but stays a named
   line.** At or below it, the engine takes the identical path it always did —
   full lemma set, `McCormick` envelopes, SOS coupling, the caller's whole
   deadline. This is what makes "no file this engine decides today can change
   verdict" a *structural* argument rather than an empirical one: no such file
   is above the line.

3. **Above the line, the existing cheap refutations run first, unchanged.** The
   sign/zero and threshold-1 solves (each under `SIGN_REFUTE_BUDGET`) are what
   this engine decides today on capped queries. Running them before the heavier
   relaxation means the new policy can only turn an `unknown` into a decision,
   never the reverse — the relaxation is a *larger* system, so it could
   otherwise time out where the small one refuted quickly.

4. **A query admitted above the line gets half the remaining deadline, not all
   of it** (`RELAXATION_DEADLINE_SHARE_ABOVE_LEGACY`). `unknown` is a
   fall-through, not a terminal answer, for two callers: `int_real_relax` relaxes
   a QF_NIA query into this engine and tries other integer routes on `unknown`,
   and `dispatch_uf_nra` does the same for UF+NRA. A newly-admitted query that
   consumed the whole budget would starve routes that have that time today.
   The share is set from the measurement: the two new `sat` results were found
   4.4 s and 1.0 s into the relaxation, so half of the 24 s protocol budget
   (~11 s after the upstream routes) leaves the larger of them 2.5× headroom.
   Since such a query gets **zero** relaxation time today, any positive share is
   strictly more search than it has now.

5. **The decline message names the number the refusal was actually made on.**
   Under the capacity policy it reports the projected atom count and the
   capacity; under the hard-count lever it reports the count and the lever. This
   is not cosmetic: attributing a decline to a bound that did not decide it is
   the exact defect this lane found in the 2026-09-06 census, which put 25 files
   under a cross-product bound that was measurably not their binding constraint.

6. **`AXEYUM_NRA_ADMISSION` selects the policy in one binary** —
   `capacity` (default), `legacy`, `unbounded`, or an integer hard count. Read
   once into a `OnceLock`, because determinism is a public API promise and the
   policy must not change between two solves in one process. The atom walk is
   skipped under a hard count so the legacy arm costs what the pre-ADR engine
   cost. `scripts/parity-run.sh` records any `AXEYUM_*` lever it sees in the
   ledger entry, so a swept number cannot be mistaken for a default one.

## Alternatives considered

- **Raise the constant to a measured value.** Rejected. The measurement shows
  every threshold from 6 upward buys the *same* +2 decides while cost grows
  monotonically (+183 s at 6, +469 s at 34, +503 s unbounded), so picking a
  number from that curve is fitting a constant to two data points. It also
  leaves the producer metering in a unit the consumer does not use.
- **Scale the count by a measured atoms-per-cross-product factor.** Rejected:
  the ratio spans 13.1–30.3 on real input, so the derived count is wrong by up
  to 2.3× either way. Counting the actual atoms costs no more.
- **Lift the bound entirely.** Rejected on the fall-through argument (4): a
  QF_NIA or UF+NRA query would lose the whole budget to a relaxation that, on
  this population, decides 2 files in 62.
- **Raise `MAX_ONLINE_LRA_ATOMS` instead.** Out of scope and separately
  measured against: that cap's own doc comment records the sweep — raising it to
  16,384 changed **no** verdict on the QF_LRA parity list, cost one file 24 s it
  used to decline in 0.12 s, and made a 1,492-atom file abort at the 8 GiB cap.
  It is an atom-*normalization* budget and lifting it needs that memory
  addressed first.
- **Do nothing and route the 62 files to a real nlsat/CAD engine.** Still the
  right long-term answer for the 60 files this does not decide, and this ADR
  does not claim otherwise. But leaving a producer sized to an unmeasured
  constant 15× tighter than its consumer would keep manufacturing loss
  attributions that name the wrong bound.

## Consequences

- Easier: the two bounds now say the same thing in the same unit, so a future
  change to either is visible to the other. A loss census reading the decline
  message gets the binding constraint, not the first gate in the chain.
- Harder: the admission decision is no longer readable off a single constant.
  `AXEYUM_NRA_ADMISSION=legacy` exists so a suspected regression can be
  attributed to this ADR in one run without a rebuild.
- The corrected attribution for the QF_NRA board: of the 62 files the census
  assigned to this bound, **25** were never gated by it (lifting it changed
  their cost by ≤ 0.2 s), **35** are admitted now and still undecided by the
  relaxation, and **2** are decided. The remaining gap is a
  **capability** gap (nlsat/CAD), not an admission-policy one — which is what
  the census could not distinguish while the message named the wrong gate.
- Revisit when an nlsat/CAD engine lands: admission then sizes to *that*
  consumer, and the atom capacity stops being the relevant ceiling.
