# 07 — The cost model, and the Pareto position against Mathlib

Date: 2026-08-27. Companion to [05-throughput.md](05-throughput.md) (the
construction plan) and to ADR-0601/0602/0603. This records a strategy
discussion held while ~30 lanes ran in one day, with the numbers measured in
that session. Nothing here is aspiration without a metric attached.

## 1. What "Pareto dominant to Mathlib" can honestly mean

Global dominance over a ~200k-theorem, decade-old library is not a coherent
near-term claim on the coverage axis. The claim that IS coherent, measurable,
and partly already true:

- **On every statement we ship, strictly dominate**: constructive ⟹ classical
  plus a program; trusted base 0 vs 3 axioms; every theorem executable where
  Mathlib's analysis is `noncomputable`. Machine-checkable on both sides.
- **Ship capability classes with no counterpart**: CAS answers that arrive as
  independently checkable kernel artifacts (no shipped CAS has this —
  Mathematica is an oracle; Mathlib's automation is tactic-time), and a
  self-extending library (neither incumbent competes on that axis at all).
- **Never lose on checkability**: a referee verifies our headline claims in one
  command; the validator prints the split
  `cas-certificate=N(kernel-reconstructed=…, cas-internal=…)` so second-class
  evidence can never read as first-class.
- **Concede breadth EXPLICITLY at current efficiency, and treat it as a curve
  to bend, not a wall** (see §3): labeled imports cover the gap meanwhile,
  excluded from every headline count as a stated invariant (ADR-0601 §3).

The per-theorem shape of "our Mathlib equivalent" is ADR-0603's graded
statement family — see the IVT/EVT worked example there. A topic's entry is
richer than the classical library's single row, because it also proves where
the boundary is.

## 2. Why the combination is a kind, not a gluing

The architecture exploits an asymmetry neither incumbent does: **finding is
hard, checking is cheap** — "untrusted fast search, trusted small checking" is
exactly this. Sturm search → sign-count certificate; Risch-style integration
search → differentiate-and-check; CAS normal-form search → kernel-checked
∀x identity (landed 2026-08-27, with the forgery rejected in the same test).
Mathematica does only the finding and asks for trust; Lean does only the
checking and asks a human to find. The boundaries are real and stated:
Richardson's theorem pins the certified fragment to the decidable one, and the
cost curves (§4) are the open bet.

## 3. The cost model — tokens are capex, not opex

The naive model (LLM tokens × theorems) prices this session at ~100k tokens
per kernel-verified declaration (~30 lanes, ~300k tokens each, ~90
declarations landed in a day). Mathlib-scale at that constant is ~20B tokens.
That model is WRONG for this architecture, in three measured ways:

1. **Encoded strategies drive marginal cost to CPU.** `ring_law_proof` emits
   kernel proof terms for ring identities mechanically — every such identity
   is now ~0 tokens forever. Farkas/SOS/DRAT/Sturm strata are already
   CPU-priced. The producer-contract registry (ADR-0602) is the mechanism for
   making this the norm rather than the exception.
2. **Templates compound.** `alternatingBracket` was proved over an ABSTRACT
   magnitude; `cosOne`'s bounds cost five lanes of discovery, `sinOne`'s cost
   one lane of instantiation. Same for `weierstrassMTest` (every power series
   now gets uniform convergence by instantiation) and `sumRangeRatioTest`.
   Marginal cost per theorem FALLS as the library grows, and this session
   measured it happening.
3. **The residual LLM role is the frontier**: designing new producers,
   selecting statements, repairing. Most of a Mathlib-scale library by count
   is lemma-farming in mechanizable strata.

Corrected model: **cost per theorem = amortized producer construction + CPU
per instance + LLM attention only at the frontier.** Under it, low tens of
thousands of dollars for Mathlib-scale coverage of the mechanizable strata is
an engineering target, not a fantasy; the novel-construction tail stays
LLM-priced.

**The known token sink to mechanize next**: setoid congruence. `CReal` is a
Bishop setoid, so every function must be PROVED to respect `Equiv`; lanes
hand-assembled `mul_congr ∘ pow_congr` obligations all session, and the
M-test carries the congruence hypothesis explicitly because arbitrary terms
need not respect it. Deriving Equiv-respect for any composite of registered
congruent operations is pure structural recursion — a producer, waiting to be
written (`IntDev::congr` is the single-hole case).

## 4. The three gates, each with a running measurement

1. **Contracts replace hand-written briefs** (ADR-0602). Today's cost per
   theorem includes a coordinator writing ~3,000-word briefs encoding ~20
   gotchas; that is the expensive input. Metric: `fact-frontier.py --json`
   `admissible` count (was 0; the jam's cause is doc 288: operations are
   receipts, not producers).
2. **Retrieval kills re-derivation.** Seven times in one day a lane's blocker
   already existed — filed under its first consumer's module, built INLINE and
   unnamed inside a larger declaration, or stated with a weaker hypothesis
   than assumed (CLAUDE.md's three-hiding-places entry). Every instance is
   pure waste at scale. "Grep for the STEP, not the name" must become
   machinery, not habit.
3. **Sharding kills coordination serialization.** One pinned inventory in
   `creal_tests.rs` made every pair of creal lanes conflict: 8+ pin incidents
   in one day, including the zero-conflict merge trap and four mid-item hunk
   cuts. C1 in [05-throughput.md](05-throughput.md); implementation in
   flight. Metric: cross-lane conflict rate on inventory files.

Falsifiability: if the bridge/RealAlgebraic cost curves come back
super-polynomial and large, the certified-CAS half is a research artifact,
not a Mathematica successor — measured, either way. The bridge's first
datum: ~8.5 s incremental for a degree-2 ∀x identity (vs ~1 s for a concrete
point); one degree-2 concrete `infer` elsewhere cost ~356 s. Scale past
degree 2 is deliberately unmeasured rather than guessed.
