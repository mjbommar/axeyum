# 07 — The cost model, and the Pareto position against Mathlib

Date: 2026-08-27. Companion to [05-throughput.md](05-throughput.md) (the
construction plan) and to ADR-0601/0602/0603. This records a strategy
discussion held while ~30 lanes ran in one day, with the numbers measured in
that session. Nothing here is aspiration without a metric attached.

**Re-measurement, 2026-08-31 (lane `pareto-position`, see
[ADR-1165](../research/09-decisions/adr-1165-the-cost-model-re-measured-two-gates-moved-one-stayed-flat.md)).**
Every number below was re-checked against this session's tree rather than
inherited. **The document holds up in substance** — the strategy framing in
§1-2 is unchanged and every named example in §3's "templates compound" item
still exists in the tree. Three things moved since 2026-08-27 and are
corrected in place below, each in a dated block: the setoid-congruence
"producer, waiting to be written" (§3) has been **built**, with one production
consumer; the sharding gate (§4.3) is **closed** for the specific mechanism
named (`creal_tests.rs`'s single pinned array no longer exists); the retrieval
gate (§4.2) got real machinery (`shape_search`, ADR-0608) but **is not yet
closed** — a follow-up measurement found the machinery is used at brief time
4.8% of the time against 272 lane status docs, and the underlying problem
(a lane re-deriving something that already exists) kept recurring after the
tool landed. The contracts gate (§4.1) is **unchanged**: still 0 admissible
against a now-larger ready set, and the registry now holds exactly two
producer contracts, matching exactly one of 170 ready facts — and declining
that one.

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

**Re-verified 2026-08-31**: as of that date the worked example
([08-ivt-and-evt-measured-against-mathlib.md](08-ivt-and-evt-measured-against-mathlib.md))
has all four ADR-0603 rows populated with evidence for both theorems, for the
first time (row 4, labeled import, landed 2026-08-31, ADR-1090). Read the
verdict precisely: IVT is Pareto-positioned under the test in §1 above; EVT is
not, for a bookkeeping reason (no fact had named its row-1 supremum theorem)
rather than a structural one. And a full four-row table is *not* dominance on
its own — `CReal.evt_approx_max` is an **approximate** max (for every `n`, a
point within `1/(n+1)` of the bound), not the classical attaining maximiser.
There is still no positive constructive substitute for that. Doc 08 states
this explicitly; this document never claimed otherwise, and this note exists
so it stays that way.

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

   **Second datum, and the first on the TACTIC layer** (2026-09-03,
   [ADR-1576](../research/09-decisions/adr-1576-a-tactic-is-a-producer-and-its-return-is-measured-in-retired-proofs.md)):
   `crate::linarith` decides quantifier-free linear arithmetic over ℕ and ℤ and
   emits the kernel term. Measured `--release`, **0.5 to 15 ms per term end to
   end**, kernel recheck included — and the recheck is the *minority* of that,
   10–45%; the emitter's own normalizer is the expensive half. It retired
   fifteen hand-written proofs the day it landed.

   That entry also exposes a hole in how this section measures. A producer
   whose return is RETIREMENT of existing proofs scores **zero** on the
   producer-contract system, which sizes dispatch:
   `linear-arithmetic-v1` is born retired against an empty live population,
   because linear arithmetic is the part of this development that was finished
   FIRST, by hand. "Marginal cost per theorem" prices theorems the library does
   not have yet; it says nothing about proofs the library stops writing. Both
   are real returns and only one of them is currently counted.
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

~~**The known token sink to mechanize next**: setoid congruence. `CReal` is a
Bishop setoid, so every function must be PROVED to respect `Equiv`; lanes
hand-assembled `mul_congr ∘ pow_congr` obligations all session, and the
M-test carries the congruence hypothesis explicitly because arbitrary terms
need not respect it. Deriving Equiv-respect for any composite of registered
congruent operations is pure structural recursion — a producer, waiting to be
written (`IntDev::congr` is the single-hole case).~~

**Correction, 2026-08-31: built, the same day this document was written.**
`crates/axeyum-lean-kernel/src/creal/congruence.rs` landed 2026-08-27
(`cb8b54e20`, [status](../plan/status/136-congruence-deriver.md)): a registry
of six base congruence lemmas, a `CongruExpr` term representation the deriver
can inspect without running it, and `derive`/`declare_derived_congr` — pure
structural recursion producing `(statement, proof)` or a typed decline, never
a panic. Its deepest kernel-checked demo (five registered-op nodes) costs
**7.62 ms** derive+check. One permanent production consumer landed with it,
`CReal.mulPowCongr` (the power-series term congruence,
`declare_congruence_extras` in the prelude's dispatch chain) — the mechanism
is real, not a demo-only exercise. **Nothing existing was retired**: every
CURRENT hand-built congruence (`neg_congr`, `add_congr`, `mul_congr`,
`min_congr`/`max_congr`/`abs_congr`, `pow_congr`, `sum_range_congr`) is a BASE
case the registry itself depends on, so deriving them through the deriver
would be circular — the token-sink reduction is prospective, for future
COMPOSITE congruences, not retrospective.

## 4. The three gates, each with a running measurement

1. **Contracts replace hand-written briefs** (ADR-0602). Today's cost per
   theorem includes a coordinator writing ~3,000-word briefs encoding ~20
   gotchas; that is the expensive input. Metric: `fact-frontier.py --json`
   `admissible` count (was 0; the jam's cause is doc 288: operations are
   receipts, not producers).

   **Re-measured 2026-08-31: still 0, and now precisely characterized.**
   `python3 scripts/fact-frontier.py --json` reports 170 `ready_fact_ids`, 0
   `admissible_fact_ids`, 1 declined. The producer-contract registry
   (`artifacts/autogenesis/producer-contracts/`) holds exactly **two**
   contracts (`nat-coprime-family-v1`, `int-modeq-family-v1`). Across all 170
   ready facts, exactly **one** (`F:ml430-nat-coprime-of-lt-minfac-0f79bdba`)
   matches either contract — and that match is itself declined
   (`declined-via-contract`). So the mechanism ADR-0602 describes exists and
   is wired into the frontier's own selection logic, but it has not yet
   started closing the gap it names: 169 of 170 ready facts are rejected for
   `no-registered-operation` / `no-matched-producer-contract` before a
   contract is even consulted.
2. **Retrieval kills re-derivation.** Seven times in one day a lane's blocker
   already existed — filed under its first consumer's module, built INLINE and
   unnamed inside a larger declaration, or stated with a weaker hypothesis
   than assumed (CLAUDE.md's three-hiding-places entry). Every instance is
   pure waste at scale. "Grep for the STEP, not the name" must become
   machinery, not habit.

   **Re-measured 2026-08-31: the machinery got built; the gate is not
   closed.** ADR-0608 (2026-08-27, same day as this document) audited the
   count up to **seventeen** distinct instances and shipped `shape_search`, a
   shape-indexed retrieval tool over every declaration kind in
   `kernel.environment()` — the "must become machinery, not habit" ask,
   delivered. It is now wired into `check.sh`/the justfile
   (`scripts/check-shape-duplicates.py`, gating on 10 adjudicated duplicate
   groups, unchanged since 2026-08-27 — no new accidental duplicate has
   landed). But CLAUDE.md's own retrospective entries record the *same
   failure mode recurring after the tool existed* — two more hiding places
   (a module-basename collision across two preludes; the same argument over a
   different aggregate in a different prelude) dated 2026-08-29 and
   2026-08-30, both found by lanes that had `shape_search` available and did
   not reach for it. `scripts/brief-step0.py` (2026-08-29,
   `b6f6d5f37`) measured why directly, over 272 lane status documents:
   mutation testing, which has both a harness *and* a gate, is followed 46%
   of the time; `shape_search`, which as of 2026-08-27 had only prose behind
   it, was used **4.8%** of the time. Its own fix is to stop asking the lane
   and run the check in the dispatcher instead, before the brief is written —
   moving retrieval from something a lane is told to do to something it is
   handed already done. Too new to have its own before/after instance count.
3. **Sharding kills coordination serialization.** One pinned inventory in
   `creal_tests.rs` made every pair of creal lanes conflict: 8+ pin incidents
   in one day, including the zero-conflict merge trap and four mid-item hunk
   cuts. C1 in [05-throughput.md](05-throughput.md); implementation in
   flight. Metric: cross-lane conflict rate on inventory files.

   **Re-measured 2026-08-31: closed, for the specific mechanism named.**
   `creal_tests.rs`'s single 432-entry pinned array no longer exists. It was
   replaced by one plain `Vec` per `creal/` source module — 46 files today
   under `crates/axeyum-lean-kernel/src/creal/inventory/` — registered from
   `creal/inventory.rs`, so a lane adding one declaration to an existing
   module edits exactly that module's shard, never a file every other
   `creal` lane also edits. No shard carries a length pin (which answered
   "is this list internally consistent," never "is it complete"); coverage is
   instead checked directly against `kernel.environment()`
   (`every_creal_declaration_is_checked_and_axiom_free`, still present),
   both directions, plus a check the single-array shape could never express:
   no declaration claimed by more than one shard. No separate cross-lane
   conflict-rate tracking document exists to quote a before/after number
   from, but the specific collision mechanism this bullet names — every pair
   of `creal` lanes touching one shared file regardless of which
   declarations they added — is structurally gone.

Falsifiability: if the bridge/RealAlgebraic cost curves come back
super-polynomial and large, the certified-CAS half is a research artifact,
not a Mathematica successor — measured, either way. The bridge's first
datum: ~8.5 s incremental for a degree-2 ∀x identity (vs ~1 s for a concrete
point); one degree-2 concrete `infer` elsewhere cost ~356 s. Scale past
degree 2 is deliberately unmeasured rather than guessed.

**Not independently re-run, 2026-08-31.** The three numbers above could not
be traced to a specific committed benchmark or test this lane could re-execute
in bounded time, so they are reported as of 2026-08-27, unverified rather
than re-confirmed. Scale past degree 2 is *still* unmeasured for this exact
axis (a universally-quantified `∀x` polynomial identity through kernel
reconstruction) as of 2026-08-31 — that stays an open falsifiability bet, not
a stale claim. A related but different cost curve — Sturm-isolation cost for
the row-3 EVT decidable fragment (concrete argmax, not a `∀x` identity) — was
separately measured up to degree 22-24
([status](../plan/status/138-cas-extremum.md)): 16 ms-13.7 s for
sparse-critical-point polynomials, ~24 s for a degree-6 "thick"
(every-coefficient-nonzero) polynomial, declining soundly rather than
exploding either way. That is evidence the surrounding CAS machinery scales
gracefully on a nearby axis; it is not a substitute for the specific
`∀x`-identity datum this paragraph is about.

**Cross-check, 2026-08-31, read from the kernel and the validator rather than
from this document's prose (`python3 scripts/validate-facts.py`,
`python3 scripts/gen-lean-axiom-ledger.py --check`):**

```
routes: cas-certificate=46(kernel-reconstructed=14,cas-internal=32)
        imported-kernel-lean=7 kernel-lean=2122 search-certificate=12
        smt-clausal=10 smt-term-level=17
LEAN_AXIOM_LEDGER|total=30|axreal=30|complex=0|cpoint=0|creal=0|integer=0
        |logic=0|nat=0|rat=0|string=0|retired=35|axiom_free=8
```

Confirms §1's "quote the pair" instruction still describes real numbers: the
prelude axiom ledger is unchanged in shape (30, all in `axreal`, every other
prelude 0) even though every other count in this document moved. One caveat
the validator itself now discloses and worth carrying alongside the
`cas-certificate` split: 1 of the 14 `kernel-reconstructed` rows is
**non-discriminating** (the kernel obligation it checks holds of every
polynomial in place of the certificate's, not just the produced one) — do not
quote 14 as fourteen certificates each carrying independent geometric
content.
