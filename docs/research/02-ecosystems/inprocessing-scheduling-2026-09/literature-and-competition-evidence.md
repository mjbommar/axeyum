# Inprocessing techniques: literature and competition evidence

Research pass, 2026-09-08, lane `research-inproc-lit`. Read-only: this file is
the only artifact produced. Question: for vivification, BVE, subsumption
(implemented in axeyum but switched off — they cost more than they save
inside a 24 s budget) and for the techniques axeyum lacks (failed-literal
probing, congruence/equivalence sweeping, ternary resolution, blocked clause
elimination, local-search hybridization), what does the *frontier* (CaDiCaL /
Kissat lineage, SAT Competition 2020-2025, recent arXiv work) actually measure
— not assert — about cost, payoff, and DRAT-checkability?

Evidence tags: **[P]** = paper/study with a reported ablation number.
**[D]** = solver system-description or changelog, stating a design decision
without a controlled ablation table. **[I]** = my own inference/synthesis, not
sourced from a measurement.

Primary sources pulled and read in full (converted PDF → text locally, not
just search snippets):

- Fleury & Kaufmann, *Life span of SAT techniques*, POS 2023 /
  [arXiv:2402.01202](https://arxiv.org/pdf/2402.01202) — controlled ablation.
- Biere, Fazekas, Fleury, Froleyks, *Clausal Congruence Closure*, SAT 2024 —
  [PDF](https://cca.informatik.uni-freiburg.de/papers/BiereFazekasFleuryFroleyks-SAT24.pdf).
- Pollitt, Fleury, Biere, Sakallah, Heule, Chen, Fisseha, *Revisiting Clause
  Vivification*, POS 2025 —
  [PDF](https://cca.informatik.uni-freiburg.de/papers/PollittFleuryBiereSakallahHeuleChenFisseha-POS25.pdf).
- Biere, Faller, Fazekas, Fleury, Froleyks, Pollitt, *CaDiCaL, Gimsatul,
  IsaSAT and Kissat Entering the SAT Competition 2024* —
  [PDF](https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-SAT-Competition-2024-solvers.pdf).
- Biere, Faller, Fleury, Froleyks, Pollitt, *…Entering the SAT Competition
  2025* —
  [PDF](https://cca.informatik.uni-freiburg.de/papers/BiereFallerFleuryFroleyksPollitt-SAT-Competition-2025-solvers.pdf).
- Biere, Fleury, *Gimsatul, IsaSAT, Kissat Entering the SAT Competition 2022*
  — [PDF](https://cca.informatik.uni-freiburg.de/papers/BiereFleury-SAT-Competition-2022-solvers.pdf).
- `arminbiere/kissat` `NEWS.md` (changelog, sc2020→sc2026) — [raw](https://raw.githubusercontent.com/arminbiere/kissat/master/NEWS.md).
- *Backtrackable Inprocessing*, SAT 2026 /
  [arXiv:2605.03654](https://arxiv.org/html/2605.03654) — subsumption + BVE
  scheduling under incremental trails.
- *Autonomous Code Evolution Meets NP-Completeness* (SATLUTION),
  [arXiv:2509.07367](https://arxiv.org/pdf/2509.07367) — LLM-evolved solver
  beating SAT Comp 2025 winners; Table 4 has qualitative technique notes.

---

## Ranked findings (expected value to axeyum, highest first)

### 1. [P]+[D] The techniques axeyum already has (vivification, BVE, subsumption) are genuinely corpus-dependent — the fix is scheduling, not activation

This is the most load-bearing finding and directly reframes axeyum's problem.

- **[P] Fleury & Kaufmann, "Life span of SAT techniques."** A controlled
  ablation of BCE, vivification, on-the-fly self-subsumption (OTFS), and BVE
  with increased bound (BVE+) in CaDiCaL, over **every SAT Competition
  benchmark set from 2009 to 2023** (292–600 instances/year, 5000 s/instance).
  Three hypotheses tested — (i) disabling a feature is always harmful, (ii) a
  technique's usefulness has a "life span," (iii) techniques simulate each
  other — and **none of the three was confirmed.** Per-year instance counts
  swing ±10 out of ~230–560 regardless of which single feature is toggled;
  the swing from year-to-year noise is comparable to or larger than any
  single technique's measured contribution. Authors' own conclusion: *"it is
  not a good idea to single out features and test them with either being
  enabled or disabled... the features influence each other too much."*
  This is a rare, honest negative result from the team that runs the
  reference solvers — it directly undercuts the premise that any one of
  these techniques has a stable, corpus-independent ablation number worth
  chasing.

- **[P] Pollitt et al., "Revisiting Clause Vivification."** Same team,
  Kissat sc2024, controlled default-vs-no-vivify:
  - SAT Competition 2023 (400 instances, 5000 s): default solves **297**,
    no-vivify **288** (+9, ~2.3%).
  - SAT Competition 2024 (400 instances): default **325**, no-vivify **320**
    (+5, ~1.6%).
  - Their own new **750 structured factoring benchmarks**: default /
    discard-both / keep-implied all solve **750/750**; no-vivify solves
    **712/750** (−38, ~5%, and categorically worse on the hardest tail).
  Reading: on a generic competition mix, vivification is worth low
  single-digit percent — plausibly inside the noise axeyum already measured
  inside its 24 s budget. On structured/algebraic instances it is worth an
  order of magnitude more. **The payoff is not a property of the technique;
  it's a property of the corpus.** If axeyum's target corpus is closer to
  generic combinatorial SAT/QF_BV than to structured circuit/algebraic
  problems, "vivification costs more than it saves" is plausible and
  consistent with this data, not a red flag about the implementation.

- **[D] Fazekas et al., *Backtrackable Inprocessing* (SAT 2026).** Different
  angle: not "is BVE/subsumption worth it" but "when is it worth invoking."
  Built a framework (BI) for running subsumption, self-subsuming resolution,
  and BVE at *any* trail level during incremental search (Island solver, a
  fork of IntelSAT), tested on 298 HWMCC'17 BMC instances unrolled to bound
  100 (1 h timeout). A naive always-preprocess-at-level-0 baseline (BASE,
  matching what CaDiCaL does today) is beaten by an adaptive strategy (DYN)
  that switches between three scheduling policies based on a **cheap
  per-instance signal** `M = (# self-subsumptions found) / (# inprocessing
  invocations)`: low `M` → cheap assumption-level pass; medium `M` → global
  pass only; high `M` → both. Result: DYN solves **~1.5× more bounds** than
  the no-inprocessing baseline among bounds that baseline could not solve,
  and beats the static BASE strategy by **308 bounds** and static AL by
  **111 bounds** at the 1 h mark. DYN's decisions are correct on **88%** of
  the highest-stakes instances (where the static strategies disagree most).
  This is BMC/incremental, not single-shot 24 s solving, so it doesn't
  transfer directly — but the mechanism (a cheap online signal computed from
  the first N conflicts/inprocessing rounds, not an up-front corpus
  classification) is the most concrete, implementable idea in this literature
  pass for reviving axeyum's disabled techniques without eating the fixed
  cost on every instance.

**Actionable synthesis [I]:** rather than treating vivification/BVE/subsumption
as a binary on/off switch calibrated against a fixed budget, the frontier
result (both papers) says: build a cheap trigger (ticks spent so far vs.
propagations/self-subsumptions found — Kissat and CaDiCaL already compute
"ticks" as a proxy for this, see below) and gate the technique on that
signal per-instance, not globally. That is a scheduling problem, which is
exactly the framing your directory name (`inprocessing-scheduling-2026-09`)
already assumes.

### 2. [P] Congruence closure / clausal equivalence sweeping: the largest single measured win *and* the largest measured loss, plus the highest DRAT cost

**[P] Biere, Fazekas, Fleury, Froleyks, "Clausal Congruence Closure," SAT'24.**
This is Kissat's headline SAT Competition 2024 technique (3 gold medals) —
syntactic gate extraction (AND/XOR/ITE) plus a bit-level congruence-closure
algorithm, run to completion each inprocessing round, complemented by an
embedded incremental SAT solver ("Kitten") for semantic sweeping.

- On isomorphic hardware-equivalence miters (HWMCC'12, 341 instances):
  congruence closure solves them **instantly** (both encodings, 341/341);
  plain CDCL and even the previous best in-solver technique (semantic SAT
  sweeping alone) cannot compete. The state-of-the-art external circuit-level
  tool `abc -fraig` is beaten too, at least on optimized miters
  (kissat-xits-opt-default: 336/341 vs. abc: 335/341).
- On **SAT Competition 2022 main track** (400 generic instances):
  kissat-default (congruence + sweep) solves **316**, no-congruence-no-sweep
  **305**, no-congruence (sweep only) **302**. Net congruence-closure
  contribution: **+11 to +14 instances**, and it eliminated 108,272,236
  equivalent literals across the 400 benchmarks.
- On **SAT Competition 2023 main track** (400 instances, more combinatorial):
  the picture *inverts*: kissat-no-congruence solves **277**,
  kissat-default (with congruence) solves **273** — congruence closure
  **costs 4 instances net**, despite averaging only 4.41% of run time. SBVA
  (structured bounded variable addition, a different technique, see below)
  wins this set instead (287).

This is the cleanest documented case in this pass of a technique whose net
value **flips sign** depending on corpus structure — hardware/circuit-shaped
CNFs: strongly positive, sometimes categorical (unsolvable→instant); generic
combinatorial CNFs: mildly negative. It is also the most expensive to build:
requires an embedded incremental SAT sub-solver for the semantic sweeping
half, and — critically for axeyum — **the hardest of any technique here to
certify.** From the SAT Competition 2025 solver description: CaDiCaL had to
grow its codebase from 46 KLOC to 64 KLOC porting congruence closure and BVA
from Kissat, and *"a major challenge was to produce LRAT proofs with
antecedents for all the advanced inprocessing we added, particularly for
clausal congruence closure. This is in contrast to Kissat, which only
supports easier to produce, more compact but much slower to check DRUP
proofs."* Read: congruence closure is checkable, but only cheaply if you
also build LRAT-with-antecedents production; the DRUP-only fallback is
"much slower to check" (unquantified in the text, but stated as a real
engineering tradeoff CaDiCaL is willing to eat).

**[I] For axeyum:** this is the highest-ceiling, highest-cost item on the
whole list. Worth pursuing only if axeyum's target corpus profile skews
toward circuit-equivalence / hardware-miter-shaped QF_BV problems (where the
win is categorical) — not a general-purpose default given the proof
production cost and the demonstrated negative case.

### 3. [D] Failed-literal probing, hyper ternary resolution, hyper binary resolution: the frontier team tested these and cut them for low marginal value — not for being wrong

**[D] `kissat` `NEWS.md`, version `sc2022-light`.** After SAT Competition
2021, the Kissat authors explicitly ran a code-reduction pass: *"we removed
code which only gave a minor improvement on the last three SAT Competition
2019-2021 [benchmarks]. The goal was to shrink the code base in order to
concentrate on the really useful algorithms."* The removal list, verbatim:

> autarky reasoning; eager forward and backward subsumption during variable
> elimination (kept global forward subsumption only); caching/reusing
> minimum assignments during local search; **failed literal probing**;
> **hyper binary resolution**; **hyper ternary resolution**; transitive
> reduction of the binary implication graph; eager subsumption of recently
> learned clauses; **XOR gate extraction during variable elimination**;
> priority-queue-ordered variable elimination; formula-size-based delaying of
> inprocessing; trail-reuse during restarts; vivification of irredundant
> clauses; keeping untried candidates across inprocessing rounds.

This is not a paper with a delta table, but it is the frontier team's own
lived measurement, stated as a design rationale, on the actual competition
gate. Two of these were later *partially reinstated* with a specific,
narrow justification: **hyper binary resolution** came back in `sc2022-hyper`
because it *"turns out to be somewhat useful for **unsatisfiable**
formulas"* — a direct, if qualitative, confirmation of axeyum's item #3
hypothesis (techniques split in value along the SAT/UNSAT axis). Failed
literal probing and hyper ternary resolution were **not** reinstated and
remain out of Kissat's default `sc2022-light`/onward line as far as this
changelog documents.

Cost/benefit shape for the two axeyum lacks:
- **Failed-literal probing**: cost is one propagation pass per candidate
  literal (assume `l`, propagate, if conflict then `¬l` is forced). DRAT-
  friendly — the output is plain learned units and binaries, RUP-checkable,
  no extension variables, no RAT reasoning needed. Cheap to certify, cheap to
  implement, measured (by the people who removed it) as low marginal value
  on generic competition benchmarks. One search snippet independently
  described exhaustive **ternary resolution** as strengthening
  subsumption-resolution "but still weaker than vivification" — i.e., a
  proper subset of what axeyum's (currently disabled) vivification already
  buys, at extra implementation cost. Low priority for axeyum on both counts.

### 4. [P] Blocked clause elimination: the one technique with a *measured negative* result, but the cheapest to certify

**[P] "Life span of SAT techniques"** is also the best source here (BCE is
one of its four studied techniques, off by default in CaDiCaL). Direct
quote: *"BCE solves fewer instances in nearly every case"* when added on top
of CaDiCaL's base or default configuration, across the 2009–2023 sweep
(exceptions noted only for 2014, 2016, 2020). This is the most negative
documented finding among all techniques covered in this pass.

DRAT-friendliness is not in question — blocked-clause addition/removal *is*
the RAT proof rule; DRAT (Reverse-unit-propagation + RAT) was designed
specifically to express BCE natively, so certifying it costs nothing extra
beyond ordinary RAT support. But "cheap to certify" and "worth building" are
different questions, and the measured competition-level answer to the second
is negative. **[P]** general proof-complexity note (not axeyum-specific):
transforming a DRAT proof that uses RAT steps (which BCE produces) down into
a pure RUP proof can **double proof size per resolution step above a
"purifier"** — so if axeyum ever wants a RUP-only proof pipeline downstream
of a BCE-using solver, that conversion is not free, independent of solving
time. Lowest priority of the missing techniques: negative solved-instance
evidence plus a real (if narrow) proof-pipeline cost if you ever want to
downgrade RAT to RUP later.

### 5. [D]+[I] A concrete DRAT soundness landmine, independent of the ranking above

**[D] SAT Competition 2024 solver description, IsaSAT section.** Not a
technique axeyum is considering, but a sharply relevant cautionary data
point about "which techniques are DRAT-friendly": IsaSAT's authors *"deactivated
our version of pure literal elimination as it is not compatible with DRAT
(as discovered last year during the competition when proof checking
broke)."* Root cause, in their words: *"pure literal[]s redundancy is a
criteria that needs only be checked on irredundant clauses... However, DRAT
does not distinguish these sets of clauses, leading to incorrect proofs
(even if the answer is correct)."* Their workaround (learning the pure
literal as a unit clause instead of eliminating the variable) was
*"provably correct"* but only accidentally proof-checkable, because in their
test cases "these clauses were always blocked" — which is not guaranteed in
general. This is exactly the class of bug axeyum's Hard Rules section
already guards against (partial/underspecified operators, degenerate
fuzz seeds): **a technique can look correct and still be a DRAT-unsoundness
trap because DRAT's clause-redundancy bookkeeping is coarser than the
technique's own correctness argument.** Relevant if axeyum ever considers any
pure-literal-style or "clauses satisfied under current assignment" style
elimination — restrict it to demonstrably-irredundant clauses, or don't
route it through plain DRAT/DRUP without re-deriving the argument for
axeyum's own clause bookkeeping.

### 6. [D]+weak-[I] XOR/Gaussian reasoning: large but narrow, and DRAT compatibility is unresolved in what I found

CryptoMiniSat's native XOR + incremental Gauss-Jordan elimination
(integrated at every decision level, not just top-level) is reported
(solver author's own blog, not a peer-reviewed ablation table) to take
cryptanalytic instances (Trivium-style) from **"thousands of seconds"** to
**"under 20 seconds."** That's an order-of-magnitude-plus number, but it is
domain-narrow (XOR-heavy/cryptographic CNFs) and comes from the author's own
retrospective, not a controlled instances-solved table over a general
competition corpus — I could not find one. Notably, CryptoMiniSat's own
scheduling heuristic **turns Gaussian elimination off for a restart** if a
propagation/conflict-count-based trigger goes negative — i.e., even its
author treats this as a technique that needs the same kind of cheap
online gating as finding #1 above, not an always-on default. I did not find
a documented general-purpose DRAT/DRUP encoding story for Gaussian-
elimination-derived conflicts/propagations in this pass — expressing an XOR
reasoning step as CNF-level resolution is a known nontrivial translation,
and I'm flagging this as **unresolved** rather than asserting it's fine or
broken. Low priority for axeyum unless the target corpus is XOR/crypto-heavy,
and the proof-format question needs its own investigation before committing.

### 7. [I] Local search hybridization: the thinnest evidence found

No controlled ablation with solved-instance/PAR-2 deltas at competition scale
turned up in this pass. What exists: FastFourierSAT (GPU continuous local
search, 2023), a 2025 SLS+CDCL branching hybrid inside MiniSat, and — already
inside the CaDiCaL/Kissat lineage today, cited in their own SAT Comp 2022
reference list — Cai & Biere, *"Better decision heuristics in CDCL through
local search and target phases,"* JAIR 2022, which is local-search-informed
phase saving, not a full SLS/CDCL hybrid. **Honest finding: I did not find
quantitative evidence either way for a full local-search hybridization
technique axeyum doesn't already have access to via target-phase heuristics.**
This is a "we don't know" rather than a ranked recommendation; treat as
lowest priority pending axeyum's own experiment, not because the literature
says it's weak, but because the literature doesn't say anything measured at
all.

---

## SAT Competition winners 2020–2025 and what distinguished them [D]

| Year | Main-track winner | Distinguishing technique(s) |
|---|---|---|
| 2020 | Kissat-sat | first Kissat release (CaDiCaL ported to C) |
| 2021 | Kissat MAB | multi-armed-bandit restart/mode selection |
| 2022 | Kissat MAB-HyWalk | MAB + local-search-informed phases (Cai/Biere) |
| 2023 | SBVA-CaDiCaL | **structured bounded variable addition** (SBVA) as a *preprocessor* bolted onto CaDiCaL — beat Kissat's congruence closure on the 2023 (combinatorial-heavy) set specifically because SBVA and congruence closure are "orthogonal" [D, congruence-closure paper] |
| 2024 | Kissat | congruence closure (SAT'24) + clausal equivalence sweeping (FMCAD'24) + internal BVA + revisited vivification, ticks-based scheduling |
| 2025 | Kissat-based variants | same core techniques + "additional heuristic components" — the trend (per SATLUTION, arXiv:2509.07367) is now bandit/ML-tuned *scheduling* of these same techniques (vivification aggressiveness, UIP depth, restart policy) rather than new techniques |

**Trend [P/D]:** 2020–2022 was about search-side heuristics (MAB, local-search
phases). 2023–2025 is about *structural* inprocessing (BVA, congruence
closure, sweeping) plus, in the newest work, **adaptive/learned scheduling of
existing techniques** rather than new technique classes. SATLUTION (an LLM
that evolves solver source and beat the 2025 winners) reports — again,
qualitatively, not with a hard ablation table, and the authors say so
explicitly ("conducting controlled ablation studies of these learned
components remains challenging due to the highly entangled nature of their
implementations") — that its main wins came from **bandit-tuned vivification
aggressiveness split by SAT/UNSAT workload**, multi-domain bandit
coordination across vivification/restarts/UIP-depth/clause-reduction
together, and BreakID symmetry-breaking integration. This is the most direct
piece of 2025-era evidence that the frontier itself is moving toward exactly
what axeyum's `inprocessing-scheduling` lane name implies: not "should this
technique be on," but "what's the per-instance signal that decides it."

## DRAT-friendliness summary table [D, synthesized from above]

| Technique | Proof mechanism | Certification cost |
|---|---|---|
| Vivification, subsumption, self-subsuming resolution | RUP (clause shrink/delete implied by unit propagation) | Cheap; native DRAT/DRUP |
| BVE | RAT (resolvents added, eliminated variable's clauses removed) | Cheap; native DRAT, well-trodden since 2005 (Eén & Biere) |
| Failed-literal probing | Learned units/binaries via UP | Cheap; RUP |
| Blocked clause elimination | RAT (literally the rule DRAT was named for) | Cheap to certify; but general RAT→RUP proof transformation can double proof size per step [P], relevant only if axeyum wants RUP-only downstream |
| Congruence closure / equivalence sweeping / BVA | Needs LRAT-with-antecedents for fast checking; DRUP-only checking works but is reported "much slower" [D]; BVA specifically needs "some form of extended resolution" and a bespoke incremental proof calculus (Fazekas et al., POS'25, cited but not fetched in this pass) | Highest cost of anything reviewed here |
| Pure-literal elimination (not on axeyum's list, but a documented landmine) | **Unsound under plain DRAT** unless scoped to irredundant clauses — DRAT's clause bookkeeping doesn't distinguish redundant/irredundant sets [D] | N/A — don't ship this pattern without rethinking the scope |
| XOR/Gaussian reasoning | Not resolved in this pass — no documented general CNF-resolution/DRAT encoding story found | Unknown, flag for follow-up |

## What I could not find

- No quantitative ablation for ternary resolution alone (only the
  qualitative "weaker than vivification" characterization and the
  Kissat-team's removal-for-minor-improvement note).
- No general-corpus (non-cryptographic) solved-instance table for
  XOR/Gaussian reasoning.
- No solved-instance/PAR-2 ablation for any CDCL+SLS hybrid technique axeyum
  doesn't already have access to via target-phase heuristics.
- No numeric size/time cost for DRUP-only vs. LRAT-with-antecedents checking
  of congruence closure — both solver descriptions state the qualitative
  direction ("much slower to check" for DRUP) but neither publishes a number.
