# Phase 2 — evaluation harness and reward signal

Verdict from review: **needs revision.** The claim "the foundational artifacts
already ARE the reward signal" is half right and half fatal.

**This phase contains gate G1, the track's first real decision point.**

## The correction, in numbers

Verified 2026-08-01, `main` at `5dbae3a0`:

| Claimed | Actual |
|---|---|
| ~50 example packs | **174 pack directories** (`artifacts/examples/math/`) |
| — | **1,131 checks: 581 sat, 414 unsat, 136 not-run** → **995 usable labels** |
| — | 243 `.smt2` files: QF_LRA 192, QF_UF 23, QF_LIA 18, QF_BV 10 |
| — | Largest instance: **28 lines, 11 declarations**; two are ground constant formulas |
| curriculum "342-line DAG" | 342 *lines*, **23 nodes**; 16 bounded / 6 computable / 1 decidable / **0 undecidable** |
| packs are self-checking via the solver | `just foundational-resources` runs **pure Python** — a 41,696-line validator with 834 validation identifiers. **The Rust solver is never invoked by that gate.** Only ~a dozen pack instances reach real bit-blast+DRAT (`tests/math_resource_{bv,lia,lra,uf}_routes.rs`) |

**What the artifacts genuinely provide:** high-quality ground truth with an
explicit trust lattice (replay-only < checked-evidence < lean-horizon), validated
by machinery independent-in-kind from the solver. Sat rows carry witnesses
re-verified by exact-arithmetic replay; unsat rows carry exhaustive enumeration or
Farkas/Alethe/DRAT evidence. Label quality is strong and rarer than critics assume.

**What they do not provide:** difficulty gradient. Every instance decides in
milliseconds. A policy trained on them receives zero discriminative reward.
**"No signal" is the default outcome, not a tail risk.**

## Where the difficulty actually lives

The graded signal exists in the repo — elsewhere:

- **`crates/axeyum-solver/tests/progress_frontier.rs`** (1,264 lines) is the
  closest existing thing to the proposed harness: five parametric families with a
  difficulty knob `N` (`bv_reduction` baseline 30, `lia_cuts` 26, `string_bound`
  8, `nra_degree` 40, `nia_unsat` 40; `BUDGET` 4 s, `MAX_N` 40), frontier =
  largest self-check-confirmed decided `N`, decided-but-wrong is a hard failure,
  ratchet asserts `frontier >= BASELINE`. Caveat for reuse: the ratchet is
  **hardware-relative** — CI skips enforcement below baseline.
- **`crates/axeyum-scenarios`** (30 modules, 7,708 lines) — generators taking
  width/round parameters, so difficulty is *scalable*. SAT by concrete execution
  with the witness in `Expectation::Sat`, UNSAT by bounded-verified identity.
- **Public corpora + `axeyum-bench`** — `corpus/regression` 140, `corpus/qfbv-curated`
  43, `corpus/public` 903 (gitignored), ~40+ committed Z3-comparison baselines at
  1 s/3 s/10 s/20 s. SMT-COMP tooling already exists
  (`scripts/acquire-smtcomp-selection-corpus.py` and siblings).

Revised thesis: **labels and trust classes from the packs; difficulty from the
parametric generators and public corpora; measurement from `axeyum-bench`.**

## G1 — the VBS–SBS gate

Compute virtual-best-route vs single-best-route PAR-2 on the assembled eval set.
**If the ratio is below ~1.1 on decidable instances, there is no
algorithm-selection signal and phase 3 is moot** regardless of infrastructure
quality. Cheap to measure. It runs before anything expensive.

## Feature space

Computed post-parse on the `TermArena`; every feature a stable integer/rational;
no hash-map iteration (Hard Rule). Three tiers, with feature-computation cost
recorded (ASlib requires this):

1. **Static census (µs–ms)** — atlas fragment id; symbol counts per sort; BV width
   histogram; assertion count; DAG node count and depth; sharing ratio; op
   histogram keyed to atlas operator lists; hard-op counters (`bvmul`/`bvudiv`/
   `bvsdiv` count and max width, nonlinear-multiplication count); quantifier count
   and alternation depth; equality/`distinct`/`ite` density.
2. **Rewrite delta (ms)** — node count before/after `canonicalize_terms` +
   `propagate_values`; fraction folded to constants; `elim_unconstrained` removals.
3. **Bounded probing** — partial lowering under existing node/CNF budgets →
   estimated AIG nodes and CNF vars/clauses; a probe SAT call bounded by
   **conflict count, not wall clock** (determinism). SATzilla probing features,
   made deterministic.

**Explicitly excluded from the policy input:** pack/curriculum provenance
(`field_ids`, `family`, `decidability`). Those are split keys and stratification
labels. Using them as features guarantees leakage on generated variants and is
undefined on external instances.

## Reward

Reward is a **lexicographic vector**, not a scalar:
`(soundness, strength, trust, -cost)`.

- `wrong` is not a low reward — it **aborts the run**, quarantines the instance
  into `corpus/regression`, and files a soundness bug. Never let a learner trade
  soundness for speed.
- `strength`: full decision > bounded/shadow decision > no decision (reusing the
  packs' existing `*-shadow-*` vocabulary).
- `trust`: the existing repo lattice verbatim — checked > replay-only >
  uncertified. **Chain trust is the meet (weakest link) of its edges.**
- `cost`: right-censored PAR-2 (`t_solve` if decided else `2T`); report mean PAR-2
  *and* shifted geometric mean per family so big families don't dominate.

**Weaker-certified vs stronger-uncertified** is settled by a declared *assurance
mode* on the episode (`evidence-required` vs `verdict-only`) so both orderings are
measurable and the choice is data, not dogma. Scalar collapse for bandit updates
fixes the mode first, with α/β pinned by ADR and the vector published alongside.

## Experimental protocol

- **Group k-fold at family level, never instance level.** Family keys: pack id
  (minimum) or curriculum node (stricter); generator identity for scenario and
  frontier instances; SMT-LIB benchmark directory for public instances. For
  parametric families additionally hold out knob ranges — train `N ≤ k`, test
  `N > k`, because extrapolation is the deployment condition.
- **Small-n statistics**: paired per-instance design; Wilcoxon signed-rank on
  per-family PAR-2; bootstrap 95% CIs resampled over *families*; permutation test
  for headline claims; Holm correction across >2 policies.
- **Gating**: a new `dispatch_frontier` ratchet in the `progress_frontier` mold —
  PAR-2 ≥ static baseline minus a pinned tolerance, zero wrong verdicts, per-family
  frontier `N` ≥ committed baseline. Inherit the hardware-relative caveat
  honestly: enforce locally, report-only on CI.

## Prior art

- **MachSMT** — SMT algorithm selection; features are grammatical-construct
  frequencies + quantifier nesting; pairwise ranking beats pointwise regression.
  <https://cs.stanford.edu/~preiner/publications/2021/ScottNiemetzPreinerNejatiGanesh-TACAS21.pdf>
- **SATzilla** — the canonical instance-feature catalogue plus probing features.
  <https://www.cs.ubc.ca/labs/algorithms/Projects/SATzilla/>
- **ASlib** — the standard scenario format (instance × algorithm × runtime,
  feature tables, feature cost, splits). Adopt the format. <https://www.coseal.net/aslib/>
- **Kerschke et al., algorithm-selection survey** — VBS/SBS gap as the measure of
  attainable signal; leakage warnings. <https://arxiv.org/abs/1811.11597>
- **Eggensperger et al., pitfalls in algorithm configuration** — over-tuning,
  censored runtimes, hardware drift. <https://arxiv.org/abs/1705.06058>

## Tasks

| id | title | size |
|---|---|---|
| [T2.1](T2.1-feature-extractor.md) | Deterministic instance-feature extractor | M |
| [T2.2](T2.2-episode-logger-aslib.md) | Episode logger + ASlib-format export | M |
| [T2.3](T2.3-vbs-sbs-gate.md) | **G1: VBS–SBS signal measurement** | S |
| [T2.4](T2.4-graduated-generator-set.md) | Graduated generator eval set | M |
| [T2.5](T2.5-public-corpus-supplement.md) | Public-corpus supplement per atlas row | M |
| [T2.6](T2.6-hardened-pack-variants.md) | Hardened pack variants | M |
| [T2.7](T2.7-vector-reward.md) | Vector reward + scalarization | S |
| [T2.8](T2.8-cv-significance-harness.md) | Family-grouped CV + significance harness | M |
| [T2.9](T2.9-dispatch-frontier-ratchet.md) | `dispatch_frontier` ratchet gate | M |
| [T2.10](T2.10-adrs.md) | ADRs: reward semantics, chain trust composition, feature surface, variant policy | S |

## Risks

- **No-signal** is the most likely failure. Mitigation: G1 first; weight the eval
  set toward frontier ladders and public corpora where routes measurably diverge.
- **Family leakage** — generated variants share a template; an instance-level split
  will overstate policy quality massively.
- **Label trust concentration** — 995 labels rest on one 41,696-line Python
  validator with 834 branches, itself tested only by three negative fixtures. A
  validator bug is silent label noise. Mitigation: route a stratified sample of
  every validation family through the solver's certified routes, extending
  `math_resource_*_routes.rs` from ~10 instances to per-family coverage.
- **`unknown` mishandling** — it is a first-class result and must be its own
  outcome class with censored cost, never collapsed into failure.
