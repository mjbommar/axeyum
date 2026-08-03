# Phase 8 — open-problem intake, triage, and the output taxonomy

Verdict from review: **sound, needs revision.** The core thesis survives contact
with the evidence; three claims need correction and one reframing is required.

## What holds, now with data

**The intake source is real and better than claimed.**
`google-deepmind/formal-conjectures`: exactly **1022 `.lean` files, 509 under
`FormalConjectures/ErdosProblems`**, Apache-2.0 (code) / CC-BY 4.0 (content),
**linter-enforced machine-readable metadata** (`@[category research open]`,
`@[AMS n]`, `answer(sorry)` polarity markers, uniform `*Reference:*` URLs),
immutable `bench-v{N}-lean4.X.Y` tags, daily commits through 2026-07-31. A
throwaway regex resolves the main statement in **501/509** files. It is *designed*
for machine consumption — there is a 564-line `AGENTS.md`.

But: only **~316 of the 509 are actually open** (164 are already
`research solved`), so the real denominator is ~316.

**The honest expectation is confirmed and quantified. Triage failures dominate.**

**The niche claim survives strongly.** The community ledger of AI contributions to
Erdős problems (`teorth/erdosproblems` wiki) has **only 3 entries in its
computation/certificates column** (#396, #513, #650) against 200+ formalizations
and 60+ AI proof contributions. Nobody ships a bounded-shadow pipeline or a
standardized "no counterexample below N, certificate-checked" artifact.
bbchallenge (BB(5), Coq-verified, July 2024) proves the community model works — but
built it for exactly one problem family. **This is axeyum's identity sentence,
uninstantiated in this space.**

## Correction: the Erdős attribution, handled carefully

The reviewer flagged "#146/#180 were counterexample-shaped" as wrong, citing the
**October 2025** GPT-5 episode — where claims about ten Erdős problems were
retracted after Thomas Bloom called them "a dramatic misrepresentation" (the model
had found existing literature).

That correction targets a different event. The **August 2026** `openai/ten-proofs`
README, read directly, states: *"Extremal number conjectures: Counterexamples to
the compactness and degeneracy conjectures in extremal graph theory, resolving
Erdős problems 146 and 180."* So the #146/#180 attribution stands for the 2026
release.

**Both facts go in the plan**, because the reviewer's underlying point is sound and
important: the October 2025 retraction is exactly the retrieval-hallucination
failure mode this pipeline is meant to guard against, and intake facts must be
verified against the ledger rather than recalled. Genuine AI resolutions have been
mostly proof-shaped (#728 via GPT-5.2 Pro + Aristotle Lean proof, Jan 2026 — Tao:
"most unambiguous"; #397, #729, #848), with counterexample-shaped results appearing
in 2026 on other problems.

## Correction: the curriculum vocabulary is too coarse to be the classifier

`docs/curriculum/curriculum.toml` defines `decidable | computable | bounded |
undecidable`, but across its **23 nodes** the distribution is 1/6/16/0 —
`undecidable` is defined and never used. Triage needs a **statement-shape
taxonomy** layered on top; the curriculum field becomes the *display* vocabulary,
not the classifier.

## The statement-shape taxonomy (the actual triage instrument)

Fractions grounded in a 29-file sample plus whole-corpus token greps. **61% of
files touch ℝ.**

| Bucket | Shape | Shadow | Fraction |
|---|---|---|---|
| **A** | Π₁ over ℕ/finite structures, decidable matrix | `check P(n) for n ≤ N` — **mechanical** | 7–10% (~35–50) |
| **B** | witness/counterexample-shaped, incl. `Infinite {n \| P n}` with decidable `P` | bounded witness search — **mechanical** | ~10% (~50) |
| **C** | asymptotic/limit/density (`Tendsto`, `limsup`, `=o[atTop]`, `∀ᶠ`) | **none** without human reduction | **45–50%** (~230–255) |
| **D** | quantified over infinite sets/sequences | only via human theorem (Keller-class) | 5–8% |
| **E** | reals/measures/geometry over ℝⁿ | generally none | 13–15% |
| **F** | ordinals/cardinals/other | none | 5–8% |

Hybrid subclass worth tracking: E→A hybrids where an outer real `∃C` blocks the
shadow but fixing a rational `C` yields decidable instances — shadow with a
parameter disclosed in the claim.

**So the mechanizable pool is roughly 17–20% of the open set, ~55–100 problems.**
Publishing that census is the experiment's first real result.

## Reframing: the flagship output

Landmark thresholds cost CPU-years with bespoke encodings. Axeyum's measured
position (8/113 on the p4dfa QF_BV slice at 20 s, parity with Z3 on that corpus but
hard-capped like Z3) means **it cannot chase records**.

The highest-value, lowest-compute output the evidence points to is one the original
plan under-weighted: **(e) misformalization detection.** DeepMind's AlphaProof
Nexus had to invent crude "test lemmas" (prove the first few sequence terms match
the formal definition) before attempting any conjecture, and formal-conjectures has
**312 open PRs** needing exactly this QA. A certified finite-instance checker tied
back to the Lean statement serves outputs (a)–(d) *and* is immediately useful
upstream at small N.

## Quantitative calibration — what computer-assisted resolutions cost

| Problem | Year | Compute | Proof | Finite-reduction mechanism |
|---|---|---|---|---|
| Boolean Pythagorean triples | 2016 | 35,000 CPU-h + 16,000 verify | ~200 TB DRAT, later Coq-verified | prefix restriction |
| Schur 5 | 2018 | >14 CPU-yr + ~36 CPU-yr ACL2 check | >2 PB DRAT | prefix restriction |
| **Keller dim 7** | 2020 | **~202 CPU-h** | 224 GB DRAT, ACL2-checked | human chain: Szabó → Keller graphs → Kisielewicz |
| **Erdős discrepancy C=2** | 2014 | **hours, one workstation** | 13 GB DRUP | prefix restriction |
| Packing chromatic χρ(Z²)=15 | 2023 | 4,851 CPU-h + 4,337 check | 34 TB DRAT / 122 TB LRAT, cake_lpr | human lifting lemma |
| R(3,8)/R(3,9) certified | 2024–25 | 59 h sequential | 31 GB DRAT | finite by definition |
| **Hadwiger–Nelson ≥5** | 2018 | **minutes–hours** | MB-scale | finite-subgraph monotonicity |
| Empty hexagon h(6)=30 | 2024 | 17,300 CPU-h | 180 TB LRAT, **cakeLPR concurrent, zero storage**; encoding Lean-verified | order-type abstraction |
| Lam's problem re-verification | 2021 | ~2 desktop-CPU-yr | ~110 TiB DRAT, GRATgen 33,000 core-h | coding-theory case split |

Structural lessons: (i) every landmark needed a problem-specific encoding insight
worth 1–2 orders of magnitude **plus certified symmetry breaking** — there is no
push-button lane at record scale; (ii) three reduction classes recur — *prefix
restriction* (mechanical), *already-finite spaces*, *human-theorem collapse* — and
**only the first is mechanizable**, which is exactly the bounded-shadow class;
(iii) since 2024, streaming DRAT→LRAT→verified-checker eliminates proof storage,
and proof size tracks encoding quality, not difficulty; (iv) **small certified
results are cheap** — Keller ~200 CPU-h, Hadwiger–Nelson verification ~1 s, EDP
hours on a workstation. **Axeyum can play in the hours-to-days band.**

## Who is already in the space, and the empty quadrant

- **LLM+Lean proof search at scale** — AlphaProof Nexus solved 9/353 formalized
  open Erdős problems and 44/492 OEIS conjectures at "a few hundred dollars per
  problem," with published Lean proofs. Harmonic Aristotle, Aletheia, Seed Prover.
- **Construction search** — AlphaEvolve (kissing number d11 592→593, Erdős
  minimum-overlap bound, Ramsey lower bounds) whose outputs have **no independent
  certificate**, only a re-runnable scorer.
- **Bespoke certified SAT** — Heule/Subercaseaux/MathCheck: months per problem, no
  mass pipeline.
- **Finite-instance tooling in Lean** — Plausible/SlimCheck (random, no
  certificates); ad-hoc `decide` (**45 of the 509 files already use `decide` in
  `@[category test]` statements — the maintainers' own seed set**); Nexus "test
  lemmas" as an improvised misformalization guard.

**The empty quadrant: mass triage + mechanical bounded shadows + standardized
checkable artifacts.** Genuinely unoccupied.

Re-certifying published AI constructions is also open territory — AlphaEvolve's
outputs have no independent certificates.

## Design

**Registry** — `docs/open-problems/registry/`, one row per problem, generated and
hand-annotated fields separated, pinned to an immutable `bench-v{N}` tag. Fields:
source (repo/path/tag/commit/url/license), `decl`, harvested `category`/`ams`/
`answer_polarity`, triage `shape`, `matrix_decidable`
(regex-guessed | confirmed-lean | no), `curriculum_decidability` for display, and
the shadow block:

```
shadow = { kind = "prefix-sweep", parameter = "n", bound = 5000,
           direction = "counterexample-refutes",   # THE soundness-critical field
           fragment = "finite-replay+QF_BV", derivation = "reviewed" }
```

**The `direction` field is soundness-critical.** A shadow counterexample refutes
the conjecture only when the Lean statement's polarity makes it so, and **a
completed sweep is never evidence of truth.**

**Triage stages:** S0 regex harvest of all 509 (no Lean needed; ~501/509 resolve) →
S1 token classifier (C-bucket reliably detected by
`Tendsto|limsup|=o\[|atTop|Density`; yields a candidate pool of 80–150) → S2 Lean
elaboration **on the pool only** (a metaprogram querying `Decidable` instances
against the pinned tag) → S3 shadow derivation with explicit direction → S4
encoding → S5 run loop → S6 pack + registry + dashboard.

**Run loop:** deterministic, budgeted exactly as
`bench-public-qfbv-sat-bv-guarded`, `unknown` first-class, per-problem monotone
ratchet `swept_bound[problem] ≥ baseline` in the `progress_frontier` style, JSON
artifact per run (solver version, seed, budgets, load average).

**Artifact:** a new pack family `artifacts/open-problems/<id>-v0/` reusing the five
required files plus `shadow.json`. The five output classes map onto existing axes
with **no new proof machinery**:

- **(a) bounded no-counterexample** — `expected_result=unsat`, `proof_status=checked`
  when DRAT-checked, `replay-only` when ground-evaluated. Mandatory boundary text.
- **(b) witness/counterexample** — `sat` + `checked` (model replay), graduating to
  "confirmed" only when a generated Lean `example : ¬P k := by decide` compiles
  against the pinned tag. **The Lean tie-back is what makes the claim about the
  formal conjecture rather than about axeyum's transcription of it.**
- **(c) certified special case** — fixed-parameter instance pack.
- **(d) pattern** — an `axeyum-cas` closed-form/recurrence certificate over the
  small-case table; claim limited to the finite table.
- **(e) misformalization signal** — a shadow disagreeing with known ground truth
  (e.g. an OEIS term); reported upstream, **never held as a math result**.

**Claim labelling:** no new top-level trust vocabulary is needed. The
`(expected_result, proof_status)` pair plus route chips already express everything.
What is needed is one new *display* row in `CLAIM-LABEL-MATRIX.md` — "bounded
no-counterexample sweep; allowed claim: no counterexample with parameter ≤ N under
the recorded shadow; do not claim: support, likelihood, or partial proof" — and a
hard rule that every open-problem pack names its shadow direction.

## Tasks

| id | title | size |
|---|---|---|
| [T8.1](T8.1-adr-intake-claims.md) | ADR: intake, artifact family, claim labels | S |
| [T8.2](T8.2-registry-harvest.md) | Registry harvest script (regex, no Lean) | S |
| [T8.3](T8.3-shape-triage.md) | Token-shape triage + triage dashboard | M |
| [T8.4](T8.4-pilot-shadows.md) | Pilot: 10 hand-derived shadows from the `decide` seed set | M |
| [T8.5](T8.5-shadow-runner-ratchet.md) | Shadow runner + swept-bound ratchet | M |
| [T8.6](T8.6-lean-decidability-probe.md) | Lean elaboration decidability probe | L |
| [T8.7](T8.7-lean-tieback.md) | Lean tie-back for witnesses | L |
| [T8.8](T8.8-witness-search-lane.md) | Bucket-B witness-search lane | M |
| [T8.9](T8.9-upstream-contribution.md) | Upstream contribution path | S |
| [T8.10](T8.10-census-scale-out.md) | **Scale-out + published triage census** (the headline result) | L |

## Risks

- **Overclaiming is the existential risk.** The October 2025 retraction shows how
  fast credibility burns. A sweep is *never* phrased as support — small-N evidence
  has famously reversed (Pólya false at ~906 million; Skewes; Mertens).
  "No counterexample below N" is a bound on the search, not a probability
  statement about the conjecture.
- **Shadow derivation is a new untrusted layer** — the exact analogue of the
  encoding-trust gap that forced the empty-hexagon team to Lean-verify their
  encoding. A wrong shadow yields a confidently-labelled artifact about the wrong
  statement. Mitigations: the direction field, the Lean `decide` tie-back, negative
  fixtures, and fuzz seed-classes emitting degenerate parameters per shadow family.
- **Duplicated effort** — do not compete with Nexus-style proof search,
  Plausible-style random testing, or AlphaEvolve-style construction search. The
  moment a task drifts toward "try to prove the conjecture," it is off-branch.
- **Arithmetic route mismatch** — most A-bucket instances involve
  primes/divisibility over unbounded ℕ, so the natural route is exact ground
  evaluation / `axeyum-cas` replay, **not** bit-blasting; fixed BV widths silently
  narrow the claim and the width must be part of any BV-routed claim.
  SAT/DRAT applies to the coloring/graph/table minority.
- **Toolchain churn and licensing** — mathlib monthly churn plus the July 2026
  module refactor mean everything pins to immutable `bench-v{N}` tags; Lean tooling
  stays out of the default no-C/C++ build. Apache-2.0/CC-BY intake is clean with
  attribution; CC-BY-SA subdirectories (Wikipedia/MathOverflow/OEIS-derived) need
  share-alike handling if redistributed in packs.
- **Registry drift** — formal-conjectures updates solved problems in place
  (category flip + `answer()` substitution). Re-harvest per tag and retire flipped
  rows, or axeyum ends up "sweeping" solved problems.
- **Open Problem Garden is dormant** — DNS/TLS failures, 2007-era Drupal, no API.
  Drop it from the plan. OEIS remains a viable secondary (2,649 open conjectures
  mechanically extracted by DeepMind; Sequencelib formalizing OEIS in Lean).
