# 10 — Autoformalization: the faithfulness gap and the low-resource-target problem

Arrived after the plan was drafted, from a long-running agent that verified
several claims against upstream repos via `gh` rather than trusting secondary
sources. **It found a risk none of the three critique rounds did** (§3), and it
supplies the strongest available evidence *for* the certificate thesis (§4).

Status of every claim below is marked. Unverified items are marked unverified and
must not be cited.

---

## 1. The compiler is not a faithfulness oracle — and neither is an LLM judge

*miniF2F-Lean Revisited* ([arXiv:2511.03108](https://arxiv.org/html/2511.03108v1))
re-graded autoformalizers with Lean experts:

| Model | LLM-judged | **Human-judged** | Gap |
|---|---|---|---|
| Herald @128 | 97.5% | **62.7%** | **34.8pp** |
| Kimina @128 | 98.4% | **88.1%** | 10.3pp |

End-to-end against the *original informal statements*: **34.8%**. Diagnosis: LLM
judges "treat small discrepancies as negligible even though they significantly
affect the meaning."

Measured semantically rather than by compilation — StepFun-Formalizer
([arXiv:2508.04440](https://arxiv.org/abs/2508.04440)), BEq@1 (Lean-checked
semantic equivalence):

| Benchmark | Kimina-7B | StepFun-32B |
|---|---|---|
| FormalMATH-Lite (in-domain) | 35.1% | **40.5%** |
| ProverBench (OOD) | 13.3% | **26.7%** |
| CombiBench (real-world) | 2.6% | **6.9%** |

**SOTA faithful formalization is ~40% in-domain and ~7% on real-world
combinatorics** — against ~97% compile/LLM-judge headlines. Herald shows the same
shape: 93.2% on miniF2F vs **22.5%** on its own graduate-textbook set
([arXiv:2410.10878](https://arxiv.org/abs/2410.10878)).

Even human experts produce semantic errors in **up to 38.5%** of formalizations
(ReForm, [arXiv:2510.24592](https://arxiv.org/abs/2510.24592)).

## 2. The benchmarks are contaminated with the bug class they measure

**PutnamBench — verified upstream, and worse than advertised.** The Aleph blog
claims 668/672 and counterexamples to 15 statements. Checked against
`trishullab/PutnamBench` via `gh`: merged PRs by Logical Intelligence total **27
statements**, not 15 — #322 (15 files, 2025-12-30), #325 (11 files, 2026-01-06),
#326. The error taxonomy is exactly the predicted surface: `putnam_1980_a4`
asserted `(a=0 ∧ b=0 ∧ c=0)` where the problem required "not all zero" (**logical
inversion**); `putnam_1977_a2` scoped hypotheses so "when a=0 the implication
becomes **vacuously true**". #299 literally reads "Remove 2 unsolved ones (due to
misformalization)" — problems counted as *prover* failures were *benchmark* bugs.

**miniF2F**: 300+ Lean 4 statements corrected; **16 unprovable**; discrepancies
for **more than half** of 488 problems.

**Vacuity, measured.** Lean-GAP ([arXiv:2606.02588](https://arxiv.org/html/2606.02588))
detects 11 regex/AST-visible vacuity patterns — conclusion is `True`, `(h : True)`
placeholder hypotheses, `∃ x, True`, embedded `sorry`. Flag rates: DeepSeek-R1
**4.6%**, Goedel-Formalizer-V2 **3.3%**, GPT-5 1.9%. A **lower bound** — only
syntactically obvious vacuity. "Patterns that result in trivially-true statements
pass elaboration silently because Lean has no reason to reject them."

**Read that last sentence against this repo's own history.** CLAUDE.md records a
vacuous-sat harness hole (`f5b00c72`) that CI caught *after the SHA was public*.
The failure mode is identical and it is ours too.

## 3. THE NEW RISK — capability is bound to target-language data volume

**This is the finding no critique round produced, and it aims at the agentic
thesis directly.**

SPEAC/Eudoxus (NeurIPS 2024, [arXiv:2406.03636](https://arxiv.org/html/2406.03636v3))
targeted **UCLID5**, a very-low-resource formal language ("code examples numbering
in the hundreds rather than thousands or millions"):

| Method | UCLID5 syntactic correctness |
|---|---|
| One-shot standard prompting | **0/33 (0%)** |
| One-shot + CoT (GPT-4-turbo) | 1/33 (3%) |
| Fine-tuned GPT-3.5-turbo (317 examples) | 2/33 (6.1%) |
| **SPEAC** (pivot through a high-resource IR + compiler repair) | **24/33 (72.7%)** GPT-4-turbo; **28/33 (84.8%)** GPT-3.5-turbo |

**No LLM produced code that parses across 660 attempts** — against GPT-4's ~80%
pass@1 on MBPP (Python).

This is the cleanest available answer to "is this just Mathlib memorization?"
**Autoformalization capability is overwhelmingly a function of training-data
volume in the target language, and it does not transfer.** Naive fine-tuning on
hundreds of examples barely moves it (6.1%).

Corroborating: *MiniF2F in Rocq* ([arXiv:2503.04763](https://arxiv.org/abs/2503.04763))
reaches 68% one-shot and **478/488 (98%) with multi-turn compiler feedback** — but
note its own caveat: Coq lacks "an expansive unified library such as Mathlib." It
is the **library** that is the resource, not the language. And the paraphrase study
([arXiv:2604.23135](https://arxiv.org/html/2604.23135)) argues against *pure*
memorization: failures are genuine code-generation errors, and 34–50% of ProofNet#
failures are **hallucinated Mathlib identifiers** (`SimpleGroup` vs
`IsSimpleGroup`). So it is *library/idiom familiarity*, not verbatim recall.

### What works (evidence-backed mitigations)

1. **Pivot through a high-resource representation, then compile/repair down** —
   0% → 84.8%, a >20× gain over fine-tuning, and it helped the *weaker* model more.
2. **Compiler-feedback repair loops** — 68% → 98% (Rocq).
3. **Grammar-constrained decoding** — improves syntactic *and* semantic accuracy;
   "an effective substitute for in-context examples, especially for smaller
   models" ([ACL 2025 Industry](https://aclanthology.org/2025.acl-industry.34/)).
4. **Back-translation consistency**, exploiting the ~70% informal vs ~30% formal
   asymmetry ([survey](https://arxiv.org/html/2505.23486v1)).
5. **Negation/disproof filtering** — FormalMATH
   ([arXiv:2505.02735](https://arxiv.org/abs/2505.02735)) retains 72.09%
   pre-human-review using it.

## 4. "Scope laundering" — the strongest evidence FOR the certificate thesis

*Know Your Limits* ([arXiv:2606.16118](https://arxiv.org/html/2606.16118v1)) on
legal contract entailment via Z3:

- Z3 execution error rates **25.5% (Claude) to 63.2% (Llama)**.
- Solver-based accuracy is **worse** than pure LLM for most models (Claude 74.5%
  vs 63.1%).
- **"Scope laundering" in 15.3–52.5% of predictions: models claim formal grounding
  *without ever executing the solver*.**

That last number is the case for checkable certificates stated by an adversary.
An agent that *says* it proved something is, between 15% and 52% of the time,
saying so without having run anything. **A certificate is the only thing that
distinguishes a proof from a claim of a proof** — and this is measured, not
asserted.

## 5. Does the informal draft help? Only for weak provers

Draft-Sketch-Prove ([arXiv:2210.12283](https://arxiv.org/abs/2210.12283)): miniF2F
**20.9% → 39.3%** (+18.4pp).

But DeepSeek-Prover-V1.5 ([arXiv:2408.08152](https://arxiv.org/html/2408.08152v1))
Table 3, CoT vs non-CoT at matched budget: **+1.1pp** (single-pass 4×6400),
**+3.3pp** (RMaxTS 16×6400). Headline 63.5% miniF2F, 25.3% ProofNet.

**Informal reasoning is worth +18.4pp as a scaffold for a weak prover and +1–3pp
once the prover is strong.** It substitutes for capability rather than adding to
it.

## 6. Corrections to figures circulating elsewhere

- **Lean Workbook is ~57K pairs, not ~140K** ([arXiv:2406.03847](https://arxiv.org/abs/2406.03847)).
  The 140K figure conflates it with Lean-Workbook-Plus.
- ⚠️ **Unverified — do not cite:** *The Faithfulness Gap*
  ([arXiv:2606.16541](https://arxiv.org/abs/2606.16541)). Unknown authors, no
  citations found, unusually tidy numbers.
- **Not verified:** Seed-Prover numbers; Kimina's informal-reasoning ablation
  (likely doesn't exist); per-benchmark defect rates in *Faults in Our Formal
  Benchmarking* ([arXiv:2606.29493](https://arxiv.org/pdf/2606.29493)) — PDF
  extraction failed, and it is the closest thing to the audit paper we want.

---

## What this implies for axeyum

**1. The new risk: do not invent a surface syntax.** SPEAC says an agent facing a
low-resource target scores **0%**, and fine-tuning barely helps. Any novel textual
surface we invent inherits that number. This is the Mathlib network-effect
argument sharpened — it is about *syntax and idiom*, not library size — and it is
the most concrete threat to "agents will drive our goal layer" that this track has
found.

**The mitigation is already the design**, and now has evidence behind it:

- **Goals as structured data, not text** (P6.2/T6.2.2). An agent that calls
  `attempt(goal_id, tactic)` over MCP is not writing a novel language. SPEAC's 0%
  is about *generating syntax*; we can avoid asking.
- **Pivot through a high-resource representation** (SPEAC's own remedy, 0% →
  84.8%). Where an agent must *write* something, let it write SMT-LIB or Lean —
  high-resource, already in the corpus — and compile down. This is an argument for
  P6.1's bridge being **bidirectional and public**, not an internal detail.
- **Compiler-feedback repair** (68% → 98%): our structured errors (T6.4.2) are
  exactly this loop's fuel. Note the ranking, though: AxProverBase's ablation puts
  *iterative refinement* first and *tools* last ("marginal").

**2. `sat`/counterexamples get a second, independent justification.** FormalMATH
uses **negation-based disproof filtering** to retain 72.09% pre-human-review, and
DeepSeek built a concurrent disproof channel. **Disproof is load-bearing
infrastructure for autoformalization pipelines, not just a nicety** — and P6.1c is
what makes ours sound. This strengthens the case for T6.1c materially.

**3. Do not measure on competition math** — already the plan's position, now
overdetermined. The benchmarks are contaminated with the exact bug class
autoformalization produces: 27 PutnamBench statements, 300+ miniF2F, "more than
half" of 488 problems showing discrepancies.

**4. The strongest external validation of the whole stance.** *Scope laundering*
at 15.3–52.5% — models claiming formal grounding without running the solver — is
"untrusted fast search, trusted small checking" argued by someone who was not
trying to argue it. **A certificate is the only thing separating a proof from a
claim of one**, and that is now a measured statement.

**5. Watch the vacuity parallel.** Lean-GAP: "trivially-true statements pass
elaboration silently because Lean has no reason to reject them." CLAUDE.md records
our own vacuous-sat harness hole (`f5b00c72`), caught by CI *after the SHA was
public*. Whatever we build, **vacuity detection belongs in the gate**, not in
review. Same failure, different system.
