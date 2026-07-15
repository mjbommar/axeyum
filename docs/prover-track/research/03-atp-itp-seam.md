# The Automated ↔ Interactive Seam

Research note for the prover track. Status: survey + strategic assessment.
Date: 2026-07-15.

**Bottom line up front.** Three findings should change axeyum's plans:

1. **cvc5's own Lean tactic (`lean-smt`) does not use Alethe. It uses CPC**
   (Cooperating Proof Calculus). The team that co-authors Alethe built their
   Lean reconstruction against a *different* format. This is direct evidence
   against P3.2's "Alethe is the critical path" bet.
2. **`bv_decide` already occupies axeyum's flagship niche** (QF_BV in Lean) via
   *verified reflection*, not reconstruction — and it is upstream, in core Lean.
   Our QF_BV-2x-Z3 advantage does not automatically convert into Lean value.
3. **SMT brittleness is real, measured, and structural** — and it is worst
   exactly where a "prover on axeyum's kernel" would live (quantifiers +
   nonlinear arithmetic), while being nearly absent where axeyum is strongest
   (decidable QF_BV). This is a *targeting* constraint, not a veto. See
   [What this implies for axeyum](#what-this-implies-for-axeyum).

---

## 1. Proof reconstruction in practice

### 1.1 lean-smt (cvc5 → Lean): CPC, not Alethe

`lean-smt` (Mohamed et al., CAV 2025) translates a Lean goal to SMT-LIB, calls
cvc5, and **replays the CPC proof step-by-step** into a Lean term checked by the
kernel ([arXiv:2505.15796](https://arxiv.org/html/2505.15796v1),
[Springer](https://link.springer.com/chapter/10.1007/978-3-031-98682-6_11)).

The paper is unambiguous about the format, and never mentions Alethe as a target:

> "cvc5 can optionally generate a proof in the CPC format that accurately
> mirrors its internal reasoning processes."

Coverage and results:

| Metric | Value |
| --- | --- |
| CPC proof rules total | **662** |
| Rules supported by lean-smt | **~200 (≈30%)** — 163 via theorems, 37 via tactics, 5 via reflection |
| Sledgehammer-derived goals | **2,868 / 5,000 (57%)** — beats veriT+Sledgehammer (2,211) |
| SMT-LIB proofs verified | **15,271 / 21,595 (71%)** vs Ethos's 98% |
| Quantifier-free subset | **5,091 / 9,263 (55%)** |
| Replay cost | **<1s for 98%** of benchmarks; remaining 2% <5s |

Two things matter here. First, **the ~30% rule coverage is deliberate**, not a
backlog: the supported subset "corresponds to the same logical fragment
supported initially by Sledgehammer and SMTCoq." A partial rule set is the
*normal* steady state of a reconstruction project, not a failure.

Second, **replay cost is not the bottleneck** — solving is. The 98%-under-1s
number is the strongest empirical argument that reconstruction overhead is
affordable. The gap between 71% (lean-smt) and 98% (Ethos, the C++ CPC checker)
is the price of kernel-level trust.

**Bit-vectors are explicitly out of scope**: future work includes "expanding
lean-smt's support to additional SMT-LIB theories, such as bit-vectors, floats,
and strings." Lean's BV story is `bv_decide` (§3), not lean-smt.

### 1.2 The format landscape, honestly

| Consumer | Format | Producer | Checker |
| --- | --- | --- | --- |
| Isabelle/HOL `smt` | **Alethe** | veriT, cvc5 | in-kernel replay |
| Coq/Rocq SMTCoq | veriT/CVC4 native | veriT, CVC4 | **verified checker** (reflection) |
| **Lean (lean-smt)** | **CPC** | cvc5 only | in-kernel replay |
| Standalone | Alethe | veriT, cvc5 | **Carcara** (Rust) |
| Standalone | CPC | cvc5 | **Ethos** (C++, Eunoia signatures) |

cvc5's docs describe CPC as designed to "faithfully represent cvc5's internal
reasoning," and note the relationship to Alethe precisely:

> "The concrete syntax of CPC is very similar to the Alethe format. However, the
> proof rules used by these two formats are different."
> — [cvc5 CPC docs](https://cvc5.github.io/docs/latest/proofs/output_cpc.html)

Neither format is deprecated. But the *direction of investment* is legible: CPC
mirrors solver internals (662 rules and growing), Ethos is its performance
checker, and cvc5's flagship Lean integration is CPC-native.

### 1.3 SMTCoq — the reflection contrast

SMTCoq reconstructs veriT/CVC4 proofs, but **does not replay step-by-step**.
Instead it "applies a formally verified checker that, if successful, confirms
the original proof goal as a theorem" (per lean-smt §2). This is the reflection
strategy inside an ITP. lean-smt reports "comparable performance to SMTCoq ...
while supporting a larger logical fragment" — i.e. reflection bought speed, and
cost coverage. SMTCoq's trusted base additionally includes Coq's OCaml
extraction.

### 1.4 Sledgehammer — reconstruction is not the hard part

Desharnais's ["Sledgehammering Without ATPs"](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.38)
(ITP 2025) is a useful calibration. Full Sledgehammer with a 30s timeout reaches
a **72.1%** success rate on Judgment Day. But an **ATP-free hammer** — just
trying Isabelle's own proof methods (`auto`, `metis`, `simp`, `blast`, …) with
premise selection — reaches **46.8%**. Adding the ATP-free portfolio on top of
the real hammer improved it only from 74.1% to **74.6% (+2.5pp)**.

The uncomfortable read: **a large fraction of what a hammer "wins" is winnable
without the ATP at all**, and marginal returns from more solver power are thin.
Also notable: "it is not uncommon for Sledgehammer to fail on a goal that can be
solved by a single [proof method]." Premise selection (MePo 30.1% / MaSh 24.4% /
MeSh 32.4%) is a first-order lever comparable to solver strength.

### 1.5 Known failure modes

Carcara's evaluation found checking failures concentrated in **quantifier
simplifications (Skolemization, one-point elimination) and AC normalization**
([Carcara, TACAS 2023](https://team.inria.fr/veridis/files/2023/05/carcara.pdf)).
This is the recurring shape across every system surveyed: the *logical core*
(resolution, congruence) reconstructs cleanly; the **preprocessing and rewriting
layer is where reconstruction dies**, because solvers do not emit fine-grained
justification for rewrites they consider "obvious." cvc5 has since invested in
this specific gap (RARE / "reconstructing fine-grained proofs of rewrites using
a domain-specific [language]"; IsaRare for verifying SMT rewrites in Isabelle) —
which is itself evidence that rewrite justification is the acknowledged bottleneck.

**Note for axeyum**: our rewrite manifest contracts (`axeyum-rewrite`) are
architecturally well-positioned here — we already treat rewrites as a named,
contracted, enumerable set rather than ad-hoc simplifier code. That is the exact
asset a reconstruction consumer needs, and most solvers lack it.

---

## 2. Alethe in 2026 — is it still the right target?

**Alethe's state.** Alethe is a real, maintained, specified format
([spec](https://verit.loria.fr/documentation/alethe-spec.pdf)), produced by
veriT and cvc5, consumed by Isabelle/HOL and Coq, and checked/elaborated by
**Carcara** (Rust, efficient, TACAS 2023). Its design — close to SMT-LIB syntax,
mixing coarse- and fine-grained steps — is genuinely good and remains the only
format with a serious *multi-producer, multi-consumer* story.

**Alethe's gaps.** cvc5's Alethe output covers "only the theory of equality with
uninterpreted functions, parts of the theory of arithmetic and parts of the
theory of quantifiers"
([cvc5 Alethe docs](https://cvc5.github.io/docs/cvc5-1.0.0/proofs/output_alethe.html)).
**Notably absent: bit-vectors.** Alethe is weakest exactly where axeyum is
strongest.

**The strategic read.** The honest framing is not "Alethe is dead" — it is
**"Alethe is Isabelle's format, CPC is Lean's format."** If axeyum's capstone
P3.7 is "Alethe→Lean reconstruction, making axeyum a Lean tactic backend," then
P3.7 is targeting Lean *through a format that Lean's own SMT tactic declined to
use*. We would be building the Alethe→Lean bridge that the cvc5/Lean community
evaluated and routed around.

That is not automatically wrong — an Alethe→Lean path would be novel, and
Carcara-style elaboration (coarse steps → fine steps) is a real technique we
could exploit. But it must be a *chosen* bet with eyes open, not an inherited
assumption. And "Alethe has no BV rules" means the Alethe bet and the QF_BV
strength do not compose.

---

## 3. bv_decide / LeanSAT — verified reflection

"Interactive Bitvector Reasoning using Verified Bit-Blasting" (Böving, Bhat,
Cicolini, Keizer, Frénot, Mohamed, Stefanesco, Khan, Clune, Barrett, Grosser),
**OOPSLA 2025**, PACMPL 9(OOPSLA2):3259–3285,
[doi:10.1145/3763167](https://dl.acm.org/doi/10.1145/3763167),
[abstract](https://grosser.science/pub/10.1145/3763167/),
[talk](https://www.youtube.com/watch?v=lV5fQyAmOLQ).

**Architecture.** `bv_decide` bitblasts a `BitVec`/`Bool` goal to CNF using a
**verified** bitblaster (AIG-based, using Lean's FBIP paradigm for in-place
mutation of the AIG), ships the CNF to **CaDiCaL**, receives an **LRAT
certificate**, and checks that certificate inside Lean. It is described as "the
first end-to-end verified bitblaster" with "a complete end-to-end proof
(trusting only the Lean compiler and kernel)." It outperforms **CoqQFBV**, the
prior state of the art in verified bit-blasting, and the team verified **7,000+
SMT statements extracted from LLVM**.

**This is the hybrid, and it is the important architectural lesson:**

- The *reduction* (term → CNF) is **verified once, ahead of time** — reflection.
- The *search* (CNF → UNSAT) is **certified per-query** via LRAT — external
  certificate.
- **The SAT solver is not in the trusted base.** Only the LRAT checker and
  Lean's kernel are.

This is precisely axeyum's own architecture — "untrusted fast search, trusted
small checking" — arrived at independently by the Lean community. Our
`axeyum-bv` (term→AIG) + `axeyum-cnf` (Tseitin, DRAT checker, proof-producing
CDCL) is structurally the same stack. **We are not behind on architecture; we
are behind on the Lean-side verified reduction.**

**Costs and limits.** The tactic's proofs use `Lean.ofReduceBool`, which "includes
the Lean compiler as part of the trusted code base" — a real, acknowledged
trust-base expansion beyond the kernel alone. **"Kernel reduction is slow, which
confines [kernel-checked mode] to small certificates."** That is the central
scaling limit of reflection-in-an-ITP: the checker is fast *as compiled code*
and slow *as kernel reduction*, and you must pick which one you trust. The paper
also notes the general obstacles to BV reasoning in ITPs: incomplete bitvector
libraries, partially integrated decision procedures, hard-to-bitblast
operations, and weak host-language integration. `bv_decide` applies a subset of
**Bitwuzla's rewrite rules** for preprocessing.

**Also in flight:** ["LRAT-Catcher: Importing SAT Solver Certificates into Lean4
by Reflection"](https://arxiv.org/pdf/2607.00815) (2026) — the LRAT-checking
layer is itself an active research target, i.e. the certificate-import seam is
still being optimized.

**What does a verified reduction cost to build?** `bv_decide` is the honest
answer: a multi-year, ~10-author effort spanning a verified AIG library, a
verified bitblaster for the full SMT-LIB 2.7 BV operator set, a verified LRAT
checker, and Lean's canonical `BitVec` library with reasoning principles. It is
a research-program-scale investment, not a task.

---

## 4. Reflection vs reconstruction vs external certificates

| | **Reflection** | **Reconstruction** | **External certificate** |
| --- | --- | --- | --- |
| What's trusted | Verified checker + kernel (+ compiler if `ofReduceBool`) | Kernel only | Checker (Carcara/Ethos), *not* an ITP kernel |
| Per-query cost | Cheap (compiled) / expensive (kernel reduction) | ~linear in proof size; **<1s for 98%** (lean-smt) | Fastest (Ethos: 98% vs lean-smt 71%) |
| Up-front cost | **Very high** (verify the reduction) | Moderate, **incremental** (rule by rule) | Low |
| Coverage growth | All-or-nothing per theory | **Graceful** — 30% of rules is shippable | Follows producer |
| Fails how | Doesn't apply | Step unsupported → surfaced to user to prove manually | Trust step / unsupported rule |
| Best for | **Decidable, finite, uniform** (QF_BV, SAT) | **Heterogeneous** reasoning (quantifiers, mixed theories) | Pipelines without an ITP |

The real systems are all **hybrids**, and the seam falls in the same place every
time: *reflect the uniform reduction, certify the search externally, reconstruct
only the heterogeneous glue.* `bv_decide` = verified reduction + LRAT
certificate. lean-smt = 163 theorems + 37 tactics + **5 reflection** rules
(reflection used exactly for "proof rules involving complex side conditions").
SMTCoq = full reflection, paid for in coverage.

**Scaling verdict.** Reconstruction scales *organizationally* (incremental,
partial coverage is useful, failure is graceful and localized). Reflection
scales *computationally* (no per-query proof term) but only over domains uniform
enough to verify once — which in practice means decidable, quantifier-free
theories. Nothing scales over unbounded quantifier reasoning, which is §6's
subject.

---

## 5. Duper / lean-auto

**Duper** (Clune et al., ITP 2024) — a proof-producing **superposition** prover
native to Lean, working directly in dependent type theory; performance
"comparable to Metis'" on TPTP-derived benchmarks (Seventeen Provers under the
Hammer, GRUNGE). Calibration: lean-smt solves **2,868** Sledgehammer-derived
goals vs Duper's **1,116**. Duper is a real, native, proof-producing engine —
but on this benchmark it is ~2.5× behind an SMT-backed tactic. Metis-class, not
Vampire-class.

**lean-auto** (Qian et al., CAV 2024) — the *interface* layer: Lean 4 → ATPs.
Its key design choice is **monomorphization** over encoding-based translation
(the CoqHammer approach), because their Mathlib4 experiment found
encoding-based translation "tends to produce much larger outputs than
monomorphization, which could negatively affect the performance of ATPs." For
ATPs with reconstruction support it replays into the kernel; otherwise it trusts
the result. lean-smt uses lean-auto for preprocessing (dependent type theory →
FOL).

**Read:** the Lean hammer stack is **real but young**, and it is *modular*:
lean-auto (translation) → {cvc5 via lean-smt, Duper, …} → kernel. The
translation layer is a shared, reusable asset — and **it is where axeyum would
plug in**. We would not need to build premise selection or monomorphization; we
would need to be a backend lean-auto can call and whose output someone can
replay. Note also §1.4: premise selection quality rivals solver strength as a
lever, and that is lean-auto's problem, not ours.

---

## 6. SMT brittleness — the strongest argument against an SMT-centric prover

This deserves to be taken seriously, not defused. The evidence is unusually good
here, because the community measured itself.

### 6.1 Mariposa: the quantitative baseline

["Mariposa: Measuring SMT Instability in Automated Program Verification"](https://www.jaybosamiya.com/publications/2023/fmcad/mariposa-extended.pdf)
(Zhou, Bosamiya, Parno et al., FMCAD 2023;
[IEEE](https://ieeexplore.ieee.org/document/10329383/)) mutates SMT queries in
*semantically irrelevant* ways — **assertion shuffling**, **symbol renaming**,
**random reseeding** — and statistically classifies each query as stable /
unstable / unsolvable.

Applied to **17,043 queries** from 14 verification projects (Dafny, F\*, Verus,
Serval):

- **2.6%** of queries are unstable under the most recent Z3 version.
- **Up to 5.0%** for individual projects.
- **Stability deteriorates with solver upgrades.** "Three [projects] have worse
  stability on newer solver versions." There is "a noticeable gap between Z3
  4.8.5 and Z3 4.8.8"; **285 queries are stable under Z3 4.8.5 but unstable
  under Z3 4.8.8**, and the authors bisected Z3's git history to two specific
  commits. **F\* pinned Z3 4.8.5 — a version several years old** — rather than
  absorb the regressions. Z3 4.12.1 has the most instability of the versions tested.
- Multiple mutation methods are needed; no single mutation finds all instability.
- Root cause is overwhelmingly **quantifiers**: matching loops, trigger
  selection. Instability was first reported by the Ironclad Apps developers on
  **non-linear integer arithmetic**; in Komodo it was called **"the most
  frustrating"** problem.
- The queries studied are "the cleaned up final versions" — i.e. **2.6% is the
  post-hardening residue**, measured on code that already survived a hardening
  process. It is a floor, not a ceiling.

Follow-on work confirms this is a live, funded problem: an
[SMT-COMP Instability Track](https://ceur-ws.org/Vol-4008/SMT_paper19.pdf),
[Cazamariposas](https://www.andrew.cmu.edu/user/bparno/papers/cazamariposas.pdf)
(CADE 30, automated instability debugging),
[normalization-based mitigation](https://arxiv.org/html/2410.22419v1), and
[Tunable Automation in Automated Program Verification](https://arxiv.org/pdf/2512.03926).
Two dedicated papers at the [Dafny 2025 workshop](https://popl25.sigplan.org/details/dafny-2025-papers/5/Towards-Proof-Stability-in-SMT-based-Program-Verification).

### 6.2 The practitioner experience

["On the Impact of Formal Verification on Software Development"](https://cseweb.ucsd.edu/~mcoblenz/assets/pdf/OOPSLA_2025_Dafny.pdf)
(OOPSLA 2025) interviewed **14 experienced Dafny users**. Its §4.4 is titled
**"Proof hardening"** and opens:

> *"There's something soul crushing about having to go back to things that you
> thought were done, and do them again."* — P7

The paper's framing is the key structural claim:

> "A key strength of auto-active verifiers like Dafny relative to interactive
> ones like Rocq or Lean is their ability to automatically discharge proof
> obligations by relying upon SMT solvers. However, this automation comes at a
> cost: the proof obligations ... often involve reasoning outside of decidable
> theories, and hence, rely on brittle SMT solver heuristics that can sometimes
> fail. Thus, verified software development has to include a new phase: **proof
> hardening**."

Note precisely what is blamed: **"reasoning outside of decidable theories."**
Not SMT per se. The undecidable fragment.

The accounts:

- P7: introducing "some little fiddly change to the code, just maybe pass one
  more element in the state [...] and all the proofs would just stop working."
- **P7, P10, P11, P13**: "updating Dafny, changing the underlying Z3 solver, or
  even **verifying on a different machine** could break a brittle proof."
- "While these issues were revealed by minor changes, their fixes were a major
  enterprise and major setbacks."
- Vocabulary used: the verifier "goes off the deep end" (P8); it "bites you"
  (P5); a "major roadblock" (P10); **"existential dread"** and **"soul crushing"** (P7).

**Opacity is a separate, equally damning complaint.** On proof debugging: P2
described the output as **"spits out a no"**; P3 called it a **"black box
thing"**; P7 said it provides **"no help."** A beginner's reaction: "have to give
a better error message."

**Resource limits don't rescue it.** P5–P8, P10 monitor Z3's resource count, but
"**no participant reported a reliable method for determining this limit**," and
P7/P10 had to **increase the limit over time** — defeating its purpose. P7
described "pushing left"; it still drifted.

**The users' own mitigation is to turn the automation down.** Style guides
adopted by P6, P7, P11, P13 "aim to **reduce automation** — and hence the
instability due to automation heuristics — as much as possible." P5:

> *"I want Dafny to be as stupid as possible and not help me at all [...]. Make
> me be really verbose, but [...] make sure the proofs are easy for [Dafny]."*

Another: "I don't play that game [...] if I'm needing to bump the resource count
up, I break it down" — decomposing into lemmas rather than raising limits, and
using `isolate-assertion` to send **one assertion at a time** rather than
Dafny's default batching.

The [Dafny team's own blog](https://dafny.org/blog/2023/12/01/avoiding-verification-brittleness/)
documents the same guidance, and there is a
[reported success story](https://popl25.sigplan.org/details/dafny-2025-papers/8/Helping-users-to-reduce-Brittleness-in-their-Dafny-programs-a-success-story)
in helping users reduce brittleness. See also
[Kiran Gopinathan on slow & brittle proofs](https://kirancodes.me/posts/log-proof-localisation.html)
and [EPFL's instability conjecture](https://dslab.epfl.ch/pubs/smt-instability-conjecture.pdf).

### 6.3 What the brittleness evidence actually says

Read carefully, the evidence is **narrower and more actionable** than "SMT is
brittle, don't build on it":

1. **Brittleness is a property of the undecidable fragment**, not of SMT. Every
   root cause named is quantifier instantiation, trigger selection, matching
   loops, or nonlinear arithmetic. Mariposa's corpus is "a mixture of
   bit-vector, integer arithmetic, and uninterpreted functions, **typically with
   quantifiers**." Nobody reports `bv_decide` being flaky — a decided QF_BV goal
   is decided.
2. **The mechanism is heuristic search over an infinite space** with no
   completeness guarantee, where the solver's arbitrary choices (seeds, term
   ordering, clause order) determine success. Syntactic perturbation reshuffles
   those choices. This is intrinsic to E-matching, not a bug awaiting a fix.
3. **Certificates do not fix brittleness.** A proof certifies the queries that
   *succeed*. It says nothing about the query that timed out after an unrelated
   edit. **Axeyum's entire differentiator — trusted checking — is orthogonal to
   the thing practitioners actually hate.** This is the single most important
   sentence in this note. Our evidence story answers "is this answer right?";
   the user's pain is "why did this stop working?"
4. **Users respond by reducing automation** — moving *toward* the ITP end of the
   spectrum, exactly the direction that makes a maximally-automated prover less
   valuable.
5. **Instability is a solver-upgrade tax on the vendor.** F\* pinned Z3 4.8.5 for
   years. If axeyum were the solver under someone's verifier, **every one of our
   performance improvements is a potential stability regression for them**, and
   we would inherit the pinning dynamic — including pressure to freeze the
   heuristics we most want to improve.

---

## What this implies for axeyum

### Engaging with (6) directly

The strongest form of the anti-SMT-prover argument is: *an interactive prover
built on an SMT core inherits, at its foundation, a failure mode that its users
experience as non-determinism — proofs that break for reasons that are not about
their proof — and axeyum's trusted-checking differentiator does nothing about
it, because certificates only certify successes.* Practitioners hate SMT-based
verification not because they distrust the `unsat`, but because they cannot
predict or control **when** they will get one. A prover whose value proposition
is "we prove it *and* we can prove that we proved it" is answering a question
users are not asking.

I think this argument is **correct as stated, and correctly scoped** — and the
scoping is the whole opportunity.

Brittleness lives in the undecidable fragment. It is caused by heuristic
quantifier instantiation over an infinite search space. It is **not** a property
of QF_BV, where axeyum is strong and where a decision procedure either decides
or exhausts a resource limit — deterministically, with an explicit seed and
explicit bounds that we already treat as public API promises. Axeyum's
determinism promise (stable iteration order, explicit seeds, explicit resource
limits) is, read in this light, **already a partial anti-brittleness stance** —
we have been building the mitigation without naming it.

So the conclusion is not "don't build the prover." It is **"do not build a
Dafny."** Do not build a system whose user-facing promise is "write your spec,
we'll figure it out," because that promise is exactly what brittleness breaks,
and no amount of proof machinery repairs it.

### Concrete implications

**1. Re-examine the P3.2 Alethe bet — this is the actionable finding.**
The evidence is specific: cvc5's own Lean tactic chose CPC; Alethe has **no BV
rule coverage**, so our best theory can't ride it; Alethe's real consumer is
Isabelle. Three coherent options, in my order of preference:

- **(a) Retarget P3.7 to Lean-native, not Alethe→Lean.** If the goal is "axeyum
  is a Lean tactic backend," the shortest honest path is `bv_decide`'s: emit
  **LRAT** (we already have a proof-producing CDCL and DRAT infrastructure), and
  let a verified Lean-side reduction consume it. This composes with our actual
  strength.
- **(b) Keep Alethe, but retarget its consumer to Isabelle**, which is where
  Alethe is genuinely load-bearing — and where Carcara gives us an independent
  checker for free. Honest, smaller, real.
- **(c) Keep Alethe→Lean as a deliberate research bet**, with the note that we
  are building what cvc5's team routed around, and that BV won't ride it.

The one thing not to do is leave P3.2 marked "critical path" on the inherited
assumption. **This warrants an ADR**, per the standing rule that decisions are
not made silently. Whatever we choose, `axeyum-rewrite`'s manifest contracts are
an unusual asset for *any* reconstruction target (§1.5) — that investment is not
at risk under any option.

**2. `bv_decide` is the competitive fact of the matter for QF_BV-in-Lean.**
It is upstream, verified, and it beat CoqQFBV. Being 2× Z3 on QF_BV does **not**
translate into Lean value on its own, because `bv_decide`'s bottleneck is not
raw solve time — it is the verified reduction and, in kernel-checked mode,
kernel reduction over certificates ("confines this mode to small certificates").
The interesting questions are therefore: *can axeyum's AIG/CNF pipeline produce
**smaller** certificates?* and *can our preprocessing close goals `bv_decide`
cannot?* Those are measurable, and they are the right head-to-head — not PAR-2
against Z3. Note also `bv_decide` pays a real trust cost (`ofReduceBool` pulls
in the Lean compiler); a route that stays kernel-only is a genuine differentiator
if we can make certificates small enough.

**3. Build for the decidable core; be honest at its edge.**
Aim at where determinism is achievable and brittleness is absent. When we must
leave the decidable fragment, **surface it** — the failure mode users cannot
tolerate is the silent one ("spits out a no"). A prover that reports *why* it
failed, *what fragment* it left, and *which* resource bound it hit is directly
attacking P2/P3/P7's opacity complaint, which the interview data shows is a
first-class pain independent of instability. This is a differentiator we can
build and that Z3 structurally does not offer.

**4. Take stability as a product requirement with a measurable gate.**
Mariposa is a *methodology we can adopt*: mutate (shuffle / rename / reseed),
measure, gate. Given our existing determinism promises and self-checking scenario
corpus (ADR-0008), **a Mariposa-style instability ratchet is a natural addition
to `just check`** — cheap to build, and it would let us make a *measured* claim
("axeyum is stable under N mutations where Z3 is not") in a domain where the
incumbent measurably struggles. That is a more defensible and more differentiated
claim than PAR-2 parity. It also pre-empts the vendor-side pinning tax (§6.3.5):
if we ratchet stability, our own upgrades stop being our users' regressions.

**5. Calibrate expectations on the hammer front.**
Sledgehammer's ATP-free baseline (46.8% vs 72.1% full) and lean-smt's 57% say
the ceiling for "throw a strong solver at ITP goals" is lower than it looks, and
that premise selection rivals solver strength as a lever. Reconstruction cost is
*not* the problem (98% under 1s). If axeyum enters this space, we enter it as a
**backend behind lean-auto**, reusing its monomorphization and premise
selection, and we should expect solver strength to be a second-order term.

### The honest summary

The brittleness literature is not an argument against axeyum. It is an argument
against a *specific product* — the maximally-automatic, undecidable-fragment,
"trust the heuristics" verifier — that axeyum should not build. It is
simultaneously an argument *for* the thing axeyum is unusually well-positioned
to build: a **deterministic, resource-bounded, evidence-carrying decision
procedure with legible failure**, whose stability is measured and ratcheted, and
whose certificates make it kernel-trustable.

But we should be clear-eyed that trusted checking and stability are **different
axes**, that our current differentiator is on the axis users complain about
less, and that our flagship theory's natural ITP home already has a verified
incumbent. The next concrete task is the **P3.2 format ADR** (§1, §2) — it is
cheap, it is decidable today from the evidence in this note, and everything
downstream on the prover track depends on it.

---

## Sources

- lean-smt (CAV 2025): [arXiv:2505.15796](https://arxiv.org/html/2505.15796v1) · [PDF](https://arxiv.org/pdf/2505.15796) · [Springer](https://link.springer.com/chapter/10.1007/978-3-031-98682-6_11) · [author copy](https://hanielbarbosa.com/papers/2025cav.pdf)
- cvc5 CPC proof format: https://cvc5.github.io/docs/latest/proofs/output_cpc.html
- cvc5 Alethe proof format: https://cvc5.github.io/docs/cvc5-1.0.0/proofs/output_alethe.html
- Ethos / Eunoia: https://github.com/cvc5/ethos/blob/main/user_manual.md
- Alethe specification: https://verit.loria.fr/documentation/alethe-spec.pdf
- Carcara (TACAS 2023): https://team.inria.fr/veridis/files/2023/05/carcara.pdf · [ACM](https://dl.acm.org/doi/abs/10.1007/978-3-031-30823-9_19)
- bv_decide (OOPSLA 2025): [doi:10.1145/3763167](https://dl.acm.org/doi/10.1145/3763167) · [abstract](https://grosser.science/pub/10.1145/3763167/) · [talk](https://www.youtube.com/watch?v=lV5fQyAmOLQ)
- LeanSAT: https://github.com/leanprover/leansat
- Lean `bv_decide` docs: https://lean-lang.org/doc/reference/latest/releases/v4.12.0/
- LRAT-Catcher (2026): https://arxiv.org/pdf/2607.00815
- Duper (ITP 2024): https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2024.11
- Lean-auto (CAV 2024): https://arxiv.org/abs/2405.14340
- Sledgehammering Without ATPs (ITP 2025): https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.38
- Mariposa (FMCAD 2023): [extended](https://www.jaybosamiya.com/publications/2023/fmcad/mariposa-extended.pdf) · [IEEE](https://ieeexplore.ieee.org/document/10329383/)
- Impact of Formal Verification on Software Development (OOPSLA 2025): https://cseweb.ucsd.edu/~mcoblenz/assets/pdf/OOPSLA_2025_Dafny.pdf
- Cazamariposas (CADE 30): https://www.andrew.cmu.edu/user/bparno/papers/cazamariposas.pdf
- SMT-COMP Instability Track: https://ceur-ws.org/Vol-4008/SMT_paper19.pdf
- Using Normalization to Improve SMT Solver Stability: https://arxiv.org/html/2410.22419v1
- Tunable Automation in Automated Program Verification: https://arxiv.org/pdf/2512.03926
- Dafny blog, avoiding verification brittleness: https://dafny.org/blog/2023/12/01/avoiding-verification-brittleness/
- Dafny 2025 workshop, proof stability: https://popl25.sigplan.org/details/dafny-2025-papers/5/Towards-Proof-Stability-in-SMT-based-Program-Verification
- SMT instability conjecture (EPFL): https://dslab.epfl.ch/pubs/smt-instability-conjecture.pdf
- Slow & brittle proofs: https://kirancodes.me/posts/log-proof-localisation.html
