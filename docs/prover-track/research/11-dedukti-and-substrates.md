# Dedukti, Lambdapi, Logipedia, and Metamath Zero as Certificate Substrates

**Status:** research note, first pass, 2026-07-15.

Follow-up to the gap named in [01-itp-anatomy.md](01-itp-anatomy.md), which
identified λΠ-calculus modulo rewriting / Dedukti as *the substrate candidate*
for a certificate-first goal layer and then never researched it. This note
closes that gap.

**Framing question.** We are designing a certificate-first goal layer: a tactic
is not a proof-term builder (de Bruijn) nor a function over an abstract `thm`
(LCF) — it is an **untrusted procedure that emits a certificate**, plus a small
checker that turns it into a kernel-checked term. Dedukti is the closest
existing artifact to that idea. Does it already solve it? Should we adopt it?

Everything below is cited. Claims I could not verify from a primary source are
marked **[unverified]**.

---

## 1. What Dedukti actually is

Dedukti is a **type-checker for the λΠ-calculus modulo rewriting** — the
Edinburgh Logical Framework (LF, dependent types: λ-abstraction and Π-types)
extended so that function and type symbols may be **defined by rewrite rules**.
It takes as input type declarations and rewrite rules, and checks that
expressions are well typed *modulo those rewrite rules plus β-reduction*
([Deducteam/Dedukti](https://github.com/Deducteam/Dedukti),
[arXiv:2311.07185](https://arxiv.org/abs/2311.07185)).

The pivotal design move: **conversion is parameterized**. In LF, two types are
convertible iff β-equal. In λΠ-modulo, conversion is β plus a user-supplied
rewrite system R. You hand Dedukti a *theory* — a signature of symbols plus R —
and Dedukti becomes a proof checker **for that theory**. This is exactly the
"supply a rewrite system and it becomes a checker for that theory"
parameterization: Deducteam describes Dedukti as "a logical framework in which
the user encodes the theory she wants to use via rewriting rules"
([Deducteam activity report 2021](https://raweb.inria.fr/rapportsactivite/RA2021/deducteam/index.html)).

Symbols come in two flavors: **static** (not definable, opaque constructors) and
**definable** (given meaning by rewrite rules). The checker validates that
rewrite rules preserve typing — LHS and RHS must have convertible types in the
appropriate context — that LHS are higher-order patterns, and that RHS free
variables occur in the LHS
([Deducteam/Dedukti](https://github.com/Deducteam/Dedukti)).

### The TCB — and the honest part

Here is the crux, and it is the single most important fact in this note for our
purposes.

**Decidability of type checking in λΠ-modulo requires the rewrite system to be
confluent and terminating** — and **Dedukti does not prove either**. Confluence
and termination are checked by *external* tools (CSI^HO for confluence,
SizeChangeTool for termination) or assumed
([Deducteam/Dedukti](https://github.com/Deducteam/Dedukti),
[Deducteam software page](https://deducteam.gitlabpages.inria.fr/software.html),
[Deducteam 2021 report](https://raweb.inria.fr/rapportsactivite/RA2021/deducteam/index.html):
"To ensure the decidability of typing, the rewriting system must be terminating.
The framework includes tools to prove the confluence, the termination, and the
consistency of theories expressed in Dedukti").

So the Dedukti TCB is *not* just "the small kernel". It is:

1. the λΠ-modulo conversion/type-checking kernel (small, OCaml), **plus**
2. the **theory file** (the rewrite system R you supplied), **plus**
3. the **meta-theoretic side conditions on R** — confluence, termination, and
   (for the encoding to mean anything) conservativity/adequacy of the encoding
   with respect to the source logic — which are discharged by *separate tools*
   or by *a paper*, not by the checker.

That is a materially different trust story from "small kernel checks a term".
The kernel is small; **the theory is the TCB**, and the theory is where all the
hard content lives. Item (3) is not a nitpick: a non-confluent or
non-terminating R makes the checker's answer meaningless (or divergent), and an
inadequate encoding makes a checked Dedukti term not correspond to a theorem of
the source logic.

Deducteam itself markets Dedukti as having "a small trust base, theory
independent" ([Deducteam 2024 activity
report](https://radar.inria.fr/report/2024/deducteam/index.html)). Both halves
of that are true and in tension: it is small *because* it is theory-independent,
and it is theory-independent *because* it pushes the theory into an untrusted-
but-load-bearing input.

**Size.** Dedukti is OCaml (93.3% of the repo), ~2,280 commits, 237 stars, 28
forks, license CeCILL-B; latest tagged release **2.7 (June 2022)**
([Deducteam/Dedukti](https://github.com/Deducteam/Dedukti)). I did not find an
authoritative kernel LoC figure. **[unverified]** The Kontroli paper (below) is
the natural source for a kernel-size comparison; I could not extract its LoC
table from the PDF in this pass. The Kontroli abstract does establish that
Dedukti is "the reference proof checker for this calculus" and that Kontroli — a
Rust reimplementation — beats it on all five evaluated datasets, with up to
6.6× on 8 threads for the most time-consuming phase
([arXiv:2102.08766](https://arxiv.org/abs/2102.08766), CPP 2022). Note the title
drift: the preprint was "**Small**, Fast, Concurrent Proof Checking"; the
published CPP version is "**Safe**, Fast, Concurrent…"
([DeepAI mirror](https://deepai.org/publication/small-fast-concurrent-proof-checking-for-the-lambda-pi-calculus-modulo-rewriting),
[POPL22/CPP page](https://popl22.sigplan.org/details/CPP-2022-papers/20/Safe-Fast-Concurrent-Proof-Checking-for-the-lambda-Pi-Calculus-Modulo-Rewriting)).
That a *Rust* λΠ-modulo checker already exists is directly relevant to us.

## 2. Certificate substrate or proof assistant? The Dedukti/Lambdapi split

The split is clean and it is the right one:

- **Dedukti** = the checker. No tactics, no elaboration, no metavariables in the
  user-facing sense. You give it fully elaborated terms; it says yes/no
  ([Deducteam/Dedukti](https://github.com/Deducteam/Dedukti)).
- **Lambdapi** = the proof assistant layer on the same calculus: interactive
  development, tactics, implicit arguments, **automatic coercion insertion**,
  Emacs/VSCode LSP support, and a Dedukti export
  ([Deducteam/lambdapi](https://github.com/Deducteam/lambdapi),
  [Deducteam 2024 report](https://radar.inria.fr/report/2024/deducteam/index.html)).

**Does Dedukti-the-checker do what our "small checker" would do?** Partly, and
this is the honest answer: it does the *last mile* — "take a fully elaborated
certificate and confirm it type-checks in theory T". It does **not** do the
middle mile that our design actually cares about — "take a *compact, non-proof-
term* certificate (a DRAT trace, an LRAT chain, a `ring` reflection witness, an
Alethe step list) and *elaborate* it into a checkable term". In Dedukti-land
that middle mile is done by **per-source translators** written in OCaml
(lrat2dk, hol2dk, CoqInE, …) or by **reflection inside the theory** via rewrite
rules. Dedukti's distinctive contribution is that the *conversion rule* can
absorb computation, so a reflective checker's evaluation is free (it happens in
conversion, not as explicit proof steps) — which is precisely the trick Rocq's
`ring`/`lia` use, generalized and made theory-parametric.

Lambdapi 3.0.0 is recent and healthy: releases 2.2.0 → 3.0.0 over several years,
most recent 3.0.0 on 16 July **[year unverified — the GitHub release list I
fetched rendered dates without years; 3.0.0 is plausibly 2025]**, with new
tactics (`eval`, `change`, `simplify rule off`), tacticals (`orelse`, `repeat`),
and a backend rewrite from Bindlib to **de Bruijn indices and closures** with a
substantial reported performance gain
([Deducteam/lambdapi releases](https://github.com/Deducteam/lambdapi/releases)).

## 3. What has actually been encoded — and how completely

Deducteam's own software page lists the live translator fleet
([Deducteam software](https://deducteam.gitlabpages.inria.fr/software.html)):
Dedukti, Lambdapi, **hol2dk** (HOL-Light → Dedukti/Lambdapi), **CoqInE**
(Rocq → Dedukti), **isabelle_dedukti**, **Krajono** (Matita → Dedukti),
**Agda2Dedukti**, **STTfaxport** (Dedukti → multiple targets), **lrat2dk**
(LRAT → Dedukti), **ZenonModulo**, **iProverModulo**, **ArchSAT**,
**SizeChangeTool**, **Logipedia**. Notably **Holide**, **Focalide**, and
**Universo** no longer appear on that page — consistent with quiet retirement of
the older generation. The reference paper claims Dedukti can express
"constructive and classical predicate logic, Simple type theory, programming
languages, Pure type systems, the Calculus of inductive constructions with
universes, etc." and has checked libraries from "Zenon, iProver, FoCaLiZe, HOL
Light, and Matita" ([arXiv:2311.07185](https://arxiv.org/abs/2311.07185)).

Completeness, by system, from strongest to weakest evidence:

### hol2dk (HOL-Light) — **this one is real, and it is the flagship**

hol2dk translates HOL-Light proofs to Dedukti, Lambdapi, **and Rocq**, with
concrete numbers:

- `hol.ml` base library: **5,687 theorems**
- Multivariate library: **40,728 theorems** (arithmetic, reals, complex
  analysis, topology, integration, measure theory)
- Logic library: unification, resolution, skolemization, Löwenheim–Skolem,
  compactness, Herbrand

and — the part that matters — the output is **shipped as opam packages**
(`coq-hol-light`, `rocq-hollight-logic`) with **semantic alignment**: HOL-Light
reals map to the Rocq standard-library reals, so the exported theorems compose
with native Rocq developments. Version **2.1.0 released 2025-11-20**, 280
commits, actively maintained ([Deducteam/hol2dk](https://github.com/Deducteam/hol2dk)).

This is the existence proof that the Dedukti pipeline can carry a
production-scale library end-to-end into a *different* system's idioms. It is
not a toy. It is also, notably, **HOL → Rocq**, i.e. simple type theory into
something richer — the easy direction.

### CoqInE (CIC) — real work, chronically incomplete

The CIC encoding is where the promise meets the wall. The record:

- The first CoqInE **ignored the universe hierarchy and universe subtyping
  entirely**; a later version added both, but "some other features such as the
  module system were still missing"
  ([Encoding Proofs in Dedukti: the case of Coq
  proofs](https://inria.hal.science/hal-01330980/document),
  [CoqInE paper](https://ceur-ws.org/Vol-878/paper3.pdf)).
- Universe polymorphism is structurally hard: CIC has infinitely many universes,
  so you cannot declare a constant per universe; restricting to the finitely many
  universes used in a module "is not modular", because definitions like `list`
  are polymorphic over all universes
  ([hal-01330980](https://inria.hal.science/hal-01330980/document)). The proposed
  fixes need universe *variables* in the encoding
  ([arXiv:2310.16595](https://arxiv.org/pdf/2310.16595)).
- Aspects "left aside" in the surveyed encodings include **impredicativity,
  η-equality, and propositional equality**
  ([hal-01330980](https://inria.hal.science/hal-01330980/document)).
- As of the **2024** activity report, CoqInE is still "mostly focused on
  implementing support for Coq universe polymorphism"
  ([Deducteam 2024](https://radar.inria.fr/report/2024/deducteam/index.html)).

Read that timeline. CoqInE dates to ~2012 (CEUR Vol-878). In 2024 it is *still*
working on universe polymorphism. **The CIC encoding is, after ~13 years, not a
finished artifact.** That is the single most damning fact for anyone hoping to
use Dedukti as a drop-in CIC/Lean substrate — and CIC is exactly the theory our
in-tree Lean kernel implements.

### The rest

- **Krajono** (Matita): the Matita arithmetic library was translated to
  constructive simple type theory and re-exported broadly — the Logipedia
  showpiece (below).
- **isabelle_dedukti**: alive; updated to **Isabelle 2025**, with "restored
  lambdapi output" and removal of old code
  ([CHANGES.md](https://github.com/Deducteam/isabelle_dedukti/blob/master/CHANGES.md)).
  "Restored" is a tell: it had bit-rotted.
- **Agda2Dedukti**: listed as maintained and operational
  ([Deducteam 2024](https://radar.inria.fr/report/2024/deducteam/index.html)).
- **Zenon Modulo** ([arXiv:1507.08719](https://arxiv.org/pdf/1507.08719)),
  **iProverModulo**, **ArchSAT** (an SMT/McSat solver emitting Dedukti/FOL
  proofs), **lrat2dk** (LRAT → Dedukti,
  [gburel/lrat2dk](https://github.com/gburel/lrat2dk)): the ATP/SMT side. These
  are the ones structurally closest to axeyum. They are research-grade, mostly
  single-author, mostly FOL.
- **Vampire → λΠ-modulo** exists as of 2025
  ([arXiv:2503.15541](https://arxiv.org/html/2503.15541)).
- **SMT proof reconstruction in Lambdapi** exists as a 2024/2025 EuroProofNet
  paper ([hal-04861898](https://inria.hal.science/hal-04861898/file/paper8.pdf)
  — **[unverified]**, the PDF returned Access Denied on fetch; I could not
  confirm which solver, which theories, or whether **bit-vectors** are covered.
  This is the single most important open question for section 5 and should be
  the first thing chased in a follow-up.)

**Bit-vectors in Dedukti: no evidence found.** The BV-proof literature that
surfaced is LFSC/CVC4-shaped
([DRAT-based Bit-Vector Proofs in CVC4](https://arxiv.org/pdf/1907.00087)), not
Dedukti-shaped. **[unverified]** but the absence is itself informative: if
Dedukti had a bit-vector theory carrying real cvc5-scale BV proofs, it would be
advertised, and it is not.

## 4. Logipedia — alive, but a beta that never grew up

Logipedia is the multi-system encyclopedia: a back-end translating Dedukti
proofs out to other systems, plus a website front-end where you search for a
theorem and download it in your system of choice
([about page](http://logipedia.inria.fr/about/about.php),
[Deducteam/Logipedia](https://github.com/Deducteam/Logipedia),
[arXiv:2305.00064](https://arxiv.org/abs/2305.00064)).

Export targets: **Coq, Matita, Lean, PVS, OpenTheory** directly, plus
**HOL Light, HOL4, Isabelle/HOL** via OpenTheory
([about page](http://logipedia.inria.fr/about/about.php)).

Achievements are real but *small and hand-picked*:

- **GeoCoq** exported to 7 systems: HOL Light, Lean, Matita, OpenTheory (⇒
  Isabelle/HOL, HOL4), PVS.
- The **Matita arithmetic library** translated into constructive simple type
  theory and thence to Coq, Lean, PVS, HOL Light, Isabelle/HOL.
- The canonical demo is **Fermat's little theorem** exported to Coq, Lean,
  Matita, PVS, OpenTheory ([arXiv:2305.00064](https://arxiv.org/abs/2305.00064)).

Status: the site says **"This is the beta version of Logipedia. In the long run,
more systems and more logic should be added"** ([about
page](http://logipedia.inria.fr/about/about.php)). The 2024 activity report
still lists it as operational
([Deducteam 2024](https://radar.inria.fr/report/2024/deducteam/index.html)). The
GitHub repo (780 commits, 65 stars, 11 forks, OCaml) is not archived and carries
open issues/PRs ([Deducteam/Logipedia](https://github.com/Deducteam/Logipedia)).
**[unverified]** I could not obtain a last-commit date or a total theorem count;
the fetches did not surface either.

**Read the mechanism, not the marketing.** The exports work because the content
was first pushed down into **constructive simple type theory** — a
least-common-denominator logic that every target can receive. That is the
"reverse mathematics" half of the Logipedia idea
([arXiv:2305.00064](https://arxiv.org/abs/2305.00064)): find the weakest theory
that proves the theorem, and then export is cheap. Export is *not* free for
arbitrary Dedukti content. Nobody exports a universe-polymorphic CIC development
to HOL Light, because that is impossible, and Logipedia does not claim to. The
"multi-prover export for free" story is real **only inside a fragment weak
enough that everyone agrees on it** — and that fragment is roughly
"constructive STT", not "whatever your solver actually proved".

## 5. Could axeyum emit Dedukti as its certificate format?

Live context: [ADR-0166](../../research/09-decisions/adr-0166-alethe-target-reassessment.md)
re-opened Alethe-vs-CPC because `lean-smt` consumes **CPC** and **cvc5's Alethe
output has no bit-vectors**. So: is Dedukti a third option?

**Mechanically, yes.** Nothing stops us. λΠ-modulo is expressive enough for our
content; you would define an axeyum theory (BV sorts, the bit-blasting relation,
the SAT-level resolution/RUP rules) as a Dedukti signature + rewrite system, and
emit terms in it. The pieces even rhyme with what we already have: **lrat2dk**
already turns LRAT into Dedukti ([gburel/lrat2dk](https://github.com/gburel/lrat2dk)),
which is exactly the shape of our DRAT/LRAT route, and there is a **Rust**
λΠ-modulo checker in Kontroli ([arXiv:2102.08766](https://arxiv.org/abs/2102.08766))
so an in-tree checker is not a fantasy.

**Strategically, no. Recommendation: do not adopt Dedukti as our certificate
format. Do steal its central idea, which we have already independently arrived
at.** Reasons, in order of weight:

1. **The "free multi-prover export" is not free and does not cover us.**
   Logipedia's exports go through constructive simple type theory
   ([about](http://logipedia.inria.fr/about/about.php),
   [arXiv:2305.00064](https://arxiv.org/abs/2305.00064)). A QF_BV bit-blasting
   certificate is not a theorem of constructive STT in any form Logipedia's
   pipeline consumes today, and **no Dedukti bit-vector theory with real BV
   proof content surfaced in this survey** — the BV-proof literature is
   LFSC/CVC4 ([arXiv:1907.00087](https://arxiv.org/pdf/1907.00087)). We would be
   the ones writing the BV theory, the BV export to each target, *and* its
   adequacy argument. That is not adopting an ecosystem; that is doing the whole
   job in someone else's file format. **The thing we would be buying is
   precisely the thing that isn't built.**
2. **It does not solve our actual problem, which is Lean.** Our target is
   `lean-smt`/Lean 4, i.e. **CIC**. Dedukti's CIC story — CoqInE — has been in
   progress since ~2012 and in 2024 is *still* working on universe polymorphism,
   with η, impredicativity, propositional equality, and the module system
   historically "left aside"
   ([hal-01330980](https://inria.hal.science/hal-01330980/document),
   [CoqInE](https://ceur-ws.org/Vol-878/paper3.pdf),
   [Deducteam 2024](https://radar.inria.fr/report/2024/deducteam/index.html)).
   Routing axeyum → Dedukti → Lean means betting our Lean story on the *weakest*
   link in the Dedukti fleet. We already have an in-tree Rust port of the Lean 4
   CIC kernel. Going through Dedukti to reach Lean would be strictly longer,
   strictly more fragile, and would *add* a TCB (Dedukti's theory + its
   confluence/termination side conditions + CoqInE's adequacy) rather than
   remove one.
3. **The TCB argument inverts.** Our pitch is "untrusted fast search, trusted
   small checking", with the trusted thing being a CIC kernel whose semantics
   are pinned by an existing, independently-implemented, heavily-exercised
   specification (Lean 4). Dedukti's kernel is small but its *theory files* are
   trusted-by-argument, and confluence/termination are discharged by external
   tools (CSI^HO, SizeChangeTool) or assumed
   ([Deducteam/Dedukti](https://github.com/Deducteam/Dedukti),
   [Deducteam 2021](https://raweb.inria.fr/rapportsactivite/RA2021/deducteam/index.html)).
   Adopting Dedukti trades "one well-understood kernel" for "small kernel + our
   own bespoke rewrite theory + two auxiliary meta-tools + an adequacy paper we
   would have to write". For a project whose hard rule is that semantics must be
   explicit before an operator becomes public surface, that is a downgrade.
4. **ADR-0166 is about a consumer, not a format.** The reason CPC is in play is
   that *`lean-smt` reads it*. Dedukti has no consumer we want. Emitting Dedukti
   would give us a format that a Lean user cannot use without a CoqInE-class
   bridge that does not exist for our fragment. It does not answer the question
   ADR-0166 asks.

**What we should take instead — and this is the useful half:**

- **Validation.** Dedukti is direct evidence that "tactic = untrusted procedure
  emitting a certificate + small parameterized checker" is a sound, buildable
  architecture, and that it scales: hol2dk carries **40,728 + 5,687 theorems**
  through it into shipped opam packages
  ([hol2dk](https://github.com/Deducteam/hol2dk)). Our design is **not**
  derivative — we are not proposing λΠ-modulo — but it is **not novel either**,
  and 01-itp-anatomy was right to flag it. Cite Dedukti as prior art; do not
  claim the idea.
- **The conversion-absorbs-computation trick.** Dedukti's real insight is that
  putting computation in the *conversion rule* makes reflective checkers cheap:
  the checker's evaluation costs nothing in proof size because it happens during
  conversion. Lean's kernel already has definitional unfolding + `Nat`/`String`
  GMP acceleration, so **we have this mechanism already**. Our reflective
  checkers (bit-blast replay, LRAT RUP checking) should be written to exploit
  kernel reduction rather than emitting step-by-step terms. This is the design
  lesson worth extracting, and it costs nothing to adopt.
- **lrat2dk as a shape reference** for our LRAT → kernel-term route
  ([gburel/lrat2dk](https://github.com/gburel/lrat2dk)), and **Kontroli** as a
  reference for a Rust checker with parallel conversion
  ([arXiv:2102.08766](https://arxiv.org/abs/2102.08766)).
- **One open thread worth chasing:** the SMT-proof-reconstruction-in-Lambdapi
  paper ([hal-04861898](https://inria.hal.science/hal-04861898/file/paper8.pdf),
  **[unverified]** — fetch blocked). If that work covers bit-vectors, point (1)
  weakens and Dedukti deserves a second look as an *additional* emit target. If
  it is FOL/UF-only, as the surrounding literature suggests, the conclusion
  above stands unchanged. Also **[unverified]**: whether EuroProofNet
  ([tools](https://europroofnet.github.io/tools/)) has since standardized a BV
  theory.

**Bottom line for ADR-0166:** Dedukti is a **third option that is worse than
both** current candidates for our purpose. Alethe and CPC each have a live
consumer and a live producer (cvc5); Dedukti has neither for QF_BV. Keep the
ADR-0166 decision between Alethe and CPC. Do not open a Dedukti lane.

## 6. Why hasn't Dedukti won? The graveyard

It has existed ~15 years, it is the obvious right answer to interoperability,
Inria funds it with ~20 people
([Deducteam 2024](https://radar.inria.fr/report/2024/deducteam/index.html)), and
it has displaced nothing. Why:

1. **Encoding is not translation, and the gap is permanent.** Getting a proof
   *into* Dedukti requires an encoding whose **adequacy** is a research paper,
   not a build step. Getting it *out* requires the target to accept the theory —
   which it generally will not unless you first weakened the content to a common
   fragment. Logipedia's exports work because everything is pushed down to
   constructive STT ([arXiv:2305.00064](https://arxiv.org/abs/2305.00064)); the
   moment content genuinely needs CIC universes or classical choice, the
   many-to-many export stops being a translation problem and becomes a
   *mathematical* one. **The hard part of interoperability was never the file
   format**, and a logical framework only solves the file format.
2. **The CIC encoding never finished.** ~2012 → 2024 and universe polymorphism
   is still the active work item
   ([CoqInE](https://ceur-ws.org/Vol-878/paper3.pdf),
   [Deducteam 2024](https://radar.inria.fr/report/2024/deducteam/index.html)),
   with η, impredicativity, propositional equality, and modules historically out
   of scope ([hal-01330980](https://inria.hal.science/hal-01330980/document)).
   Coq/Rocq and Lean are where the mass of formalized mathematics lives. A
   universal substrate that cannot faithfully round-trip the two biggest
   producers is not universal, and the community correctly declined to build on
   it.
3. **Nobody's incentive points at it.** A logical framework is *pure
   infrastructure*: it has no users of its own, only users-of-users. Coq/Rocq,
   Lean, Isabelle, and HOL Light each have a self-sufficient community, a
   library, and a tactic culture. None of them gets a feature by adopting
   Dedukti; they get a dependency, an extra TCB, and a translation-maintenance
   burden. Dedukti's value is a **network effect that requires the network to
   move first**, and no member of the network is paid to move. This is the
   central reason, and it is sociological, not technical.
4. **The translators rot.** They are per-source-system, per-version, mostly
   single-author, and they track a moving upstream. `isabelle_dedukti`'s changelog
   literally records **"restored lambdapi output"** after bumping to Isabelle
   2025 ([CHANGES.md](https://github.com/Deducteam/isabelle_dedukti/blob/master/CHANGES.md)).
   **Holide, Focalide, and Universo — all named in our 01-itp-anatomy note as
   precedents — no longer appear on the Deducteam software page**
   ([software](https://deducteam.gitlabpages.inria.fr/software.html)), though
   Universo shipped with Dedukti 2.7 as recently as 2022. n translators × m
   upstream release cadences = an unfunded maintenance treadmill, and it is
   losing.
5. **Cadence.** Dedukti's last tagged release is **2.7, June 2022**
   ([Deducteam/Dedukti](https://github.com/Deducteam/Dedukti)) — four years, for
   the *reference checker of the framework*. Energy has visibly migrated to
   **Lambdapi** (3.0.0, active, tactics, LSP,
   [releases](https://github.com/Deducteam/lambdapi/releases)) and to **hol2dk**
   (2.1.0, Nov 2025, [hol2dk](https://github.com/Deducteam/hol2dk)). That is a
   telling drift: the team's live output is a *proof assistant* and a *point-to-
   point HOL-Light→Rocq translator* — i.e. they are succeeding at exactly the
   things that are **not** "universal substrate". hol2dk is great work and its
   value proposition is "HOL-Light theorems, usable in Rocq" — a bilateral
   bridge that happens to route through Dedukti. Users want the bridge; the
   substrate is plumbing.
6. **Performance was a real drag.** Kontroli exists because Dedukti was slow
   enough that a faster reimplementation was a publishable contribution, with up
   to 6.6× on the dominant phase using 8 threads
   ([arXiv:2102.08766](https://arxiv.org/abs/2102.08766)). Kontroli itself is a
   2021/2022 research artifact, not an ecosystem replacement **[unverified: its
   current maintenance status]**.
7. **Logipedia stalled at beta.** Still self-described as "the beta version…
   In the long run, more systems and more logic should be added"
   ([about](http://logipedia.inria.fr/about/about.php)). Fermat's little theorem
   and GeoCoq are lovely demos and *demos are what it has*. Compare: Lean's
   Mathlib. The encyclopedia never reached the mass where using it beats
   reproving.

**The honest summary: Dedukti is not a graveyard — it is a well-funded, alive,
technically-sound research program that produced one genuinely valuable
artifact (hol2dk) and did not achieve its stated goal.** The failure is not of
execution or of the calculus. It is that **a universal substrate's value is
proportional to adoption, adoption is proportional to encoding fidelity,
encoding fidelity for CIC is a 13-year research problem, and no downstream
system has any incentive to wait.** Around it sit the actual graveyard markers:
Holide, Focalide, Universo, and the endless per-system translator treadmill.

The lesson for us is specific: **do not build the universal thing. Build the
bilateral bridge that someone actually wants.** For axeyum that is
axeyum → (Alethe|CPC) → `lean-smt` → Lean, and it is exactly what ADR-0166 is
already arguing about. hol2dk succeeded by being a bridge, not a substrate. Be
hol2dk.

## 7. Metamath Zero

**What it is.** MM0 (Mario Carneiro) is "a language for writing specifications
and proofs" that balances "simplicity of verification and human readability" —
Metamath without verification gaps, interpretable as a subset of HOL, at
Metamath-like checking speed ([digama0/mm0](https://github.com/digama0/mm0);
[Metamath Zero: Designing a Theorem Prover
Prover](https://dl.acm.org/doi/10.1007/978-3-030-53518-6_5), CICM 2020;
[arXiv:1910.10703](https://arxiv.org/pdf/1910.10703);
[thesis](https://digama0.github.io/mm0/thesis.pdf)).

**Architecture — and it is *our* architecture.** MM0 is built on a sharp
separation between **proof producers** and **proof consumers**. A producer may
do anything it likes — tactics, higher-order unification, calling external
solvers — but the artifact it emits is a self-contained binary **MMB
certificate** that a small dedicated verifier checks independently. This is the
certificate-first goal layer, stated cleanly, by the person who thought hardest
about minimal TCB.

**TCB.** The design criterion is that the verifier be "small enough to fit in one
person's head, and to be plausibly audited end-to-end", and once correct, never
need to change ([FOMM 2020
slides](https://www.andrew.cmu.edu/user/avigad/meetings/fomm2020/slides/fomm_carneiro.pdf)).
`mm0-c` is the "bare bones MM0 verifier, intended for formalization", written in
C ([digama0/mm0](https://github.com/digama0/mm0)). **[unverified]** I did not
obtain an authoritative LoC figure; the commonly-cited "~2–3 kLoC of C" for
`mm0-c` should be checked against the repo before we quote it anywhere.

**Speed.** MM0 holds the record for fastest verification of set.mm (ZFC,
including 71 of Wiedijk's 100 targets) at **under 200 ms** — a number worth
internalizing: a whole ZFC library, checked in a fifth of a second. Compact
certificates + a dumb fast checker beats clever elaboration.

**Bootstrap — the ambition, and its status.** The goal is "a formally verified
(in MM0) verifier for MM0, down to the hardware": `x86.mm1` formalizes the x86
architecture, `verifier.mm0`/`.mm1` state the implementation-correctness
theorem, and the intent is to base a bootstrap chain for more complicated
compilers and verifiers, "possibly including metamath itself". **But the
completed x86 bootstrap is not there**: `verifier.mm1` is noted as forthcoming
work ([digama0/mm0](https://github.com/digama0/mm0)). Components: `mm0-c` (C
verifier), `mm0-rs` (**Rust** compiler + LSP server), `mm0-hs` (Haskell,
**deprecated**), `mm0-lean` and some MM1 implementations marked WIP. Activity is
"active but limited" ([digama0/mm0](https://github.com/digama0/mm0)).
**[unverified]** last-commit date; a 2025 search hit referring to components
"written in zig… compiled to WebAssembly" could not be attributed to MM0 and may
belong to a different project — **do not repeat that claim**.

**MM0 vs Dedukti as a substrate.**

| | Dedukti | MM0 |
|---|---|---|
| Foundation | λΠ-calculus modulo rewriting (LF + rewrite rules) | Metamath-style, interpretable as a subset of HOL |
| Kernel trust | small kernel, **but** theory file + external confluence/termination + adequacy | small verifier; axioms in `.mm0` spec file are the trusted statement |
| Parameterization | rewrite system defines the theory | `.mm0` spec declares sorts/axioms; `.mmb` proves against it |
| Certificate | elaborated λΠ term (text `.dk`) | compact **binary** `.mmb` |
| Speed | Kontroli existed *because* Dedukti was slow | set.mm in <200 ms |
| Export to other ITPs | Logipedia (beta, via constructive STT) | essentially none |
| Bootstrap | none | verified-verifier-to-x86 **[incomplete]** |
| Maintenance | Dedukti 2.7 = 2022; Lambdapi/hol2dk active | active-but-limited, one principal author |

They optimize different things. **Dedukti buys theory-parameterization and (in
principle) interoperability, at the cost of a TCB that includes your rewrite
theory and its meta-theory. MM0 buys a genuinely minimal, auditable, absurdly
fast checker with a producer/consumer split, at the cost of no interoperability
story and a bus factor of ~1.**

**For our minimal-TCB argument, MM0 is the citation, not Dedukti.** MM0's
producer/consumer separation *is* our certificate-first thesis and we should
cite it as such — it is the strongest published statement of it. But MM0 is not
adoptable for us either, and for the mirror-image reason to Dedukti: our
consumer is Lean/CIC, and MM0 deliberately targets a subset of HOL with no path
to it. We should take **the argument** (small consumer, arbitrary producer,
compact binary certificate, checking speed as a first-class design goal) and
leave **the artifact**.

Two concrete borrowings worth acting on:

1. **Binary certificates, not text.** MM0's `.mmb` is binary and it is why
   set.mm checks in 200 ms. Our certificate format should be a compact binary
   with a text debug rendering — not the reverse. Alethe/LFSC being text is a
   cost, not a feature.
2. **Checking speed as a design gate.** MM0 treats verifier throughput as a
   headline property. We should have a number for "time to kernel-check the
   corpus" in STATUS.md and defend it, the same way we defend PAR-2.

---

## What this implies for axeyum

**(5) Should we emit Dedukti? No.** Not as a replacement for, nor alongside,
Alethe/CPC.

- The multi-prover export via Logipedia is **not free and does not reach our
  content**: it is a beta ([about](http://logipedia.inria.fr/about/about.php))
  whose exports work by first weakening everything to constructive simple type
  theory ([arXiv:2305.00064](https://arxiv.org/abs/2305.00064)), and **no
  Dedukti bit-vector theory carrying real BV proofs surfaced anywhere in this
  survey** — the BV proof literature is LFSC/CVC4
  ([arXiv:1907.00087](https://arxiv.org/pdf/1907.00087)). We would write the BV
  theory, every export, and the adequacy argument ourselves. The thing we'd be
  buying is the thing that isn't built.
- It **doesn't reach Lean**, which is the whole point. CoqInE has been chasing
  CIC universe polymorphism since ~2012 and was still chasing it in 2024
  ([Deducteam 2024](https://radar.inria.fr/report/2024/deducteam/index.html));
  η, impredicativity, propositional equality, modules have all been "left aside"
  at various times ([hal-01330980](https://inria.hal.science/hal-01330980/document)).
  We already have an in-tree Rust Lean 4 CIC kernel. Dedukti-to-Lean would be a
  longer path through a weaker link.
- It **grows the TCB**: small kernel *plus* our rewrite theory *plus*
  external confluence (CSI^HO) and termination (SizeChangeTool) checks *plus* an
  adequacy proof ([Deducteam/Dedukti](https://github.com/Deducteam/Dedukti)).
  That is the opposite direction from "trusted small checking".
- **ADR-0166 stands unchanged.** The Alethe-vs-CPC question is about which
  format a live consumer (`lean-smt`) reads. Dedukti has no consumer we want.
  Keep the decision binary; do not open a Dedukti lane. *(One caveat that could
  move this: the Lambdapi SMT-reconstruction work
  ([hal-04861898](https://inria.hal.science/hal-04861898/file/paper8.pdf)) is
  **[unverified]** — fetch blocked. If it covers bit-vectors, revisit as an
  additional emit target, never as the primary.)*

**What we take instead:** our design is **prior-arted, not derivative**. Dedukti
and MM0 both independently validate "untrusted producer + small parameterized
checker", and hol2dk proves it scales (**46k+ theorems** into shipped opam
packages, [hol2dk](https://github.com/Deducteam/hol2dk)). Cite them; don't claim
the idea. The transferable techniques are (a) **conversion absorbs computation**
— write our reflective checkers to lean on Lean-kernel reduction rather than
emitting step-by-step terms; (b) **binary certificates** (MM0's `.mmb`, set.mm
in <200 ms) rather than text; (c) **checking throughput as a defended metric**;
(d) **lrat2dk** and **Kontroli** (a Rust λΠ-modulo checker,
[arXiv:2102.08766](https://arxiv.org/abs/2102.08766)) as implementation shape
references.

**(6) Why Dedukti hasn't won — the load-bearing lesson.** Not because it's
wrong; it is well-funded (~20 people at Inria), alive, and technically sound.
It hasn't won because **a universal substrate's value scales with adoption,
adoption scales with encoding fidelity, CIC fidelity has been a 13-year research
problem, and no downstream system is paid to wait.** Infrastructure with no
users of its own, only users-of-users, needs the network to move first, and the
network never does. Meanwhile the translator fleet rots on an unfunded
treadmill (`isabelle_dedukti` "restored lambdapi output" after an Isabelle bump;
**Holide, Focalide, Universo have fallen off the software page** — and those
were three of the precedents our own 01-itp-anatomy cited). Dedukti's own
reference checker last tagged **2.7 in June 2022**, while the team's live energy
went to Lambdapi (a proof assistant) and hol2dk (a *bilateral bridge*).

**That is the directive for us: do not build the universal thing; build the
bridge someone wants.** hol2dk won by being HOL-Light→Rocq with real semantic
alignment, not by being universal. Our equivalent is
axeyum → (Alethe|CPC) → `lean-smt` → Lean — one bridge, one consumer, real
alignment. Resist every temptation to generalize the certificate format before
that bridge carries load. A format with two producers and one consumer that
works beats a substrate with fifteen encodings that almost do.

**(7) MM0 is our minimal-TCB citation.** Its producer/consumer split is our
thesis stated by the person who thought hardest about it, and set.mm in <200 ms
is the empirical case that compact certificates + a dumb fast checker wins. Take
the argument and the two engineering consequences (binary certificates; checking
speed as a gate). Leave the artifact: it targets a subset of HOL, has no Lean
path, no interop story, an incomplete x86 bootstrap, and a bus factor of ~1
([digama0/mm0](https://github.com/digama0/mm0)).

### Open threads (for a follow-up pass)

- **[unverified]** Does [hal-04861898](https://inria.hal.science/hal-04861898/file/paper8.pdf)
  ("Reconstruction of SMT proofs with Lambdapi") cover bit-vectors, and which
  solver/format does it consume? Fetch was blocked. **This is the one finding
  that could move conclusion (5).**
- **[unverified]** Dedukti kernel LoC and Kontroli LoC (Kontroli PDF text
  extraction failed) — needed if we quote comparative TCB sizes.
- **[unverified]** `mm0-c` LoC; MM0 last-commit date; the "zig/WebAssembly"
  claim from a 2025 search hit could not be attributed to MM0 — **do not repeat
  it**.
- **[unverified]** Logipedia last-commit date and total theorem count.
- **[unverified]** Kontroli's current maintenance status.
- **[unverified]** Whether EuroProofNet ([tools](https://europroofnet.github.io/tools/))
  has standardized a BV theory for Dedukti/Lambdapi since 2024.
