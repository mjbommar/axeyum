# Critique — Iteration 2 (adversarial, against the "no")

Targets: [`../design/00-thesis.md`](../../design/00-thesis.md) (v2),
[`../plan/README.md`](../../plan/README.md) (v2),
[`../DIARY.md`](../DIARY.md).

Round 1 attacked a draft arguing **for** a prover and returned MAJOR REVISION.
The author rewrote the thesis to say **do not build one**. This document attacks
the "no".

The specific risk under review is **over-correction**. Round 1 was adversarial
*by construction* — it says so in its own first paragraph (`iteration-1.md:6-9`:
"This document does not attempt balance… the draft's authors should answer it,
not agree with it"). The author agreed with it. Every numbered finding F1–F10 is
conceded in v2, several verbatim. An author who accepts 100% of an adversary's
findings has not reasoned; they have capitulated. A "no" is cheaper to defend
than a "yes", which is exactly why it needs to be attacked harder.

---

## G1 — The 0%-column concession is over-conceded, and the refuting evidence is in this repo, unmeasured

**Claim attacked** (`00-thesis.md:29-36`):

> **False.** The 0% rows are `lia-cvc5-regress-clean-quantified` (**0/12, PAR-2
> 30.0 — every instance times out**) and quantified UF (0/5). Those are **loop
> invariants and callee abstraction** — software verification's bread and butter,
> not mathematics. […] I read past it. This is the "fell in love with a
> narrative" failure, and it was the load-bearing claim.

This is the single largest retraction in v2 — it is what turns "the market is our
strong column" into "a shell over a hole", which is what makes the whole document
say no. It is **half wrong, and the author had the evidence to know it.**

**Round 1 conflated a fragment with a mechanism.** "Loop invariants" is not a
quantified-LIA *decision* problem. It is an invariant *synthesis* problem. The
standard route — PDR/IC3, IMC — synthesizes a candidate and discharges
initiation/consecution/safety as **quantifier-free** queries. This repo has that
route, in tree, today:

- `crates/axeyum-solver/src/pdr_lia.rs:43` and `pdr_lra.rs:35` — "`verify_invariant`,
  run before any `Safe` is returned: the candidate…"
- `pdr_lia.rs:716`, `pdr_lra.rs:694` — the gate is called on the return path.

So the inference "quantified LIA is 0/12 ⇒ loop-invariant obligations are
undecidable for us" **does not follow**, and the `lia-cvc5-regress-clean-quantified`
row is not evidence for it. Quantified UF (0/5) survives as a real hit — callee
abstraction over uninterpreted infinite carriers genuinely lives there — but that
is one row of five instances, not "software verification's bread and butter."

**The author saw this and let the concession stand anyway** (`00-thesis.md:46-51`):

> One honest nuance in our favour, which the critique's framing also overstates:
> PDR/IMC **synthesize** invariants and discharge each obligation with a
> quantifier-free query gated by `verify_invariant`. So the invariant route does
> not necessarily require deciding quantified LIA. That is a real asset and it is
> measured — but it is married to `TransitionSystem` (`bmc.rs:47-72`), and nobody
> has shown it covers the obligations a goal layer would face.

Read the structure of that paragraph. It correctly identifies that **the
critique's framing is overstated**, correctly names the mechanism, correctly
notes the asset is *measured* — and then demotes itself to "one honest nuance"
and hands the verdict back to the critique on an *unmeasured* objection ("nobody
has shown it covers…"). The unmeasured objection is doing the same work here that
"88–100% coverage" did in draft 1: an unmeasured claim decides the document. Draft
1 assumed in its favour; v2 assumes against. **That is not a correction. That is
the same error with the sign flipped**, and the sign flipped toward the reviewer.

The tell is that the concession is graded by *who said it*, not by *what is true*.
The correct disposition of a nuance that shows an adversary's framing is
overstated is to shrink the adversary's finding, not to file it as a footnote
under a retraction that keeps the adversary's conclusion.

**What would have to be true.** For the 0% column to be the binding constraint on
a goal layer, someone must show that real obligations *escape* the PDR/IMC route —
i.e. that they need quantified LIA decided directly rather than invariants
synthesized. **That is a measurement, it is cheap, and G1.2 does not currently
run it.** `plan/README.md:110-112` lists it as "Unmeasured: whether PDR/IMC's
invariant route… covers the gap." Good — but it is listed as a bullet under a
gate whose *fire condition* (`<40%`) is defined without it. G1.2 must measure the
PDR route explicitly, and until it does, `00-thesis.md:29-36` should read "round
1's framing was overstated; the mechanism question is open" — not "**False.** […]
I read past it."

**Verdict on this finding: the retraction is over-conceded.** Quantified UF stands;
"loop invariants" does not.

---

## G2 — The number v2 kept is as cherry-picked as the one it retracted

**Claim attacked** (`00-thesis.md:43`, and `plan/README.md:107-109`):

> | Finite / bounded domains | **strong** — quantified BV **54/54 = 100%**, QF_AX/QF_DT/QF_FP/QF_UFBV 100%, QF_BV ~2× Z3 |

v2's entire "encouraging" column — and the strongest available rebuttal to G1's
own market objection ("crypto/codec/serialization obligations are BV, and
quantified BV is 100%") — rests on `54/54`. Check what it means
(`docs/research/08-planning/capability-matrix.md:82`):

> checked query-scoped QF_BV **positive-universal** instance sets … bounded CEGIS
> may select complete positive-universal Bool/BV source instances, but candidate
> models, quantifier erasure, and instance selection remain **search-only** …
> validates 1 through 256 unique complete typed binding tuples … **General QSAT,
> negative quantifier contexts, existentials, functions/arrays, free BVs in
> quantified assertions, mixed arithmetic, wasm proof export, and broader Lean
> reconstruction remain open**

So "quantified BV 54/54 = 100%" means: *a 54-instance committed slice, restricted
to positive-universal quantification, no existentials, no negative quantifier
contexts, no functions or arrays, no free BVs under a quantifier, no mixed
arithmetic.* Note 08 itself sources it to a **committed regression corpus**
(`SCOREBOARD.md:28`), not to real obligations.

Round 1's F4 was precisely this attack: "100% rows are committed regression
corpora (`SCOREBOARD.md`), not real obligations. Presenting a 7/8 regression-suite
pass as a market-sizing datapoint is not calibration" (`iteration-1.md:164-168`).
v2 accepted F4 in full — and then **re-committed F4's error on the row that
survived**, in a table headed "What is actually true". `54/54` is quoted as a
capability. It is a corpus score on a fragment carve-out.

This cuts both ways and both cuts land:

1. Against v2's rigour: the document that retracts a cherry-pick republishes one
   two paragraphs later, in the table that replaces it.
2. Against anyone (including me) who would rebut G1 with "but crypto is BV and
   quantified BV is 100%": that defence is **not available on this evidence**.
   Crypto obligations involve arrays and existentials constantly. The
   capability-matrix line excludes both.

**What would have to be true.** Either the table cites `54/54` with its carve-out
attached ("positive-universal, no arrays/existentials, committed slice"), or it
drops the number and waits for G1.2. Same remedy round 1 prescribed
(`iteration-1.md:170-171`): "the sentence must be deleted, not softened."

A minor instance of the same habit: **"the trusted-reduction ledger — 6 of 14
entries open"** (`00-thesis.md:160`, `:194`; `plan/README.md:143`) appears only in
v2's own documents. `docs/plan/track-3-proof-lean/P3.0-trust-ledger.md` states the
`TrustId` enum's *purpose* (`:17-27`) but no `6/14`; ADR-0035:63 supports "the 6th
hole" for `XorGaussian`. The `/14` denominator has no citation anywhere in the
corpus. v2 introduces a fresh uncited number in the act of condemning draft 1 for
unsourced figures (`plan/README.md:21-22`). Cite it or count it.

---

## G3 — "The prover is the last 10%" is invented, and v2 contradicts it on the facing page

**Claim attacked** (`00-thesis.md:170-171`, and `plan/README.md:149-150`):

> The ambitious reading of this track's result: **the prover is the last 10%, and
> the first 90% is theory and trust work already in the plan.** That is not a
> retreat from ambition. It is a refusal to build the visible part first.

And (`00-thesis.md:165-166`):

> Close those and a goal layer becomes thin, cheap, and obviously worth building —
> possibly a few thousand lines over automation that already decides the goals.

**There is no evidence for this anywhere in the corpus, and v2 knows it.** Three
refutations, two of them from v2 itself:

1. **`plan/README.md:122-128`** — v2's own Gate 2 sizing:

   > the phases would be roughly: CIC↔IR bridge (**XL**, and the crux) →
   > goals/holes (**L** — note 01 settles that metavariables are *unavoidable*
   > for goal-directed proof, so this is not cheap) → certificate-first tactics
   > (**L**) → spec surface (**L**…).
   > **Estimated cost if re-entered: multiple person-years.**

   A document cannot size the goal layer at **XL + L + L + L = multiple
   person-years** on page 4 and call it "thin, cheap… possibly a few thousand
   lines" and "the last 10%" on page 5. These are the same object. One of the two
   sentences is false, and the honest one is the one with the sizing attached.

2. **Note 01 (`01-itp-anatomy.md:858`)**: "**Metavariables are unavoidable;
   *dependent* metavariables are a choice.**" v2 quotes this correctly in its
   closing section (`00-thesis.md:219-222`) and draws the right conclusion —
   "That makes P6.2 bigger than draft 1 assumed and removes the last reason to
   believe the goal layer was cheap." **The document contains its own refutation
   of "the last 10%", 50 lines below it, and does not notice.**

3. **The 0% column closing does not make a goal layer thin.** The claim is that
   the blockers are *upstream* — theories, ledger, `sat` lifting. But none of the
   three blockers is a goal layer's *content*. A CIC↔IR bridge, metavariable
   handling, hole management, tactic certificates, and a spec surface are not
   produced by fixing quantified LIA. Closing the 0% column changes the goal
   layer's **hit rate**, not its **size**. Conflating those is exactly the move
   draft 1 made in the other direction.

**Why this matters more than a slip.** "The last 10%" is doing rhetorical work: it
converts *no* into *later*, which lets the document claim it is "not a retreat
from ambition" (`00-thesis.md:170-171`) without paying for the claim. It is the
one sentence in v2 that a reader will remember, it is the one sentence with no
citation, and it is contradicted by the sentence with the sizing in it. Draft 1's
sin was a load-bearing claim written to be approved. **This is the same sin
written to be admired.**

**What would have to be true.** Either delete it, or replace with what v2's own
Gate 2 says: *"If the blockers close, the goal layer is still multiple
person-years and still fronts an XL CIC↔IR crux. The blockers change whether it
would work, not whether it is cheap."* That sentence is defensible and it is less
flattering, which is why it is the right one.

---

## G4 — The redirect is sound, but it is sold on a definition the repo does not use

**Claim attacked** (`00-thesis.md:157-159`, `plan/README.md:142`):

> 1. **The 0% column** — quantified LIA/UF over infinite domains. A goal layer over
>    a solver that times out on every loop-invariant obligation is a shell over a
>    hole. This is Track 2 (theories) and it is already on the roadmap.

The challenge to answer here is: *if the 0% column is research-hard and may never
close, then "the prover is blocked on it" means "never", and the document should
say so.*

**It is not research-hard, and the document is right to sequence rather than
refuse — but for a reason it never states.** `docs/plan/00-north-star.md:33-36`:

> **Honest unknown on the undecidable** — for semidecidable/undecidable fragments
> (full NRA without CAD, general quantifiers), parity means matching Z3's
> *practical* decide-rate and heuristics, with `unknown` first-class. We do not
> claim to "solve the halting problem"; we claim to match the **engineering**.

So the target is *not* "decide quantified LIA" — it is "match Z3 on quantified
LIA". Z3 is nowhere near 0% there; it uses E-matching and MBQI, which are
published, understood, and roughly two decades old. **Going 0/12 → competitive is
engineering, not open research.** The redirect is therefore genuinely achievable
and "blocked on Track 2" is a real sequencing claim, not a euphemism for never.

**But this rescue is fatal to G3's framing.** If the blocker is standard
engineering that Z3 shipped in 2009, then it is not "the first 90%" of anything —
it is a known implementation task on the roadmap. v2 needs the blockers to be
*hard* to make "the prover is the last 10%" sound like wisdom, and needs them to
be *tractable* to make the redirect honest. **They cannot be both.** They are
tractable. Which means the redirect stands and the 90/10 framing falls — again
(see G3).

**Credit where due, against the charge in the brief.** K4 (`00-thesis.md:206`) —
"Quantified LIA remains **0%** after Track 2's next phase → the redirect failed;
a goal layer stays unbuildable. Re-open only on evidence" — is a real gate with a
real trigger and a real observer. It is the best-constructed criterion in either
draft, and it is precisely the criterion that would catch "the redirect was a
polite never." Round 1's F8 said the criteria could not fire. K4 can. That is an
earned repair.

---

## G4b — On responsiveness: the redirect respects the instruction; the *report* does not

**Claim attacked** (`00-thesis.md:151-153`):

> The instruction that shaped this track was that *narrow scoping is bad*. Agreed —
> so the redirect is not "do less," it is **"do the hard thing instead of the
> shell."**

The user's framing was: *"lean compatibility is good, lean copying or narrow
scoping is bad."*

**On copying: v2 is the most responsive document in the track.** Round 1's F7
showed draft 1's phase list *was* the ITP lower half with humans deleted
(`iteration-1.md:258-286`), and the diary had already named the failure
(`DIARY.md:143-146`: "the research prompts were shaped around 'what does Lean have
that we lack,' which silently defines success as catching up to a 2015 design").
Redirecting to P3.7 (be Lean's backend) + Track 2 (theories) is *more* Lean-
compatible and *less* Lean-copying than building a parallel goal layer. The
instruction is satisfied on this axis, not evaded. The charge that "go do theory
work" is narrow-scoping by another route does **not** land: quantified LIA/UF and
`sat`→CIC lifting are strictly harder and broader than an MCP server.

**On narrow scoping, one thing does land: the report is narrower than the
finding.** `plan/README.md:152-167` ("What this track produced") lists five items
and books three of them elsewhere. That is honest about credit and *silent about
scope*: it never says what the track's own remaining surface is. The result is a
document that recommends against a track by dissolving it, rather than by bounding
it. "Do not open Track 6" and "here is the S/M-sized thing Track 6 is" are both
available conclusions; v2 asserts the first without pricing the second, even
though it sized that second thing itself (`plan/README.md:80-81`, S/M). The
correct verdict may well be "Track 6 is one S/M task inside Track 3" — that is a
scoping answer, and v2 declines to give one.

---

## G5 — K1 is rigged, in the same shape as draft 1 and pointing the other way

**Claim attacked** (`00-thesis.md:203`, K1):

> The agent-surface experiment (S4) shows a `lean4check`-shaped loop within **5
> points** of a rich surface on the same obligation set → The surface is not the
> product. Prover question closes **permanently**.

And the calibration (`plan/README.md:93-95`):

> `lean4check` + Claude Code reaches **87% on 189 proof-engineering tasks with one
> tool**, and AxProverBase's own ablation ranks iterative refinement ≫ memory ≫
> tools ("marginal").

Now read the author's own note 05 (`05-education-and-agentic.md:462-464`):

> *(Inference)* The defensible synthesis: **a good agent surface is worth little
> for mechanical tasks and a lot for search-heavy ones.** We should not claim the
> former.

**The baseline's 87% is on *proof-engineering* tasks — mechanical repair.** Note
05 says the rich surface is *known to lose* there. So K1, as calibrated, anchors
the experiment on the workload class where the author's own research predicts the
surface loses, and then fires **permanently** on that result. That is not a
falsification test; it is a confirmation with a stopwatch.

The asymmetry is visible in the two branches (`plan/README.md:86-91`):

| Branch | Condition | Qualifiers |
|---|---|---|
| **Close forever** | "the loop lands within 5 points" | *none* — no workload class named, no obligation set named |
| **Evidence for a goal layer** | "the surface wins **decisively** on a **search-heavy** workload" | two |

One branch requires a numeric threshold on an unspecified set. The other requires
"decisively" (undefined) **and** a workload class (correctly specified). **The
"no" branch is strictly easier to trigger than the "yes" branch, and only the
"no" branch is permanent.** Round 1's F8 attacked draft 1 for criteria that could
not fire; v2 built one that fires almost regardless of result. This is the mirror
image of the same defect, and it is worse in one respect: draft 1's rigging was
detectable by a hostile reviewer, whereas a gate rigged toward "no" reads as
rigour.

**What would have to be true.** K1 must specify the obligation set **before** the
run, and it must be search-heavy — because that is the only class where note 05
says the question is live. A `lean4check` loop matching a rich surface on
mechanical repair is **already known** from the 87% datapoint; running an
experiment to rediscover it and then closing the question "permanently" on the
result is spending weeks to launder a prior. Add: "if the obligation set is
mechanical, K1 does not fire — it was never in question."

Also strike "permanently". No experiment of size S closes a question forever, and
the word is doing the same work "the last 10%" does in G3 — buying finality on
credit.

---

## G6 — Gate 0 is laundering unless someone signs for it

**Claim attacked** (`plan/README.md:28-30`, and `:164-167`):

> ## Gate 0 — unconditional, and none of it is Track 6
> These proceed regardless of any prover decision. **Each has an owner track.**
> […]
> Items 3 and 4 are worth more than the question that surfaced them. That is a
> normal and good outcome for a research track, and it is the argument for running
> more of them.

Round 1's F9 said: book P6.0 to Track 3, and "if Track 6's net contribution to
date is a research corpus and a thesis, say that" (`iteration-1.md:345-347`). The
author complied — and then applied the same move to **all three** surviving items
(G0.1 kernel hardening → Track 3; G0.2 Alethe/CPC → Track 3; G0.3 `sat` trust →
Track 1/4). The result is a structure round 1 did not ask for and should be
attacked on its own terms:

**Every item of value is assigned to a track that has not accepted it, by a track
that is closing.** "Each has an owner track" is false as written. An owner is a
person and a date. What v2 has is a *routing label*. And the document knows this,
because it says so about its own most important item (`plan/README.md:61-62`):

> This is worth more than everything Track 6 proposed and it is being made **by
> inertia right now**.

A document that correctly diagnoses a decision being made by inertia, and whose
remedy is to hand that decision to a different track with no owner, no date, and
no ADR number, **has left it to inertia**. G0.2 is sized **S** — "S (decision)"
(`plan/README.md:47`). It is a decision this track has the evidence to make and
the standing to file: `lean-smt` uses CPC, cvc5's Alethe has no bit-vectors, QF_BV
is our strength, and P3.2 is the declared keystone. Three options are already
enumerated and all three are defensible (`plan/README.md:54-59`). **Writing an ADR
that states the three options and forces the choice is within this track's reach
and should not survive it as a hand-off.**

So: is Gate 0 legitimate, or is it a way to claim value while recommending
against the track? **Both, and that is the problem.** The credit-booking is
correct (round 1 was right; P0 belongs to Track 3). But the *work-routing* is not
the same act as the credit-booking, and v2 performs them with one gesture. The
honest version separates them:

- **Credit**: Track 3's. Agreed, unconditionally.
- **Work**: unowned as of this document. If nobody picks up G0.1/G0.2/G0.3, the
  track's claimed output is a corpus, a classification rule, and two unfiled
  findings — and `plan/README.md:163` ("A measured 'no'… with the conditions under
  which it reopens") is the only item that actually exists.

**What would have to be true.** Before this track closes: G0.2's ADR is *filed*
(it is S), and G0.1/G0.3 appear in Track 3's and Track 1/4's task tables with
sizes, or they are recorded as **found and dropped**. A "no" that offloads its
value to tracks that did not ask for it and cannot be shown to have received it
produces zero. That is not honesty; it is an accounting entry.

The `sat` gap (G0.3) deserves one further note in v2's favour: it is real, it is
correctly identified as the sharpest unmitigated risk (note 08:569-572 says so
independently), and v2 is right that it is owed by **P3.7's** future too, not just
a prover's (`plan/README.md:70`). That is the single most valuable sentence in the
document, because it is the one finding that survives *every* branch of the
decision.

---

## G7 — Claims that survived: checked

| Claim | Location | Status |
|---|---|---|
| Quantified BV **54/54 = 100%** | `00-thesis.md:43` | **True but materially incomplete.** Sourced (`08:56,258,588` → `SCOREBOARD.md:28`). But `capability-matrix.md:82` scopes it to positive-universal, query-scoped, no existentials/arrays/functions/free-BVs/mixed-arithmetic, committed slice. See G2. |
| Quantified LIA **0/12, PAR-2 30.0**; quantified UF **0/5** | `00-thesis.md:29-30` | **True.** `08-solver-automation-assets.md:38` and `:54-60` confirm verbatim, incl. PAR-2 30.0 = all timeouts. |
| "The 0% rows are exactly the fragments a prover lives in" | `00-thesis.md:32-33` | **Quoted accurately** (`08:56-60`). But note 08's *inference* from it is what G1 attacks, and note 08 is not a neutral authority on its own inference. |
| QF_BV ~2× Z3 | `00-thesis.md:43` | Consistent with the corpus; not independently re-derived here. Flagged: like `54/54`, it is a committed-slice number being used as a market claim. |
| Trust ledger **6 of 14 open**; `IntBlast`/`XorGaussian` unsound at pedantic 3 | `00-thesis.md:160-161`, `:194` | **Partly unsourced.** `XorGaussian` as a trust hole is real (ADR-0035:52,63 — "the 6th hole"). `P3.0-trust-ledger.md` contains no `6/14`. The denominator has **no citation in the corpus**. See G2. |
| `lean-smt` uses **CPC, not Alethe**; cvc5's Alethe has no bit-vectors | `00-thesis.md:113-115` | **Consistent across the corpus** and the most actionable finding in the track. Not independently verified against upstream here; it is load-bearing for G0.2 and should be verified before the ADR is filed, not after. |
| Kobeissi, 13 vulns, 4 inside verified code | `00-thesis.md:175-179` | **Consistent** with `04-software-ir-verification.md:246-273` as quoted by round 1 (`iteration-1.md:181-185`). |
| Note 01 settles metavariables unavoidable | `00-thesis.md:219-221` | **True** — `01-itp-anatomy.md:858`, and §1.4.1 at `:266`. Note 01 exists now (59KB); round 1's complaint that it was missing (`iteration-1.md:428-437`) is resolved. |
| Note 06 "did not exist when the table was written" | `plan/README.md:22` | **True and still true.** `06-kernel-gap-analysis.md` is 607 bytes, marked "DRAFT IN PROGRESS", three provisional bullets. The sizing note remains absent. v2 does not re-price anything on it — correctly, but it means Gate 2's "multiple person-years" is also unsourced. It is at least *conservative*, which draft 1's was not. |
| Sledgehammer ATP-free 46.8% vs 72.1% | `00-thesis.md:207` | Consistent (`03:494-498` per round 1). v2 files it under K5 as anti-overselling calibration — the correct use; round 1's F10 complaint about its placement is addressed. |

Net: **one claim materially misleading (`54/54`), one uncited (`6/14`), the rest
hold.** That is a better ratio than draft 1 and not a clean sheet.

---

## G8 — The strongest case FOR building: v2 walked past it without killing it

Round 1 never had to steelman the "yes" — it was attacking one. v2 has no such
excuse, and it does not engage this at all. Stated properly:

1. **Lean 4's kernel is a known bottleneck.** `bv_decide` — the very capability
   v2 cites as Lean closing the gap (`iteration-1.md:302`, Lean 4.12.0, verified
   AIG + LRAT-in-kernel) — is bottlenecked on in-kernel checking. Shipping the
   feature does not mean shipping the performance.
2. **`lean-smt` reconstructs 71% vs Ethos's 98%**, blamed partly on Lean's kernel
   speed and **missing array support**.
3. **Axeyum has a Rust kernel** (`axeyum-lean-kernel`) **and `eliminate_arrays`**
   (ADR-0010, QF_ABV → QF_BV via read-over-write + Ackermann) — i.e. exactly the
   two things named in (2).
4. **Nobody ships a WASM-deployable checkable reasoning substrate.** v2 retracted
   the *false* form of this ("Lean 4 cannot compile to WASM" — correctly; it was
   three repetitions of one inference from Lean4Web's gVisor deployment,
   `00-thesis.md:81`). But the *true* residue survives and v2 never re-costs it:
   Lean runs server-side behind gVisor; our WASM support is real and in the check
   gate (`CLAUDE.md`: "WebAssembly is a supported target (ADR-0017)").

**This is a product, and it is not the one v2 killed.** It is not a prover. It is
not a goal layer. It is "the fast, array-capable, edge-deployable reconstruction
backend" — which is **P3.7 with a reason to exist**, and it is the strongest
argument in the corpus for why P3.7 is not merely a fallback but a position.

**The asymmetry is the finding.** v2 retracted the false half of the WASM claim
and never asked what the true half is worth. Every retraction in v2 is *complete*;
no retraction leaves a surviving positive residue behind. Real revisions are
lumpy — a claim is usually 60% wrong, and the 40% is where the value is. **A
revision in which every one of ten findings resolves cleanly against the author is
evidence of deference, not of accuracy.** F1–F10 → ten clean concessions is not a
distribution that occurs when someone is reasoning; it is what happens when
someone is agreeing.

**What would have to be true.** v2 should contain a section, absent today, that
says: *"the strongest case for building is X; here is why it still loses."* It
does not, because round 1 did not ask for one — and v2 is a response to round 1
rather than an answer to the question. That is the structural defect underneath
every finding in this document.

Note the corpus itself hands over the disposition (`04:735-744`, quoted at
`iteration-1.md:24-26`): "**Do not enter the middle. Sell to both ends.** …
**Not one of them builds their own solver. All of them rent Z3.**" A fast,
array-capable, WASM-deployable backend is *literally* the thing to be rented. v2
routes to P3.7 and then declines to say what P3.7 is *for*. The steelman is not
an argument against v2's verdict — **it is v2's own verdict, argued properly, and
v2 left it on the floor.**

---

## What v2 got right, stated so the verdict is not mistaken for a reversal

Attacking the "no" is not the same as wanting a "yes". These are earned:

- **The residue argument (R3, `00-thesis.md:69-77`).** Subtract P3.7 and P5.2 and
  what remains is an MCP server and a WASM build. This survives independently of
  every finding above. It alone justifies "do not open a track."
- **Gate 2's sizing** (`plan/README.md:122-128`): XL crux, multiple person-years.
  Conservative, honest, and fatal to the *build* case on its own.
- **The inversion of the schedule.** Cheap deciding experiments first
  (`plan/README.md:24-26`). This was round 1's best structural finding (F6) and v2
  implemented it correctly.
- **K2** — "<40% of a SymCrypt-class obligation set → no market"
  (`00-thesis.md:204`). This is a *good* gate and the brief's suspicion should not
  land on it: SymCrypt-class is crypto/BV, i.e. our strongest column. Failing
  there means failing everywhere. Choosing the corpus most favourable to yourself
  and setting a kill threshold on it is exactly right.
- **K4** (see G4) — the one criterion that can catch the redirect being a polite
  never.
- **The TCB/boundary section** (`00-thesis.md:173-195`), including "**Not covered
  at all**: `sat` results… and — until measured — whether the fragment covers
  anything anyone wants." Round 1's F5 asked for this; it is free, it is correct,
  and the last clause is the most honest sentence either draft contains.
- **"Deferral by rejection is safe. Deferral by permission is not."**
  (`00-thesis.md:99`). This is the track's one durable artifact and it generalizes
  past the kernel.

---

## VERDICT

**OVER-CORRECTED.**

Not WRONG. The recommendation — *do not open Track 6* — survives this critique,
and it survives on a single argument that none of my findings touch: **subtract
P3.7 and P5.2 and the residue is an MCP server and a WASM build** (R3,
`00-thesis.md:69-77`), while re-entry is priced at an XL crux and multiple
person-years (`plan/README.md:122-128`). That is sufficient. It was sufficient in
round 1. It needs neither the 0% column nor "the last 10%".

Not EARNED, because **the document does not reach its conclusion by that
argument.** It reaches it by conceding ten of ten findings to a reviewer who
announced they were unbalanced by construction (`iteration-1.md:6-9`), and the
concessions are load-bearing where they are weakest:

1. **G1** — the 0%-column retraction ("**False.** […] I read past it.") is
   over-conceded. `pdr_lia.rs:43,716` / `pdr_lra.rs:35,694` show loop invariants
   are discharged by synthesis with QF queries gated by `verify_invariant`, not by
   deciding quantified LIA. The author found this, wrote it down
   (`00-thesis.md:46-51`), called round 1 "overstated" — and filed it as a nuance
   under a retraction that keeps round 1's conclusion. Quantified UF (0/5) stands;
   "loop invariants" does not. **An unmeasured claim decides the document, exactly
   as in draft 1, with the sign flipped toward the reviewer.**
2. **G3** — "the prover is the last 10%" has no evidence and is contradicted twice
   in v2's own pages: by Gate 2's sizing (`plan/README.md:122-128`) and by note
   01's "metavariables are unavoidable" (`01:858`), which v2 quotes approvingly 50
   lines later (`00-thesis.md:219-222`). Closing the 0% column changes the goal
   layer's hit rate, not its size. The phrase converts *no* into *later* without
   paying for it — **draft 1's sin written to be admired instead of approved.**
3. **G5** — K1 is rigged. Its calibration anchors on `lean4check`'s 87% on
   *proof-engineering* tasks, and note 05:462-464 says a rich surface is worth
   "little for mechanical tasks and a lot for search-heavy ones." The close-forever
   branch carries no qualifiers; the evidence-for branch carries two. **The "no"
   branch is easier to fire than the "yes" branch, and only it is permanent.**
4. **G2** — the number v2 kept (`54/54 = 100%`) is cherry-picked by the same
   standard that retracted `88–100%`: `capability-matrix.md:82` scopes it to
   positive-universal, no existentials, no arrays, no functions, committed slice.
   Plus `6/14` is uncited. **The document republishes F4's error inside the table
   that replaces it.**
5. **G6/G8** — the value is routed to tracks with no owner, no date, and no ADR
   (G0.2 is sized **S** and this track could file it), while the strongest case
   *for* building — Rust kernel + `eliminate_arrays` + WASM against `lean-smt`'s
   71% and Lean's kernel speed — is never engaged, only walked past. **v2 is an
   answer to round 1, not an answer to the question.**

**The distribution is the evidence.** Ten findings, ten clean concessions, zero
survivals, and one "nuance in our favour" that the author talked himself out of in
the same paragraph. Real revisions are lumpy. This one is uniform, and it is
uniform in the direction of the person grading it.

**Required before this document is adopted:**

1. **Restore G1's nuance to the body.** `00-thesis.md:29-36` becomes: round 1's
   framing was overstated; quantified UF stands; the loop-invariant claim is a
   mechanism error; the PDR/IMC route is unmeasured. **G1.2 must measure it** —
   currently it is a bullet (`plan/README.md:110-112`) under a gate whose fire
   condition ignores it.
2. **Delete "the last 10%"** (`00-thesis.md:170-171`, `plan/README.md:149-150`).
   Replace with Gate 2's own sizing.
3. **Re-specify K1**: name the obligation set in advance, require it to be
   search-heavy, strike "permanently".
4. **Scope `54/54`** with its carve-out or drop it. **Cite or count `6/14`.**
5. **File G0.2's ADR before closing** (it is S), or record it as found-and-dropped.
6. **Write the steelman section** (G8) and kill it explicitly — the one in note
   04's own words: be the thing they rent, and be fast, array-capable, and
   deployable where Lean is not.

Do those six and the verdict is **EARNED**, the recommendation is unchanged, and
the document will be shorter, less flattering, and true. Right now it is a correct
answer arrived at by deference, and a correct answer nobody can reconstruct is
worth about as much as a wrong one — which is the actual lesson of the paper this
track keeps citing (`00-thesis.md:175-179`): the proofs were fine; **nobody could
tell what they covered.**
