# Critique — Iteration 1 (adversarial)

Targets: [`../design/00-thesis.md`](../../design/00-thesis.md),
[`../plan/README.md`](../../plan/README.md), [`../DIARY.md`](../DIARY.md).

Written adversarially by instruction. This document does not attempt balance. Its
job is to state the strongest case against the draft; the draft's authors should
answer it, not agree with it.

---

## F1 — The picks-and-shovels contradiction is not answered, it is renamed

**Claim attacked** (`plan/README.md:12-14`):

> A goal layer above `axeyum-lean-kernel` that lets **agents** discharge
> **software** proof obligations against axeyum's decision procedures

Note 04 reaches the opposite conclusion, and it is the note's own headline
(`research/04-software-ir-verification.md:735-744`):

> **Do not enter the middle. Sell to both ends.** … Axeyum should **not** become
> "a sound-ish Rust verifier." It should be **the VC-discharge + certificate
> layer under the tools that already have distribution** … **Not one of them
> builds their own solver. All of them rent Z3.**

And `:674-676`: "the middle is mostly a trap; the picks-and-shovels layer under
both ends is not."

**Why the thesis is wrong here.** A layer that (a) owns a goal representation,
(b) owns forkable proof states, (c) owns tactics, and (d) sells directly to the
agent rather than to Verus/Kani/Creusot/Lean **is the middle**. The thesis's own
list of deliverables (`design/00-thesis.md:175-183`) is a verification front-end
minus the language. Note 04's graveyard test — "you can occupy the middle only if
you (a) control the language, (b) have a regulator forcing spend, or (c) abandon
soundness" (`04:616-620`) — is never applied to the proposal. Track 6 controls no
language. It names no regulator. It refuses (c). By its own imported criterion it
fails all three.

The thesis's escape hatch is `design/00-thesis.md:99`: "It is not an argument
against building a decision-procedure substrate that reports failure legibly."
That is an assertion, not an argument. Note 04's four structural reasons the
middle is hard (`04:623-643`) — spec cost, discontinuous value of soundness, both
ends eating inward, maintenance — apply to a "substrate for agents" verbatim. The
draft engages exactly zero of them.

**What would have to be true.** The thesis would need to name, concretely, a
customer who wants a goal layer that is *not* Lean, *not* Verus, and *not* Kani —
and explain why that customer will not simply use Lean's goal layer with axeyum
as a `bv_decide`-shaped backend (i.e. P3.7). "Agents" is not a customer. Note 04
already found the customer list and it is the tool cohort, not the agent.

---

## F2 — Track 6 is not distinguishable from P3.7 + P5.2 on the evidence presented

**Claim attacked** (`design/00-thesis.md:200-208`, the kill criterion):

> **P3.7 turns out to be sufficient.** If being a Lean tactic backend captures
> the value, the marginal case for a substrate is weak and we should say so.

The draft raises this and then does not answer it anywhere. Walk the five
deliverables (`design/00-thesis.md:175-183`) against the plans of record:

| Track 6 deliverable | Already covered by |
|---|---|
| 1. Goal as data | Lean's `MVarId` + Pantograph, reachable via P3.7 |
| 2. Forkable states | Pantograph does exactly this, today, for Lean |
| 3. Certificate-first tactics | **is P3.7** — "a Lean tactic backend" (`DIARY.md:50-52`) |
| 4. Counterexamples | needs T6.1.4, unbuilt and XL (F3) |
| 5. WASM | T6.4.3, sized **S** |
| Contracts / spec surface | P5.2, "may correctly reduce to" it (`plan/README.md:167-174`) |

The plan concedes row 6 outright. Rows 1–3 are Lean's, and the thesis's own
`what this is not` refuses to compete with Lean on them (`00-thesis.md:161-165`).
That leaves **row 4 and row 5**: a counterexample story that does not exist yet,
and a WASM build sized S. The draft's own residue is *an MCP server and a WASM
target*. `plan/README.md:151-157` sizes the entire agent surface — the thing
called "**the payoff**" — at **M**.

The draft even supplies the deflation and does not act on it
(`plan/README.md:161-163`): "`lean4check` + Claude Code reaches 87% on 189
proof-engineering tasks with **one tool**. A rich surface buys little."

**What would have to be true.** A measured demonstration that an agent driving
axeyum's goal layer beats the same agent driving Lean-with-axeyum-as-backend, on
the same obligations. The plan does not schedule this experiment — and it is
cheap, which is damning. If P6.4 is "where the thesis gets falsified cheapest"
(`plan/README.md:33-34`), it should be **first**, not fourth behind an XL crux.

---

## F3 — The counterexample differentiator is a hope with three unpaid debts

**Claim attacked** (`design/00-thesis.md:65-69`):

> Axeyum is a solver first. Every `sat` is checkable by evaluating the original
> term against the lifted model — that hard rule *already is* the counterexample
> product.

**It is not.** The hard rule says every `sat` is checkable *against the original
IR term*. The counterexample product requires checking against the **original CIC
goal**, across an untrusted translation the plan itself has not built. The thesis
elides a translation boundary in the word "already." Note 08 is blunt
(`research/08-solver-automation-assets.md:569-572`): "The `sat` side has no such
backstop and this is the sharpest unmitigated risk in the plan."

Three debts, none paid:

1. **T6.1.4 is XL and admitted unmitigated** (`plan/README.md:96`, `:196`). The
   differentiator's soundness gate is the single largest unscoped item in the
   track, and `plan/README.md:139` makes T6.3.2 "depend entirely" on it. The
   headline rests on the deepest item in the DAG.
2. **The 2026 state of the art walked away from this exact approach.**
   `research/05-education-and-agentic.md:536-538`: "the 2026 state of the art,
   having looked at SAT/SMT-based counterexample finding, walked away from it and
   trained a model instead." The thesis's rebuttal (`00-thesis.md:75-78`) — their
   complaint is about *approximating* HOL — is note 05's own rebuttal, and note 05
   marks it *(Inference)* and calls it "a much narrower claim"
   (`05:544-546`). The thesis promotes an inference-tagged, self-described-narrow
   reply into a load-bearing headline.
3. **No study shows counterexamples help learners.** Note 05's §5.3 is explicitly
   *"(Inference, but well-supported)"* (`05:553-554`) — i.e. unsupported by data.
   Note 05 also records `05:302`: "There is no controlled study showing CNL beats
   tactics for student outcomes," and the same evidential vacuum applies here.

**What would have to be true.** T6.1.4 closed *before* the thesis is written, not
scheduled after it; plus the fragment-coverage number (T6.1.6) showing that real
software non-theorems land inside the decidable image. The thesis admits it owes
this number (`00-thesis.md:78`, `plan/README.md:98`) and then argues as if it had
it.

---

## F4 — The "88–100%" claim is cherry-picked, and its 0% foil is misidentified

**Claim attacked** (`design/00-thesis.md:185-187`):

> The market is software and IR — where the goals are decidable, where axeyum
> already measures 88–100% … Not mathematics, where the goals are the 0% column.

This is the worst single sentence in the draft. Its source is note 08's scoreboard
table (`research/08-solver-automation-assets.md:38-53`). The full column reads:

| Fragment | Rate | Line |
|---|---|---|
| LIA (quantified) | **0%**, PAR-2 30.0 = every instance times out | `08:38` |
| UF (quantified) | **0%** | `08:39` |
| QF_SLIA | 36% | `08:40` |
| QF_UF | 54% | `08:41-42` |
| QF_S | 65% | `08:43` |
| QF_BVFP | 88% — **7 of 8 problems** | `08:49` |

The thesis quotes the top of the range and calls the bottom "mathematics." **The
0% rows are quantified LIA and quantified UF.** Those are not mathematics. They
are the bread-and-butter fragments of *software verification* — loop invariants,
array bounds over unbounded indices, uninterpreted function abstraction of callees.
Every tool in note 04's cohort (Verus, Creusot, Prusti, Dafny) lives there. Note 08
says so on the next line (`08:55-59`): "The 0% rows are exactly the fragments a
prover lives in."

So the thesis cites its own research note to claim the software market is the
88–100% column, when that note says the software market is substantially the 0%
column. Also: 88% is **7/8**, and 100% rows are committed regression corpora
(`SCOREBOARD.md`), not real obligations. Presenting a 7/8 regression-suite pass as
a market-sizing datapoint is not calibration; it is the exact overclaiming
`04:788-808` warns against.

**What would have to be true.** A coverage measurement on real software
obligations — which is T6.1.6, unbuilt. Until then the sentence must be deleted,
not softened.

---

## F5 — "Verification Theatre" applies to the draft, and the draft cites it without applying it

**Claim attacked** (`design/00-thesis.md:173`):

> **A checkable reasoning substrate for agents, aimed at software.**

Kobeissi's finding (`research/04-software-ir-verification.md:246-273`): 13
vulnerabilities escaped verification in libcrux/hpke-rs, **four inside verified
code**, because "the vulnerability is not in the proofs, it is in the
**verification boundary** — the undocumented interface between machine-checked
code and the trusted-but-unverified code around it."

Note 04 explicitly instructs that this be turned inward (`04:799-802`): "Take this
personally rather than as gossip about a competitor. Axeyum will make claims of
exactly this shape, and the failure mode is not 'our proofs are wrong,' it's
'nobody could tell what our proofs covered.'"

**The draft commits the sin it quotes.** Nowhere does the thesis or the plan state
what a Track 6 proof would cover. Search the two documents for a TCB enumeration:
there is none. Yet the TCB is *knowably* long and knowably novel:

- the CIC→IR translator (T6.1.2, untrusted but the boundary is undocumented);
- the model→CIC lifter (T6.1.4, unbuilt);
- the totality-convention reconciliation (T6.1.5) — a *semantics* boundary, exactly
  the "spec was wrong" class that produced Kobeissi's four in-verified-code bugs;
- the fragment definition itself (T6.1.1), i.e. what we decline;
- for the counterexample path: the kernel, the lifter, *and* the evaluator.

Note 04 hands over the counter-model and the draft does not use it
(`04:724-733`): SymCrypt's README enumerates its TCB *including what it does not
cover* ("leakage resistance is explicitly NOT verified"). Track 6 has no such
paragraph. A track whose research note says "cite this paper every time someone
says 'it's verified' — including us" (`04:272-273`) and which then ships a thesis
with no boundary statement has misread its own evidence.

**What would have to be true.** A TCB-and-boundary section in the thesis, written
before P6.1, stating what a Track 6 answer means and what it does not. This is
free. Its absence is a choice.

---

## F6 — Sizing is not credible, and the plan knows it

**Claim attacked** (`plan/README.md:21-29`) — the phase table.

Three XLs (P6.1, T6.1.4, T6.0.4) and no person-year figure anywhere in either
document. Meanwhile note 04's own §4 (`04:466-504`) is a table of person-year
costs — seL4 ~12–20 person-years for 8,700 SLOC; CompCert ~6; SymCrypt 58K proof
lines for 5.5K Rust. The draft cites that section for other purposes and never
applies its own yardstick to itself.

Specific implausibilities:

- **T6.0.4 = XL** covers `Proj`, `Lit`/bignum, `Quotient`, and mutual/nested/
  recursive-indexed inductives (`plan/README.md:69`). That is a *multi-year* list
  in Lean's own history. The plan's warning (`:76-78`) — "this is XL and could
  exceed the rest of the track" — is correct and is treated as a footnote rather
  than as a re-scoping trigger.
- **P6.4 = M** (`plan/README.md:27`) includes T6.4.3 WASM (**S**) *and* T6.4.4
  "parallel/batch checking" (M). Parallel checking of a kernel whose performance
  baseline does not yet exist (T6.0.5) is not M. Note that Aleph's entire
  competitive edge is "highly parallel Lean verification calls"
  (`research/02-ai-assisted-proving.md:293`) — the draft cites this as proof the
  capability is valuable and simultaneously sizes it as a sub-task.
- **P6.0 = M** for "kernel trustworthiness" of a kernel that admitted `False` last
  week, including T6.0.3 (differential-test against real Lean's export format,
  L, blocked on T3.6.4). Hardening-to-confidence is not an M.

**Dependency ordering error.** `plan/README.md:30` gives
`P6.0 → P6.1 → P6.2 → {P6.3, P6.4} → P6.5`, and `:33-34` says P6.4 "is where the
thesis gets falsified cheapest." Then it is placed **behind an XL crux**. If the
cheapest falsifier is fourth, the plan is optimized to spend before it learns. The
same inversion applies to T6.1.6 (the coverage number the thesis "owes"): it is
task *six* of P6.1, behind T6.1.2 (XL). The number that decides the track is
scheduled after the largest expenditure in the track.

**What would have to be true.** A person-year estimate per phase, using note 04's
own comparables, and a re-ordering that puts T6.1.6 and P6.4 first.

---

## F7 — The Mathlib concession is rhetorical cover

**Claim attacked** (`design/00-thesis.md:157-159`):

> **Not a rival ITP for humans writing proofs.** No proof scripting language, no
> IDE, no `Ltac`.

Now read what is being built: goals as data (T6.2.2), holes (T6.2.4), forkable
proof states (T6.2.3), metavariables-if-needed (T6.2.1, and the plan pre-concedes
"yes, you need them" is an acceptable finding, `plan/README.md:124-126`), `decide`
(T6.3.1), `simp` (T6.3.3), `induction` over recursors (T6.3.4), and a spec surface
(P6.5).

That is an ITP. The concession is scoped to the three artifacts a *human* touches
— script language, IDE, `Ltac` — and every artifact a human does *not* touch is
retained. Renaming the consumer from "human" to "agent" does not change the
engineering. `simp` is `simp` whether an LLM or a grad student calls it, and
T6.3.3 admits it is worse for us than for Lean: "`axeyum-rewrite`'s canonicalizer
emits no proofs — its certificate story is two `Future`-tagged comments"
(`plan/README.md:139`).

The draft even names the pattern in its own diary and then does it
(`DIARY.md:143-146`): "the research prompts were shaped around 'what does Lean
have that we lack,' which silently defines success as catching up to a 2015
design." The phase list is precisely a list of what Lean has that we lack.

**What would have to be true.** A demonstration that the agent-facing subset is
*structurally smaller* than the ITP lower half — not merely renamed. The plan
offers no such reduction; P6.2–P6.3 are the ITP lower half with the humans deleted
from the requirements doc.

---

## F8 — The kill criteria cannot fire

**Claim attacked** (`design/00-thesis.md:189-192`):

> The track must be able to conclude "no." These are the conditions under which it
> should, written now while they can still be honest.

Test each for falsifiability:

| Criterion | Line | Can it fire? |
|---|---|---|
| "P6.1 fails" | `:194-197` | **No threshold.** "Too narrow to cover useful software goals" — *useful* is undefined and the coverage number (T6.1.6) is self-graded by the track that wants to continue. |
| "`sat` trust story cannot be closed" | `:198-200` | **Unfalsifiable in practice.** No engineering problem is ever *proven* unclosable; it just stays open. This fires only if someone volunteers to stop. |
| "Lean closes the gap" | `:201-203` | **Not ours to observe on a schedule.** "Watch it" is not a criterion. And it is already half-fired: note 04 records `bv_decide` shipped in Lean 4.12.0 (2024-10-01) with a verified AIG + LRAT-in-kernel — the gap-closing event *already happened* (`04:387-406`). |
| "P3.7 turns out to be sufficient" | `:204-208` | **No test scheduled.** See F2. A criterion with no experiment attached cannot fire. |

Now add the sunk-cost problem. `DIARY.md:194` already says: "the track has already
paid for itself without a single line of prover code." Once P6.0 lands and is
credited to Track 6, every subsequent review inherits a track with a *positive*
ledger. The one unconditional item is also the item that makes stopping feel like
a loss. That is textbook.

**What would have to be true.** Numeric thresholds (e.g. "if T6.1.6 coverage on a
named obligation corpus < X%, stop"), a named date, and a named person who is not
the author. And P6.0 must be booked to Track 3, not Track 6 — see F9.

---

## F9 — The `False` bug is being spent twice, and it is not evidence for this track

**Claim attacked** (`DIARY.md:194`):

> Notably, the track has already paid for itself without a single line of prover
> code.

**This is self-congratulation wearing a ledger.** Three problems:

1. **The bug was found by auditing, not by planning a prover.** The diary says so
   itself (`DIARY.md:156-158`): "While auditing `inductive.rs` for the kernel-gap
   note, a line stood out." The generative act was *reading the kernel*. A task
   called "harden the kernel" — one sprint, no research corpus, no eight sub-agents,
   no thesis — would have found it strictly cheaper. The track cannot claim credit
   for a finding that its own cheapest alternative also produces.
2. **The plan disclaims the credit and then banks it.** `plan/README.md:23` and
   `:59-62`: P6.0 "is worth doing **whether or not any prover is built** — P3.6/P3.7
   route all their assurance through this component. It carries no decision." Both
   documents state P6.0 belongs to Track 3's obligations, and both count it as
   Track 6's payoff (`plan/README.md:105`: "P6.0 has already paid for itself"). It
   cannot be unconditional-therefore-not-a-bet *and* the bet's first return.
3. **It is weak evidence for the thesis and strong evidence against the schedule.**
   A kernel that admitted `False` in 2026, whose test suite was `Type`-only
   (`DIARY.md:174-177`), whose corroborating gate "was blind by construction"
   (`:178-181`) — that is an argument that the foundation needs a year of work
   before anything is stacked on it. The draft reads it as a green light with a
   prologue.

**What would have to be true.** Book P6.0 to Track 3. Re-run the ledger. If Track
6's net contribution to date is a research corpus and a thesis, say that.

---

## F10 — The `grind` vs Dafny number does not support the weight placed on it

**Claim attacked** (`design/00-thesis.md:28-32`):

> on miniF2F-Dafny, **Dafny's empty-proof SMT baseline reaches 38.9%, beating
> Lean's `grind` at 32.4% — with 1,221 lines of library against Mathlib's ~2M.**
> Library scale is demonstrably not the active ingredient on arithmetic-heavy
> goals.

This number carries findings #1 and #2 of the thesis and reappears in
`plan/README.md:45-46`. Its context, from the note it cites
(`research/02-ai-assisted-proving.md:346-366`):

- The benchmark is **miniF2F** — competition mathematics. The thesis's own market
  is "software and IR, not mathematics" (`00-thesis.md:185-187`). It is arguing
  for a software substrate using a *math-benchmark* result, in the same document
  that dismisses math benchmarks as the 0% column.
- The advantage is scoped: "Dafny-only wins concentrate in **algebra and number
  theory** — 'SMT solvers excel at arithmetic-heavy problems'" (`02:357`). The
  thesis carries "arithmetic-heavy" through once (`00-thesis.md:30-31`) and then
  drops it.
- **Complementarity, omitted:** "67 problems solved by both, 28 only by Dafny, 12
  only by grind" (`02:356`). A 6.5-point margin on a 244-problem benchmark with a
  12-problem reverse-win column is not "demonstrably" anything.
- The paper's *stated bottleneck* is "verification brittleness — minor variations
  in assertion order or calc organization cause verification failure"
  (`02:363-366`). That is note 03's Mariposa finding, i.e. the argument *against*
  the SMT route, arriving inside the datapoint the thesis uses to argue *for* it.

Compounding: the thesis quotes Sledgehammer's ATP-free baseline at 46.8% vs 72.1%
full (`00-thesis.md:206-207`) as calibration against overselling — and files it
under a *kill criterion for P3.7*. Read `research/03-atp-itp-seam.md:494-498`
again: that number says **premise selection rivals solver strength as a lever**.
Premise selection is a corpus-and-library problem. It is an argument that the
thesis's "library scale is not the active ingredient" claim is at best fragment-
local — and note 03's actual recommendation is to be a "**backend behind
lean-auto**, reusing its monomorphization and premise selection" (`03:496-498`),
i.e. **P3.7 again**.

**What would have to be true.** The same experiment on *software* obligations, and
an accounting of the 12 grind-only wins.

---

## Smaller hits

- **`plan/README.md:47-48`**, "Lean 4 cannot compile to WASM." Stated three times
  (`00-thesis.md:50-54`, `plan/README.md:47`, `:155`) and load-bearing for the
  "structural advantage" claim, sourced only to the observation that Lean4Web runs
  server-side behind gVisor (`00-thesis.md:51`). *Currently does not* ≠ *cannot*.
  A claim repeated three times on one inference needs a citation, and "structural
  property Lean has conceded and cannot cheaply reclaim" (`:53-54`) needs a
  mechanism. Lean's own runtime is C; the constraint is engineering appetite, and
  appetite changes when a competitor appears. This is the same class of error as
  a kill criterion that assumes the incumbent stands still — and `bv_decide`
  already shows they do not.
- **`00-thesis.md:97-99`**, the Mariposa instability ratchet as "a differentiated
  *measured* claim." It measures *our* stability. Practitioners' pain
  (`00-thesis.md:85-88`: "soul crushing," "existential dread") is on quantifiers
  and nonlinear arithmetic — the fragment the plan explicitly declines
  (`plan/README.md:93`). Measuring stability on a decidable fragment where
  instability is structurally rare and calling it a differentiator is measuring
  the easy case and reporting the score. The thesis half-admits this at `:93` —
  "Our differentiator is orthogonal to what practitioners actually hate" — and then
  proposes the ratchet anyway, two sentences later.
- **`00-thesis.md:141-143`**, "It is agent-shaped. An agent proposes; a checker
  disposes." Every ITP is this. Lean's kernel re-checks regardless of generation
  method — note 04 calls that "the one durable structural point" and notes it "is
  also *exactly* axeyum's thesis" (`04:455-457`). If it is exactly our thesis and
  already exactly Lean's property, it is not a differentiator; it is a shared
  premise.
- **`plan/README.md:186-195`**, the Alethe/CPC question filed as "not this track's
  call." If `lean-smt` uses CPC and cvc5's Alethe has no bit-vectors, then the
  Lean-facing route — the thing Track 6 must beat or join — is aimed through the
  wrong format *today*. A track whose central comparison is "P3.7 vs us" cannot
  defer the question of whether P3.7 is correctly targeted. Deferring it means the
  kill criterion at `00-thesis.md:204-208` is being evaluated against a P3.7 that
  may not be the real P3.7.
- **Missing notes 01, 04, 06 were partially reconstructed but the gap is
  under-marked.** `DIARY.md:250-254` records that notes 01, 04, and 06 died. Note
  04 exists now (and is the most damaging note in the corpus — see F1). **Note 01
  (ITP anatomy) and note 06 (kernel gaps with sizing) do not.** The thesis leans on
  the open question note 01 was commissioned to answer and says so twice
  (`00-thesis.md:147-151`, `plan/README.md:123-126`: "Note 01 was asked exactly
  this and did not survive to answer"). **Note 06 was the sizing note.** The plan's
  sizes (F6) are therefore unsourced — the document that would have priced P6.0/
  T6.0.4 never existed, and the table was filled in anyway. That is not a gap; that
  is the load-bearing input being absent.

---

## VERDICT

**MAJOR REVISION.**

Not KILL, for one narrow reason and it is not the thesis's: **P6.0 is real,
unconditional, and correctly identified** — and it belongs to Track 3 (F9). The
research corpus is genuinely good; notes 04, 05, and 08 are honest, self-critical,
and repeatedly contradict the thesis that cites them. That is a corpus worth
keeping and a thesis worth rewriting.

Not MINOR, because the load-bearing claims fail:

1. The strategic conclusion **inverts note 04's own** (F1) without engaging its
   argument, and note 04 is the only note that surveyed the actual market.
2. The market-sizing sentence is **cherry-picked from a table whose 0% rows are the
   software fragments** the track claims to serve (F4). This is the kind of error
   that, uncorrected, becomes the thing everyone remembers.
3. The differentiator depends on an **XL, unbuilt, admitted-unmitigated** task,
   scheduled after the spend it is supposed to justify (F3, F6).
4. The kill criteria **cannot fire** and the ledger is already rigged to make
   stopping feel like a loss (F8, F9).
5. The residue after subtracting P3.7 and P5.2 is **an MCP server and a WASM
   build** (F2) — and the plan sizes them S and M itself.

The revision that would make this defensible is smaller than the draft and more
useful:

- **Delete `00-thesis.md:185-187`.** Replace with T6.1.6's number or with nothing.
- **Book P6.0 to Track 3.** Re-run the ledger honestly. Track 6's net to date is a
  corpus and a hypothesis.
- **Write the TCB/boundary paragraph now** (F5). It is free, it is the one thing
  note 04 tells us to do "personally," and SymCrypt's README is the template.
- **Invert the schedule.** T6.1.6 (coverage on real obligations) and the P6.4-vs-
  P3.7 head-to-head are the two experiments that decide the track. Both are
  cheap. Both are currently scheduled behind two XLs. Run them first and let the
  thesis be *derived* from the result rather than defended against it.
- **Then re-ask the question.** If coverage is high and the head-to-head favours
  the substrate, this document is wrong and the track is real. If not, note 04
  already wrote the answer at `04:735-744`, and it is P3.7.

A track that has to survive its own research notes is not yet a plan. Make the
notes win, and see what is left.
