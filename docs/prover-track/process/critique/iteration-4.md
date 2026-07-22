# Iteration 4 — adversarial review

**Scope:** thesis v4 (+ iteration-1/2 edits), `plan/README.md`, `plan/P6.0`–`P6.6`,
`ADR-0167`, `research/11-dedukti-and-substrates.md`.
**Following:** [`iteration-3.md`](iteration-3.md).

> **Historical-number correction (2026-07-21):** this review's 64-row figure
> was the arithmetic/integer helper-call census, not the complete admitted
> population. Runtime construction finds 65 assumptions: real 30, integer 34,
> and the directly inserted string `append` axiom. The
> [type-digested ledger](../../../plan/generated/lean-axiom-ledger.md) supersedes
> the number below without rewriting the review's original reasoning.

**Verdict up front: NEEDS REVISION.** The sixth premise is named in F1 and it is
round 3's mistake with the sign flipped, exactly as feared. This round's other
findings are consequences of it.

The track's record: draft 1 (for) died of a backwards citation; v2 (against) died
of capitulation; v3 (against) died of "residue = MCP + WASM"; v4 (for) died of an
unfailable crux. Each was fully cited. Each was wrong at the root. The author's own
closing line — *"the adversary checks your reasoning; only the world checks your
premises"* (`P6.6-paper-attempt.md:131`) — is correct, and F1 is what happens when
you apply it once and then stop.

---

## F1 — THE SIXTH PREMISE: "Skolemization is plumbing"

**Claim** (`P6.6-paper-attempt.md:47`):

> "**The 0/5 is three distinct missing features, none of them research:** 1. **No
> Skolemization** (3/5, including the one `unsat` that matters). Textbook."

And (`:80-83`):

> "With `lives(sk)` from the Skolemized `pel55_1`, instantiating `pel55_3` at `sk`
> forces `sk ∈ {agatha, butler, charles}` — a three-way case split, after which the
> relevant reasoning is over a **three-element carrier**. That is precisely the
> shape we already decide."

**This is wrong, and it is wrong three times over.** I checked the goal and the
engine.

### 1.1 — Skolemization moves PUZ001+1 *out* of the only fragment we could decide

`pel55_10` (`cli__regress1__fmf__PUZ001+1.smt2:106-108`) is
`∀X ∃Y ¬hates(X,Y)`. Skolemizing yields `∀X. ¬hates(X, f(X))` — a **unary function
symbol**. The formula's other 13 assertions contain only constants
(`:46-48`; the TPTP header at `:33` states it: *"Number of functors : 3 (3
constant; 0-0 arity)"*).

Before Skolemization the prefix is `∃*∀*`-with-one-`∀∃`; after it, the formula has
a genuine function symbol under a universal. **That is the boundary of EPR** —
the effectively-propositional fragment, which is the *only* quantified-UF fragment
with the finite-model property, and therefore the only one where "bound the
carrier" is a **sound route to `unsat`**. `∀` + function symbols is undecidable in
general.

So Skolemization does not carry the goal *into* the shape we decide. It carries it
*out* of the shape we could have decided. The author has the arrow backwards — the
same failure as draft 1's "software is 88–100%", on a different number.

### 1.2 — The three-element carrier is unsound for `unsat` here regardless

`pel55_3` (`:69-74`) is **relativized to `lives`**:

```smt2
(assert (forall ((?X sort)) (=> (lives ?X) (or (= ?X agatha) (= ?X butler) (= ?X charles)))))
```

A model may contain any number of **non-living** elements. Bounding the carrier to
three and finding no model refutes *three-element models only* — it does not
establish `unsat`. The author's own cited evidence points the other way: the
file's first line is `; COMMAND-LINE: --finite-model-find` (`:1`), and FMF is a
**model-finding** technique for the `sat` instances. `PUZ001+1` is `unsat`
(`:43`). The author cites the FMF flag *in support of* the carrier-bounding route
on the one instance where FMF is not the route.

The author's caveat (`:86-89`) — *"`pel55_10`'s `∀X ∃Y` is not relativized to
`lives`, so `f(X)` escapes the closure"* — is stated and then discounted as "what a
real P6.6-paper must work out." It is not a caveat. It is the finding.

### 1.3 — Closing it needs a *fixpoint* instantiation loop, i.e. E-matching search

I worked the refutation. `pel55_10` is used at `X = butler`: from `pel55_7`
(`:91-94`) and `pel55_9` (`:101-104`), `hates(butler, X)` holds for every `X ≠
butler`; so `¬hates(butler, f(butler))` forces `f(butler) = butler`; then
`pel55_8` (`:96-99`) gives `richer(butler, agatha)`, contradicting `pel55_5`
(`:81-84`) in the `killed(butler, agatha)` branch.

**That derivation requires instantiating `pel55_7` and `pel55_9` at the ground term
`f(butler)`** — a Skolem term that does not exist until `pel55_10` has itself been
instantiated at `butler`. Two rounds.

Our engine does not do two rounds. `instantiate_with_triggers`
(`crates/axeyum-rewrite/src/quantifiers.rs:475-494`) collects `ground_subterms` and
`ground_universe` **once, from the input assertions**, then matches triggers
against that fixed set. It is single-pass. Terms *created* by instantiation never
re-enter the trigger set.

So the honest task list to close `PUZ001+1` is: Skolemization **plus** a
multi-round instantiation loop with a fairness/depth policy over a Herbrand
universe that is now **infinite** (`f(f(f(butler)))…`), because 1.1 removed the
finite-model property. **A depth policy is a search heuristic.** There is no
termination guarantee and no completeness guarantee; you stop when you stop.

**That is F5.** Not "how do we emit a certificate" — *how deep do we instantiate,
and why*. The goal the author offered as the plumbing example is the goal on which
F5 bites hardest. Skolemization does not retire the search premise; it **arrives
at** it.

### 1.4 — `Unsup=5, PAR-2=0.000` is what a *correct fragment boundary* looks like

**Claim** (`P6.6-paper-attempt.md:30`):

> "**`Unknown = 0`. `Unsup = 5`. `PAR-2 = 0.000`.** Not five timeouts — **five
> honest declines, costing zero time.**"

The row is real — `bench-results/SCOREBOARD.md:61` reads
`| UF | uf-cvc5-regress-clean-quantified | 5 | 0 | 0% | 0 | 5 | 0 | 0 | :status | 0.000 |`.
**Verified.**

But read the code that produces it. `decide_instantiation`
(`crates/axeyum-solver/src/auto.rs:5245-5252`) declines on
`instantiation.residual_quantifier`, and the doc comment two functions up
(`:5186-5194`) says why:

> "Because instantiation only *weakens* (each instance follows from its
> universal), a returned `Unsat` transfers soundly to the original."

The decline is **the soundness guard**. A residual quantifier means the weakening
argument does not license a verdict, so the engine says so — in 1.4 ms, because
checking a flag is fast. **`PAR-2 = 0.000` is not evidence that we didn't try. It
is evidence that the fragment boundary is checked before the search, which is what
we designed it to do.**

The author read *speed* as *unseriousness*, exactly as four drafts read *0%* as
*hard*. Both are readings of a number that encodes a **design decision**, mistaken
for a measurement of the world. The lesson of `P6.6-paper-attempt.md` was applied
to the scoreboard and not to the code behind it.

Note also: `auto.rs:5248` returns `CheckResult::Unknown(UnknownKind::Incomplete)`,
not `SolverError::Unsupported`. The harness buckets it as `unsupported`
(`crates/axeyum-bench/src/main.rs:4626-4638` is the `Unsupported` path). The
`Unknown=0 / Unsup=5` split the whole argument turns on is **a harness
classification artifact**, not a statement by the solver about the goal. The
solver said `Unknown`. Three adversarial rounds and one probe later, the argument
still rests on a column nobody traced to its source.

**What would have to be true** for F1 to be wrong:
- `PUZ001+1` must close with a *single-round* instantiation over
  `{agatha, butler, charles, sk}` after Skolemization — i.e. my 1.3 derivation must
  be avoidable. Falsify by running it, not by arguing.
- **Or** carrier-bounding must be sound for `unsat` on a formula with a
  non-relativized `∀∃` and a Skolem function. It is not.
- **P6.6-probe is still the right next task** — but it must publish, alongside the
  number, *how many instantiation rounds and to what term depth*. Without that,
  a `decides` outcome proves only that a depth we chose happened to suffice for a
  goal we chose.

---

## F2 — The conclusion outlived its stated reason without moving

**Claim** (`design/00-thesis.md:58`, quoting v4 draft 1):

> "v4's first draft inverted it: *the 0% column is the reason the layer exists.*"

**Claim** (`:75-76`):

> "**So the 0% column is withdrawn from this document as evidence for anything** —
> for or against."

**Claim** (`:80`):

> "The *claim* stands on its own without the 0/5."

**This is the tell.** The author stated the reason ("the 0% column **is** the
reason the layer exists"), withdrew the reason, and the conclusion did not move a
millimetre. A conclusion that survives the deletion of its declared reason was
never held for that reason.

What is actually left holding it up:

1. **The residue argument** (`:35-47`): P3.7's only input is a completed `unsat`;
   it has no representation of not-yet-knowing; **"the residue is machine-found
   decomposition outside the decidable fragment."** This is a true and
   well-cited observation about a **gap**. R2 established that the same fact
   supported the *opposite* conclusion — v3 used "P3.7 + P5.2 cover it, the residue
   is an MCP server and a WASM build" to refuse. **A gap is not a demand.** "X does
   not do Y" is a premise for "build Y" only with a further premise that someone
   wants Y. That premise is `P6.1e`, unmeasured, and the ADR says so
   (`adr-0167:156`: *"whether the fragment covers anything anyone wants
   (unmeasured until P6.1e)"*). The load-bearing fact is scheduled after the
   decision it bears.
2. **PDR as precedent** (`:84-96`) — and the author concedes it: *"`TransitionSystem`
   **donates** the schema… PDR searches for the **witness**; it never searches for
   the **schema**. We have never machine-found a schema."* An existence proof that
   is explicitly labelled as not covering the case at issue is not evidence for
   the case at issue.
3. **The independent-kernel argument** — which the author states needs **no goal
   layer** (`:308-309`: *"true today, with no goal layer, no bridge, and no
   person-years"*). It cannot support the goal layer; it is an argument for P6.0,
   which the ADR already exempts.

Netting: after the withdrawal, the affirmative case for the goal layer is (1) a
gap that also argued for refusal, and (2) a precedent the author says does not
transfer. **That is less than v3 had for the opposite conclusion.**

**What would have to be true:** the thesis would have to name *one obligation, from
one consumer, stated in advance*, that P3.7 and P5.2 both decline and someone
wants. It does not have one — and P6.4's own exit criteria demand exactly this
rigour of the falsification experiment (`P6.4:139-143`: *"a **named** obligation
set, fixed **in advance**"*). Hold the thesis to the standard the plan holds the
experiment to.

---

## F3 — The gates: one is owed anyway, one fires after the spend, one is
contradicted by its own phase file

**Claim** (`adr-0167:68-77`):

> "**Everything above P6.0 is authorized only through gates**… 1. P6.6-probe …
> 2. P6.6-paper … 3. **P6.1b** — CIC → IR for a named starter fragment. 4. **P6.4**
> — beat a `lean4check`-shaped loop on a named, search-heavy set. **Any gate
> failing closes the rung.**"

Gate by gate:

- **Gate 1 (P6.6-probe): can fire, and is the best thing in the plan.** Days,
  cheap, publishes a number. Keep it — but see F1.4: it must publish rounds and
  depth or it measures the policy we chose.
- **Gate 2 (P6.6-paper): can fire.** Good.
- **Gate 3 (P6.1b): CANNOT close the rung.** The thesis says so directly
  (`00-thesis.md:481`): *"(Owed to P3.7's T3.7.3 anyway — **worth doing, not a
  test**.)"* A task you will do, want, and keep regardless of the rung is not a
  gate on the rung. **This is R3's F-crux defect, relocated one phase down.** R3
  killed "P6.1a is the crux" because the crux could not fail; the ADR now lists as
  gate 3 a task the thesis explicitly labels "not a test."
- **Gate 4 (P6.4): fires after the spend it is supposed to authorize.** P6.4
  depends on P6.2 (`P6.4:112`), P6.2 depends on P6.1b (`P6.2:3`), and P6.2 is
  **L** with the author's own note *"**P6.2 is genuinely L**"* (`P6.2:38`). So the
  sequence to reach gate 4 is P6.1b + P6.2(L) + P6.4(M). The gate that tests the
  product claim fires **after most of the person-years**. That is `README:45`'s
  own diagnosis of draft 1 — *"put the real test after person-years — draft 1's
  sin"* — reproduced.
- **Gate 4 is also contradicted by its own phase file.** `adr-0167:77`: *"Any gate
  failing closes the rung."* `P6.4:159-161`, section titled **"Ship it
  regardless"**: *"The MCP server is picks-and-shovels and it is cheap. **Ship it
  whatever K1 says.**"* And `P6.4:151`: *"**Revisit only on new evidence** — *not*
  'permanently'."* So a gate whose failure "closes the rung" sits in a phase that
  ships regardless and whose failure is explicitly non-permanent. **Two documents,
  two incompatible consequences for the same event.** One of them is wrong. Given
  the track's history, I predict which survives contact with sunk cost.

**On "is 'any gate failing closes the rung' credible once P6.0 has shipped?"** No —
and not because the author is dishonest. Because **the ADR has already
pre-committed the rhetoric**. Its title is *"Enter the proof-construction rung"*;
its Decision (`:33-35`) is *"**Enter the rung** for a certificate-first goal
layer"*; the gates appear 30 lines later under a heading admitting *"this ADR
authorizes P6.0 only"* (`:62`). A reader — including the author in six months —
retains the title. If the ADR authorizes P6.0 only, and P6.0 is *"exempt from this
rung"* and *"authorized unconditionally"* (`:64`), then **the ADR authorizes
nothing that requires an ADR.**

**What would have to be true:** the ADR should be titled and framed as what it is —
*"Authorize P6.0 and schedule four gates before the rung question is reopened"* —
with Status: `proposed`, decision **deferred**, not `Enter the rung`. And gate 3
must be replaced (P6.1b is owed anyway) and gate 4 moved before P6.2, or the
gate structure is decorative.

---

## F4 — The new phase files: not padding, but a second source of truth

`P6.2`–`P6.5` are **substantially duplicated** in `plan/README.md:151-220`, which
carries the same phase headings and the same T6.x task tables. Neither file is a
stub pointing at the other. Two copies, no owner, guaranteed drift. Fix: make the
README a table of contents.

On content:

- **P6.2 (L)** is real and correctly sized. T6.2.1 (`:22`) — *"obligation type
  **outside** the kernel… **Prove this insufficient before touching the kernel's
  term language**"* — is the best-designed task in the track: it names the TCB
  consequence and the re-decision trigger (`:44-46`). T6.2.4 (metavariable
  coupling, "the sleeper") is genuinely the kind of thing that is unrecoverable
  later. Keep.
- **P6.3** is real per-tactic. `T6.3.2` correctly gates `counterexample` on P6.1c.
  Its "open premise" section (`:94-98`) is honest and states F1's problem
  correctly: *"`simp`, `induction`, and `invariant` are not [safe]: they must
  *find* the decomposition first, and nothing in the design says how."* **This
  section is right and F1 shows it applies to `decide` too** — `decide` is only
  "safe" (`:96`, *"the solver already found the proof, so the certificate is a
  transcript"*) when the goal is in the fragment. On `PUZ001+1` the instantiation
  depth *is* the search, and it happens inside `decide`. The phase file's own
  safe/unsafe split is drawn in the wrong place.
- **T6.3.5 marked "undefined, scope it before scheduling" (`:80`) is HONEST**, and
  it is the single most credible line in the plan: *"'Unweld it from
  `TransitionSystem`' is a research question wearing a task's clothes."* That is
  the author catching themselves. It is not an escape hatch because it is
  accompanied by a consequence (blocked in the slice order, `:84-85`) and because
  the thesis repeats it rather than burying it (`00-thesis.md:95-96`).
- **P6.5's "the most likely honest outcome is this phase is cancelled" (`:215-219`)
  is HONESTY, narrowly** — because T6.5.0 (`:204`) makes it *testable*: *"measure
  what fraction P5.2's finite+decidable contracts already cover… **a number; if
  high, cancel P6.5**"*. A hedge with a measurement and a pre-committed action is a
  gate. **But it is not on the ADR's gate list**, and it should be: it is cheaper
  (S) than gates 3 and 4 and it can retire an L phase. Promote T6.5.0 above gate 3.

**Net:** the phase files are the best-executed artefact in the track. They are also
downstream of F1 and F2, which means well-built plumbing under a premise that has
not held once in five attempts.

---

## F5 — The Dedukti rejection is under-argued, and the author had a motive

**Claim** (`adr-0167:125-127`):

> "**Dedukti / λΠ-modulo as substrate.** Rejected: it **grows** the TCB (kernel +
> rewrite theory + external confluence + termination + adequacy proof), its export
> weakens to constructive simple type theory, no BV theory exists, and CoqInE has
> chased CIC universe polymorphism since ~2012."

The research note is **more honest than the ADR that cites it.**
`research/11:368-369` says:

> "**One open thread worth chasing:** the SMT-proof-reconstruction-in-Lambdapi
> paper (hal-04861898)"

The note flags the thread as **open and unchased**. The ADR converts it into a
settled rejection whose stated ground — *"no BV theory exists"* — is precisely
what a paper on **SMT proof reconstruction in Lambdapi** is most likely to speak
to. **You cannot reject an option on a fact you declined to look up.** The note
itself records `research/11:225-226` that the paper exists.

The "grows the TCB" argument is also the wrong metric. The alternative under
comparison is `axeyum-lean-kernel`, which **admitted `False` on 2026-07-15**
(`adr-0167:150`), carries **64 unproven prelude axioms**, and has **6 of 13 open
reduction-ledger entries**. TCB *size* is not the axis; TCB *validatedness* is,
and the track's own synthesis says so (`00-thesis.md:326-330`: *"Small trusted
kernels get verified; the bugs live in the parts that aren't small"*). By that
standard Dedukti's position is better than ours, not worse.

**The motive is on the page.** Dedukti is the one alternative that would make the
author's *"strongest claim this track produced"* — the independent kernel — a
commodity. That does not make the rejection wrong. It makes it the one rejection
that needed the citation the author skipped.

**What would have to be true:** fetch hal-04861898 and hol2dk's BV coverage.
Twenty minutes. Then reject it on what it says. If the conclusion is unchanged the
ADR costs nothing and gains a defensible alternative section; if it changes, the
track's substrate choice changes. Either way, "convenient" stops being the fair
reading.

---

## F6 — The independent kernel: rare is not wanted, and the ADR forbids the use

**Claim** (`00-thesis.md:288-309`):

> "**`axeyum-lean-kernel` is a genuinely independent, from-scratch CIC kernel in a
> different language.** There are almost none. That is a stronger, cheaper, and
> more defensible claim than anything in the differentiator list."

The **rarity** claim is well-sourced and I believe it: `coqchk` links
`rocq-runtime.kernel` (`:297-300`), `lean4lean`'s README concedes *"not really an
independent implementation"* (`:301-303`), and the empirical case is one data point
(`lean4checker` vs `native_decide`). **This is the best-verified paragraph in the
track.**

**It is also a vanity metric as stated**, for a reason the author's own out-of-scope
list creates:

> "**A mathematics library.** No Mathlib competitor, ever. **We import nothing** and
> grow no corpus of mathematical lemmas." (`adr-0167:51-52`)

An independent checker's job is to re-check **the same artefacts** the first kernel
accepted. `lean4checker` does this by loading `.olean` files and replaying the
environment. **To be the second independent Lean checker you must import Lean's
environment** — which is precisely the thing the ADR forbids *permanently, not "for
now."* The claim and the scope boundary are incompatible: **an independent checker
with nothing to check.**

Three more problems:

1. **We are not checking the same logic.** 64 unproven prelude axioms
   (`SYNTHESIS.md:222`: *"arith 30 + int 34, counted"* — 30+34=64, **verified**)
   plus 6 of 13 open ledger entries means our kernel **accepts strictly more** than
   Lean's on arithmetic. A checker that is *weaker* than the thing it checks is not
   a cross-check; it is a different system with a coincidentally similar term
   language. The thesis knows this (`:134`: *"Bounds what 'kernel-checked' means for
   arithmetic"*) and still calls the claim the strongest one it produced.
2. **The one empirical win is expiring, by the author's own citation**
   (`:314-317`): Lean deprecated in-kernel native reduction **2026-02-01**. The
   author correctly says *"no plan should lean on it"* — and then leans the
   strongest claim on the single data point that hole produced.
3. **Pollack-consistency is unchecked** (`:319-321`: *"Nobody has checked whether
   `lean_pp.rs` is well-behaved"*). An independent checker whose printer might
   render `False` as `True` is not yet a checker.

**Who would pay for it?** Nobody named. The thesis names no consumer for this, and
`P6.1e` — *"whether the fragment covers anything anyone wants"* — is unmeasured
(`adr-0167:156`). The people who want a second Lean kernel are the ~dozen people
who already ran `lean4checker`; they got it in 738 lines.

**What would have to be true:** name one artefact, produced by someone else, that
our kernel can re-check today and `lean4checker` cannot — or drop "strongest claim"
to "true, cheap, and currently unused." **P6.0 is still worth doing** — a kernel
that admitted `False` must be fixed regardless of every argument in this track —
but as ADR-0165 hygiene, which is how ADR-0167 correctly frames it (`:64`), **not
as the product** (`00-thesis.md:311`: *"Hardening the kernel is not merely a
prerequisite; it is the product"* — that sentence oversells).

---

## F7 — Fact check

| Claim | Cited at | Status |
|---|---|---|
| `UF / uf-cvc5-regress-clean-quantified / 5 / 0 / 0% / 0 unknown / 5 unsup / PAR-2 0.000` | `P6.6:23-28` | **VERIFIED** — `bench-results/SCOREBOARD.md:61` reads exactly this. |
| The 3/5 decline string *"query has quantifiers instantiation does not reach (nested, existential, or non-top-level)"* | `P6.6:41-43` | **VERIFIED verbatim** — `crates/axeyum-solver/src/auto.rs:5248-5250`. |
| The decline is `Unsup`, i.e. not an `Unknown` | `P6.6:30` | **MISLEADING** — the solver returns `CheckResult::Unknown(UnknownKind::Incomplete)` (`auto.rs:5245-5247`). `unsupported` is a *harness bucket* (`bench/src/main.rs:4626-4638`). See F1.4. |
| `pel55_1` = top-level `∃`; `pel55_10` = `∀X ∃Y ¬hates(X,Y)` | `P6.6:60-66` | **VERIFIED** — `PUZ001+1.smt2:55-58` and `:106-108`. Author renamed symbols for readability (`lives` vs `lives__smt2_1`); harmless. |
| `pel55_3` is a domain-closure axiom relativized to `lives` | `P6.6:75-78`, caveat `:86-89` | **VERIFIED** (`:69-74`) — and it is fatal to the surrounding argument, not a caveat. See F1.2. |
| *"a three-element carrier… precisely the shape we already decide"* | `P6.6:82-83` | **FALSE.** See F1.1–F1.3. |
| PUZ001+1 has only constant functors | TPTP header `:33` | **VERIFIED** — which is why Skolemization is the step that breaks EPR. |
| Instantiation is single-pass over input ground subterms | — | **VERIFIED** — `axeyum-rewrite/src/quantifiers.rs:475-494`. Author never states this; it is the load-bearing fact. |
| **64 unproven prelude axioms** | `00-thesis.md:134,504`; `adr-0167:150` | **VERIFIED as counted** — `SYNTHESIS.md:222` gives the breakdown "arith 30 + int 34, counted" (sums). Not independently recounted here. |
| **6 of 13** open reduction-ledger entries | `adr-0167:151`; `00-thesis.md:504` | **PLAUSIBLE** — `docs/research/08-planning/trust-ledger.md` has 15 table lines = header + separator + **13 rows**. The "6 open" figure was not spot-checked. **Citation hazard:** the same paragraph cites *Verification Theatre*'s **13 vulnerabilities** (`SYNTHESIS.md:210`). Two unrelated 13s, one paragraph. Disambiguate. |
| *"~99.9% of agent per-branch wall time is import + re-elaboration"* (~60s import, tactic exec <0.1%) | `00-thesis.md:277`; `P6.4:123-127`; `SYNTHESIS.md:195` | **Internally consistent, source not re-fetched.** The **inference** is the problem, not the number: "we have no library to import" is true *because we have no library*. That is an advantage the way having no customers is an advantage in support costs. If P6.5/P6.3 ever need a corpus of lemmas, the tax arrives. Do not bank it. |
| *"LLMs score 0/33 across 660 attempts"* | `adr-0167:54-56` | **VERIFIED** — `research/10-autoformalization.md:82,87` (*"No LLM produced code that parses across 660 attempts"*). |
| MM0 producer/consumer split; set.mm ZFC <200ms | `P6.3:63-68` | Consistent with `research/11`; not independently re-fetched. |
| `lean4checker` caught `native_decide` `False`; `coqchk` links `rocq-runtime.kernel`; `lean4lean` README concedes | `00-thesis.md:294-303` | Best-cited passage in the track; see F6 for what it does not support. |

---

## VERDICT: NEEDS REVISION

**The sixth unexamined premise, stated explicitly:**

> **"A decline is missing plumbing."**
>
> Concretely: *that Skolemization moves PUZ001+1 into the fragment we already
> decide, and therefore that the 0/5 measures our coverage rather than the goal.*
>
> It is false. Skolemizing `pel55_10` introduces a unary function symbol under a
> universal, which **leaves EPR** — the one quantified-UF fragment with the
> finite-model property, and the only one where carrier-bounding is sound for
> `unsat`. `pel55_3` is relativized to `lives`, so the three-element carrier does
> not license `unsat` even without `f`. And the refutation needs `pel55_7`/`pel55_9`
> instantiated at `f(butler)` — a term that exists only after a *second*
> instantiation round, which `quantifiers.rs:475-494` does not perform, over a
> Herbrand universe that is now infinite. **Closing the goal requires an
> instantiation depth policy. A depth policy is a search heuristic. That is F5.**
>
> The `PAR-2 = 0.000` the author read as "we never tried" is the soundness guard at
> `auto.rs:5245-5252` reporting, correctly and instantly, that the goal is outside
> the fragment where our technique is sound. **Fast is what a correct boundary
> looks like.**

**The shape of the error is the track's signature, for the sixth time.** Draft 1
read `88–100%` backwards. v2 read "the adversary is right" as evidence. v3 read
`0%` as `hard`. v4 read `0%` as `the reason the layer exists`. The probe read
`Unsup, 0.000s` as `we never tried`. **Every one is a number, correctly quoted,
whose *meaning* was assumed rather than traced to the code or the model theory that
produced it.** The author's own maxim is right and was applied one level too
shallow: running the goals checked the *scoreboard*. It did not check the
*engine*, and it did not check whether the fragment boundary the engine reports is
a bug or a theorem. **It is a theorem.**

R3's F5 stands, undamaged, and is now *stronger* than when R3 stated it — not
because R3's inference was valid (it was not; the author is right about that) but
because the probe walked to the same wall from the other side and did not
recognise it.

**What must change before iteration 5:**

1. **P6.6-probe stays gate 1 and is still the right next task** — but its exit
   criterion must include **instantiation rounds and term depth**, and it must
   state up front that a `decides` result at depth *k* is a fact about *k*.
2. **Withdraw §"Why PUZ001+1 declines, concretely"** (`P6.6:56-89`) as an argument.
   Keep the observation that the errors are informative; delete the three-element
   carrier and the "none of them research" verdict.
3. **F2:** either name one obligation, one consumer, in advance — or record that
   the affirmative case for the goal layer is currently a gap plus a
   non-transferring precedent, which is **weaker than v3's case for refusal.**
4. **F3:** retitle ADR-0167 to what it does (authorize P6.0, defer the rung).
   Replace gate 3 (owed anyway → cannot fail). Move gate 4 before P6.2 or accept
   that the product test follows the person-years. Reconcile `adr-0167:77` with
   `P6.4:159-161`.
5. **F5:** fetch hal-04861898 before rejecting Dedukti.
6. **F6:** demote "the product" to "an obligation on a shipped component," and
   either name an artefact only we can re-check or drop "strongest claim."

**And the standing instruction for iteration 5, which is the only one that has ever
worked here:** *before quoting a number, open the code that emits it.* Five drafts
and four reviews have now been decided by numbers whose provenance nobody opened.
The probe opened one. Open the next one.
