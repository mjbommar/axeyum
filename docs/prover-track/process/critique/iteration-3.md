# Iteration 3 — adversarial review of v4 ("build it, sliced")

**Scope:** `design/00-thesis.md` (v4), `plan/README.md` (P6.0–P6.6), `DIARY.md`
(2026-07-15 late), research notes 01/04/07/08, checked against the repo.

> **Historical-number correction (2026-07-21):** later runtime inventory found
> 65 admitted prelude assumptions (real 30, integer 34, string `append` 1).
> Call-site/line counts discussed below were not a complete environment census;
> the [runtime ledger](../../../plan/generated/lean-axiom-ledger.md) is authoritative.
> T6.0.3 has also since landed a deterministic 768-case gate over the four
> currently representable seams. The zero-fuzz statements below describe this
> review's input state; projection/eta and quotient extensions remain open.

**Charge:** v4 reversed v3's considered position immediately after a grader told
the author the position was unacceptable. Round 2's central finding was that this
author concedes to whoever holds the pen. The question is whether v4 found a real
hole or manufactured an escape hatch.

**Short answer:** the hole is **real but partial** — one of four clauses. The
other three are false against P3.7's own text, and they are precisely the three
that make the hole sound total ("the residue is *everything*"). v4 is not a pure
capitulation; it is a genuine finding inflated to carry a conclusion the author
was told to reach.

---

## F1 — The load-bearing claim is 25% true. Three of its four clauses are false.

**Claimed** (`design/00-thesis.md:23-30`):

> **P3.7 makes axeyum a *Lean tactic backend* — Lean owns the goal, the
> elaborator, and the proof state.** So P3.7 delivers:
> - nothing without a Lean toolchain installed;
> - nothing in WASM, in a browser, or in an agent's own process;
> - nothing when the goal is not already stated in Lean;
> - and — the real one — **no way to make progress on a goal we cannot one-shot
>   decide**, because decomposition is Lean's job in that architecture.

Read P3.7. It says the opposite of clauses 1–2.

- `docs/plan/track-3-proof-lean/P3.7-lean-reconstruction.md:8-11` — Goal: "Turn
  axeyum's Alethe proofs into CIC `expr` proof terms that
  **`axeyum-lean-kernel`** (and Lean itself) accept". Our kernel is named
  **first**; Lean is the parenthetical.
- `:25` T3.7.1 — "A pre-proved lemma library **(Lean or in-kernel terms)**".
- `:28` T3.7.4 — exit: "axeyum `unsat` → Alethe → CIC term →
  **`axeyum-lean-kernel` accepts**". No Lean in the loop.
- `:50` Phase exit — "reconstructs into a CIC proof term that
  **`axeyum-lean-kernel`** (and Lean's kernel) accepts".

`axeyum-lean-kernel` is pure Rust with an **empty `[dependencies]`** (verified:
`crates/axeyum-lean-kernel/Cargo.toml`). Under ADR-0017 it builds to WASM. So:

- **Clause 1 is false.** P3.7's exit criteria are satisfied with no Lean
  installed. The Lean binary appears in P3.7 only as an *additional*
  cross-check (`:41-45`, "the real Lean binary" as a gate — a corroborator, not
  a dependency).
- **Clause 2 is false.** A no-C/C++, empty-dependency Rust kernel checking a CIC
  term is *exactly* "in WASM, in a browser, in an agent's own process."
- **Clause 3 is false as stated.** The goal is stated in **Alethe/axeyum
  `Term`**, and T3.7.3 (`:27`) encodes axeyum `Term`/sorts *into* CIC. Nothing
  requires the goal to originate in Lean. If anything the pipeline runs the other
  way: axeyum owns the goal, Lean is an export target.
- **Clause 4 is TRUE.** See F2.

**Why this matters more than an erratum.** The rhetorical payload is
`:32-33` — "Remove that assumption and the residue is not an MCP server. It is
*everything*." That inflation is carried **entirely** by clauses 1–3, and clauses
1–3 are contradicted by four lines of the file being characterized. Clause 4
alone yields "the residue is decomposition," which is a real but bounded gap —
and notably *not* "everything."

**What would have to be true:** P3.7 would have to make `axeyum-lean-kernel`
optional or subordinate — e.g. reconstruction emitting only Lean source for an
external `lean` binary to elaborate. It does not; `prove_unsat_to_lean_module`
(`crates/axeyum-solver/src/reconstruct.rs:3710`) "errors unless the term checks to
`False`" **in our kernel** (note 07:70).

**Verdict: the central new claim is 25% true, and the 75% is what makes it feel
decisive.** This is the same defect the author diagnosed in his own diary —
"letting one unexamined claim carry the document" — reproduced at the exact
moment he claimed to have cured it.

---

## F2 — The surviving clause is real, and neither prior round examined it.

Clause 4 stands, and it is not trivial. Check both alleged decomposers:

**P3.7 does not decompose.** Its whole input is an Alethe proof — an artifact that
exists *only because the solver already decided the goal*. Reconstruction's
control flow "runs backward from the answer" (note 07:366, 485). It cannot start
on a goal with no proof to replay. On the 0% column P3.7 has no input at all.

**P5.2 decomposes, but along axes v4 correctly identifies as insufficient:**

- `P5.2-contracts-modular.md:33` T5.2.2 — the composition rule is "assert the
  callee's `requires`…, assume its `ensures`…", i.e. decomposition **at call
  boundaries only**, and "**recursion declined honestly in v1**."
- `:18-20` — "Contracts keep every obligation **finite and decidable**… which is
  what separates this from ghost-code deductive systems."

So P5.2 is *definitionally* confined to obligations already in the decidable
fragment. It never produces progress on an undecidable goal; it presupposes the
decomposition is **supplied by a human writing contracts**. The residue after
P3.7+P5.2 is therefore: *machine-found decomposition of goals outside the
decidable fragment, including recursion/induction.* That is not an MCP server.

**This is a genuine hole and I am not going to pretend otherwise.** Round 1's F2
and round 2 both endorsed "residue = MCP + WASM" without either adversary reading
P5.2's recursion carve-out or noticing P3.7 has no input on undecided goals. The
author is right that an adversary "attacks the argument you make; it cannot supply
the argument you failed to make" (`DIARY.md`, late entry).

**But:** the residue is one capability (found decomposition), not "everything,"
and F5 shows v4 has no mechanism for it either.

---

## F3 — The PDR argument generalizes from the one case where the shape did the work.

**Claimed** (`design/00-thesis.md:45-52`, `plan/README.md:16-19`):

> `pdr_lia.rs:40-46` — PDR **synthesizes** an invariant…, then discharges three
> obligations… quantifier-free… **That is a goal layer.** A special-purpose one,
> welded to `TransitionSystem` (`bmc.rs:47-72`). The generalization of that
> pattern is the thing v3 refused to build.

**This is the argument v4 leans on hardest, and it is the weakest.**

Read `crates/axeyum-solver/src/bmc.rs:47-72` (verified). `TransitionSystem` is a
trait with exactly `state_vars`, `init`, `trans` (+ `bad`). That is not incidental
scaffolding — **it is the entire reason PDR works.** Given `init`/`trans`/`bad`,
the decomposition into three obligations

```
init ⇒ Inv        Inv ∧ trans ⇒ Inv'        Inv ⇒ ¬bad
```

is **not discovered**. It is the *definition* of an inductive invariant, fixed a
priori, instantiated mechanically. PDR searches for the **witness** (`Inv`); it
never searches for the **schema**. The schema was donated by the shape.

An arbitrary CIC goal has **no such schema**. There is no `init`/`trans` to read
off, no known induction principle to instantiate, and finding the right
decomposition *is* the open problem. So the inference "we generalize PDR off
`TransitionSystem`" (`plan/README.md:19`) quietly proposes to remove the only
component doing the work and expects the pattern to survive.

Compare `T6.3.5` (`plan/README.md:118`): "**`invariant`** — expose PDR/IMC as a
tactic. It already *is* a goal layer; unweld it from `TransitionSystem`." Unwelded
from `TransitionSystem`, PDR has no transition relation. This task, as written, is
not sized L; it is not defined.

**What would have to be true:** v4 would need a second, structurally *different*
goal where a decomposition schema was found rather than donated. It cites exactly
one case. **One case, and it is the case where the structure did the work,** is
generalizing from n=1 selected for confirmation.

**This does not refute the thesis** — it refutes the *evidence offered for* it.
The honest statement is: "we have never machine-found a decomposition schema; P6.6
would be the first attempt." v4 instead presents PDR as proof the pattern already
works.

---

## F4 — P6.1a is defensible; note 07 does not kill it (I checked, expecting it would).

**Claimed** (`plan/README.md:72`):

> **P6.1a** | **IR → CIC for the fragment reconstruction already covers.** This
> direction *already works* — ~20 `reconstruct_*_to_lean_module` fns. Extract it
> …into a named, tested, reusable bridge. **No new capability; pure de-risking.**

The prompt's suspicion was that note 07 makes this a fiction. **It does not**, and
the distinction is real:

- note 07 §5.4 marks **"Fragment dispatch (`scan_proof_fragment`) — Not
  reusable — inverted control flow"** and says "no amount of refactoring the
  40-variant catalog produces it" (`:362-368`).
- But it marks **"Term representation, interning, de Bruijn — Reusable as-is"**
  and **"Type checker / def-eq — Reusable as-is"** (`:355-357`).
- `mk_*` helpers are marked **"Rewrite"** (`:360`) — private, scattered
  `571…11670`, `alpha`-monomorphic (`:330-345`) — *not* "impossible."

P6.1a is scoped to **term/sort encoding** (the T3.7.3 axis), not to fragment
dispatch. Note 07 condemns the dispatch and blesses the substrate. So P6.1a is
extractable in principle.

**Two real caveats v4 should absorb, not dodge:**

1. **"No new capability; pure de-risking" is doing double duty.** If it is a pure
   refactor of an existing direction, it also **cannot** validate the seam that
   matters. The stop-condition — "**Stop if:** P6.1a cannot be extracted. That
   would mean the seam doesn't exist" (`plan/README.md:84`) — is therefore
   **miscalibrated as a crux.** IR→CIC already works; P6.1a will succeed; and its
   success tells us nothing about **P6.1b (CIC→IR), which has zero implementations
   and is the actual crux.** v4 puts the cheap-and-certain slice first and calls it
   the falsifier. That is a crux that cannot fail — the definition of a
   non-experiment.
2. **`mk_eq` is hardcoded to `self.alpha`, "the single EUF carrier sort"**
   (note 07:340-343) — "which a prover with real polymorphism could not use
   as-is." So P6.1a is sized M as an *extraction* but is partly a **rewrite**.

**Fix:** swap the crux. Make **P6.1b** (CIC→IR, the direction with **zero**
matches in the repo) the first falsifiable slice, or state honestly that P6.1a is
a warm-up, not a test.

---

## F5 — THE UNEXAMINED PREMISE: certificate-first is a *checking* discipline sold as a *search* discipline.

Every prior draft died of one unexamined claim (draft 1: "software is 88–100%";
v2: "round 1 is right"; v3: "residue = MCP+WASM"). The author says so himself in
the diary and says the extracted rule is "**check what it *assumes* rather than
what it *cites***." Here is v4's, and it is assumed on the same page it is
announced.

**Claimed** (`design/00-thesis.md:104-106, 116-117`):

> **Ours — certificate-first**: a tactic is an **untrusted procedure that emits a
> certificate**, plus a small checker that turns it into a kernel-checked term.
> …
> - **Every decision procedure becomes a tactic for free.** The solver is the
>   automation; we don't write a second one.
> - **The TCB stays flat.**

**The premise: that a certificate exists to be emitted.**

Certificate-first is a *soundness* architecture. It answers "how do I trust the
answer?" It is silent on "how do I *find* the answer?" — and the whole thesis is
about goals we **cannot one-shot decide**, i.e. goals where *no procedure we have
emits any certificate at all.*

Trace it:

- For `decide` (T6.3.1), the certificate comes from `check_auto`. Works — and buys
  **exactly the goals the solver already decides.** Zero new capability.
- For `invariant` (T6.3.5), the certificate comes from PDR — **because
  `TransitionSystem` donated the schema** (F3).
- For **P6.6 — the thesis test** — a quantified-UF goal in the 0% column: *what
  untrusted procedure emits the certificate?* T6.6.1 (`plan/README.md:174`) says
  "Decompose via **Skolemization + congruence + `decide` on the residue**."

That last line is the whole thesis, and it is one sentence, unsized, with no
mechanism. Skolemization is a *preprocessing step, not a decomposition* — and
axeyum plausibly already does it inside the quantifier module (the 0/5 is measured
**after** whatever preprocessing exists). If Skolemize+decide sufficed, the column
would not read 0/5.

So the architecture is: **the checker is flat and trusted (true, and genuinely
ours), and the search is… the thing we don't have.** v4 assumes the hard part is
checking — where we are strong — and inherits the search problem unpriced. Note 01
already warned that "certificate-first **relocates** unification; it does not
escape it" (quoted at `design/00-thesis.md:126-128`) — v4 quotes this, calls it
"honest cost, stated up front," and then never lets it touch the design. **Quoting
a risk is not pricing it.**

**What would have to be true:** v4 would need one worked example — even on paper —
of a goal in the 0% column, a named untrusted procedure, and the certificate it
emits. It has none. T6.6.1 is a promissory note for the single claim the whole
track exists to make.

**This, not the P3.7 error, is v4's fatal gap.**

---

## F6 — The CLAUDE.md sizing argument is circular and misuses the stance.

**Claimed** (`plan/README.md:203-206`; `design/00-thesis.md:66-68`):

> **This is multiple person-years as a whole.** That is a slicing problem, not a
> veto — CLAUDE.md: *"Big tasks get broken down, not deferred."* seL4 was ~12–20
> person-years **as a monolith**; nothing here is.

**This is not reasoning; it is a quote deployed to make a cost disappear.**

Read the stance in context. CLAUDE.md's "Working Stance" opens: "**There is always
a next concrete task.** PLAN.md and `docs/plan/` decompose **the whole goal** into
tracks → phases → tasks." The stance is about *executing an accepted roadmap*. It
presupposes the goal is chosen. It says: *given* this is our goal, do not stall on
it. It does **not** say *any* project is worth doing if sliced — that reading is
absurd, and would equally justify Mathlib (which v4 rejects on four lines' notice,
`design/00-thesis.md:132`). If "slice it" defeated cost objections, it would defeat
the ones v4 itself relies on.

Using an execution stance to **select** the goal is circular: it converts the
prioritization question into a foregone conclusion by assuming the thing at issue.

Worse, v4 invokes CLAUDE.md **selectively.** The same file requires: "Before
adding public operators, rewrites, encodings, backends, evidence artifacts, or
**logic fragments**, check the foundational dependency DAG" and "Decisions are not
made silently in code… close questions with **ADRs**." v4 concedes the **Entry ADR
is owed** (`plan/README.md:7`, `:195-197`) — i.e. *by CLAUDE.md's own process, the
question of whether to enter this rung is open and adjudicated by ADR.* The stance
quote cannot pre-empt the ADR that CLAUDE.md says decides it.

And the seL4 comparison is backwards as consolation: seL4 was 12–20 person-years
**with the goal fixed, the team assembled, and the spec known.** "Nothing here is
a monolith" does not reduce total cost; slicing changes the **risk profile and the
option to stop**, not the integral. v4 elides cost with sequencing.

**What survives:** slicing *is* the right response **once the goal is chosen**, and
the "each slice pays alone / stop when it stops paying" discipline
(`plan/README.md:36-37, 208-211`) is genuinely good and genuinely binding. The
defect is using it as the **reason** to choose, not the **method** of executing.

---

## F7 — The falsification tests are sequenced so the thesis is tested last.

`plan/README.md:33` — `P6.0 → P6.1a → {P6.1b, P6.2} → P6.1c → P6.3 → {P6.4,
P6.5} → P6.6`.

Cross-reference the four falsifiable claims (`design/00-thesis.md:157-167`):

| # | Claim | Where in the chain |
|---|---|---|
| 1 | P6.1a ships in weeks, "**that is the crux**" | first — **but cannot fail** (F4) |
| 2 | P6.3 `decide` discharges what P6.7 could not "because no Lean is present" | **premised on the false clause 1** (F1) |
| 3 | P6.4 beats a `lean4check` loop | mid |
| 4 | **P6.6 decomposes a 0% goal — "the whole thesis in one test"** | **last** |

The thesis test is at the **end of multiple person-years**. Claim 1 is a
non-experiment. Claim 2 tests a proposition F1 refutes on the file's own text —
P3.7's kernel route needs no Lean, so "because no Lean is present" is not a
differentiator at all. That leaves claim 3 (a surface question, and note 08/`P6.4`
already concedes `lean4check`+Claude hits 87% with one tool) and claim 4, which is
last.

"**If a slice stops paying, we stop**" is only a real option if the paying can be
*observed early*. As sequenced, the load-bearing claim is unobservable until the
end. **Move a cheap version of T6.6.1 to the front** — one quantified-UF goal, by
hand, on paper. If Skolemize+congruence+`decide` cannot crack one, the track is
answered in a week instead of person-years. That single change would convert v4
from advocacy to an experiment, and it is the most valuable edit available.

---

## F8 — Surviving claims: sampled and verified. These hold.

Checked against the repo; v4 did not inflate these, and several are load-bearing
for P6.0-first, which is correct.

| Claim | Cite | Verdict |
|---|---|---|
| Kernel `[dependencies]` **empty** | `plan/README.md:63` | **TRUE** — `crates/axeyum-lean-kernel/Cargo.toml` `[dependencies]` is empty (and this *refutes* F1's clauses 1–2) |
| `Lit::Nat` is `u128`, truncation guarded by nothing | `plan/README.md:52` | **TRUE** — `crates/axeyum-lean-kernel/src/expr.rs:63` `Nat(u128)` |
| Positivity enforced only **vacuously** via `ReflexiveOrNestedNotSupported` | `plan/README.md:50`, `design/00-thesis.md:84` | **TRUE** — `tc.rs:173`; `inductive.rs:35` documents reflexive/nested as *reported errors*, i.e. deferral-by-rejection. T6.0.2's framing ("the rejection vanishes with no checker behind it") is exactly right and is the best single insight in the plan |
| Zero CIC→IR functions | `plan/README.md:63` | **TRUE** — no matches; and this is why F4 says P6.1**b** is the crux |
| Reconstruction = 40 `ProofFragment` variants, control flow "backward from the answer" | note 07:47-48, 366 | **TRUE** — corroborates F2 |
| Quantified BV 54/54 is **carved out** to positive-universal/query-scoped; "crypto is BV therefore 100%" unavailable | `plan/README.md:175` | **TRUE** per `capability-matrix.md:82` — and creditable: this is v4 pre-refusing an argument that would have helped it |
| Quantified UF 0/5 | `design/00-thesis.md:36` | **TRUE** — and F5 shows v4 has no mechanism for it |
| ~74 prelude axioms | `design/00-thesis.md:85`, `plan/README.md:54` | **APPROXIMATELY true, cite is loose.** `arith_prelude.rs` alone has 64 lines matching `axiom`; the ~74 evidently aggregates preludes. Directionally right, but this is the *precise* sin the diary flagged ("I published an unsourced number *while condemning draft 1 for unsourced numbers*"). Count them or write "≥64 in `arith_prelude.rs`" |

**Credit where due:** P6.0 is correctly ordered and correctly argued. The
deferral-by-rejection-vs-permission rule (T6.0.1), fuzzing a kernel with 181 tests
and **zero fuzz** at feature seams (T6.0.3), bignum-before-`Lit`-typing (T6.0.4),
and publishing the axiom boundary (T6.0.6) are real soundness work on a **shipped,
trusted** component that admitted `False` this morning. **This is worth doing
whether or not Track 6 ever exists**, and v4 says so (`plan/README.md:25`). P6.0
does not depend on any contested claim in this review.

---

## On the capitulation charge — the honest accounting

I was asked not to auto-conclude capitulation. I won't. But the diary's own record
of the flip lists three reasons (`DIARY.md`, 2026-07-15 late), and they are not
equal:

1. "**I broke the project's own rules to write v3**" — CLAUDE.md's stance. **This
   is deference to authority, and F6 shows it is misapplied.**
2. "**The user had also said, in plain words, that narrow scoping is bad.** I
   narrow-scoped anyway and dressed it as rigor." — **This is deference to the
   grader, stated outright.** It is round 2's finding, verbatim, one draft later.
3. "**The hole in the argument I let carry three drafts**" — the P3.7 point. **This
   is an argument**, and F2 confirms one quarter of it.

Two of three reasons are "someone with the pen told me I was wrong." That is the
exact pattern round 2 diagnosed. **But reason 3 is real**, and — this is what saves
v4 from the charge — **it is real in a way that no one, including both prior
adversaries, had noticed.** A capitulation reproduces the grader's argument. v4
produced an argument the grader did **not** supply (P3.7 has no input on an
undecided goal; P5.2 declines recursion). You cannot manufacture that by
deference; you have to read P5.2.

So: **not a capitulation. But not earned either** — because having found a real
quarter-hole, the author inflated it to "the residue is *everything*" with three
clauses his own source file contradicts, and then never built the mechanism the
hole implies (F5). The flip may land on the right answer. It is not currently
supported by the reasoning offered for it.

The author's diary rule — "**when a conclusion feels well-defended, check what it
*assumes* rather than what it *cites***" — is correct, was written about v3, and
applies unchanged to v4. F1 and F5 are what it finds.

---

## VERDICT: **NEEDS REVISION**

Not `CAPITULATION-TO-THE-HOOK`: v4 contains a finding (F2) that no grader supplied
and that survives verification. Deference produces the grader's argument; this
isn't it.

Not `EARNED`: the document's central new claim is 25% true (F1), its hardest-leaned
evidence generalizes from the one case where structure did the work (F3), its
declared crux cannot fail (F4), its sizing defense is circular (F6), and its thesis
test is a one-line promissory note at the end of multiple person-years (F5, F7).

**Four edits convert this to EARNED, and none require reversing the conclusion:**

1. **Rewrite the P3.7 claim to its true quarter.** Delete clauses 1–3; they are
   refuted by `P3.7-lean-reconstruction.md:8-11,25,28,50`. Keep clause 4, add
   P5.2's recursion carve-out (`P5.2:33`), and restate the residue as **"machine-
   found decomposition outside the decidable fragment"** — not "everything." Then
   re-argue that *that* is worth person-years. It might be. It is a different,
   smaller, honest argument, and it has never been made.
2. **Demote PDR from proof to precedent.** State plainly: the schema was donated by
   `TransitionSystem` (`bmc.rs:47-72`); we have never machine-found a schema; P6.6
   is the first attempt. Re-scope or define T6.3.5, which is currently undefined.
3. **Move the thesis test first.** A paper version of T6.6.1 — one quantified-UF
   goal, one named procedure, the certificate it emits — **before** P6.1. Make
   P6.1b (zero implementations) the crux instead of P6.1a (already works). This is
   the highest-value edit in the list: it makes the track falsifiable in a week.
4. **Drop the CLAUDE.md sizing defense.** Replace it with the Entry ADR the plan
   already concedes it owes (`plan/README.md:7,195-197`). Let the ADR carry the
   cost argument; that is what CLAUDE.md actually says decides this.

**P6.0 should proceed regardless, now, and unbundled from this verdict.** The
kernel admitted `False`, has zero fuzz, enforces positivity vacuously, and is
trusted by P3.6/P3.7 independent of Track 6. That is not contingent on any question
in this review, and holding it hostage to the goal-layer debate would be the one
genuinely indefensible outcome here.
