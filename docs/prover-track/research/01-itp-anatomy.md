# The Anatomy and Design Space of Proof Construction Above a Kernel

Research note. Status: survey + orientation for the axeyum prover track.
Date: 2026-07-15. Last reframed: 2026-07-15.

Context: axeyum has `crates/axeyum-lean-kernel` (~15.5k LoC Rust: CIC, universes,
dependent Pi, inductives + recursors, WHNF, defeq, trusted admission gate) and
**nothing above it**. This note maps the *design space* of what "above it" can
contain, what each choice costs, and what it buys.

**Framing — this note is not a gap list.** We are not trying to reproduce Lean.
Lean *compatibility* (consuming and emitting artifacts a Lean kernel accepts) is
an asset worth keeping; Lean *imitation* (reproducing MetaM, the elaborator
surface, Mathlib's tactic culture) is a trap that costs person-decades and buys
little that a certificate-first culture doesn't already reach another way. Lean
appears below as **one well-documented point in the space**, cited heavily
because it is the best-instrumented — not because it is the target. Read every
"Lean does X" as "X is one option, and here is its price."

Section map: **§0** the design space (three architectures, including one nobody
takes); **§1** Lean as a worked example of the proof-term point; **§2** the
de Bruijn criterion and the empirical soundness-bug record; **§3** LCF vs.
proof-term in the abstract; **§4** other points in the space; **§5** what is
genuinely hard; **§6** sizing.

---

## 0. The design space

Three architectures for "how does a claim become trusted." They are usually
presented as two. The third is the interesting one for us.

### 0.1 LCF discipline (Isabelle/HOL, HOL Light, HOL4)

The rules of the calculus are sealed in an abstract data type `thm` in a
strongly-typed host language. The *only* values of `thm` are axiom instances and
the results of inference-rule operations — there is no other constructor. Tactics
are **ordinary host-language functions**; they need no privilege because the type
system is the guard. Proofs are *performed but not recorded*: the system
remembers results, not steps
([Paulson, "The de Bruijn criterion vs the LCF architecture"](https://lawrencecpaulson.github.io/2022/01/05/LCF.html)).

- **Buys:** a tiny trusted base (HOL Light: a few hundred lines of OCaml).
  Zero proof-object memory cost. Tactic authors cannot be unsound *no matter what
  they write* — worst case they fail. Extensibility is free.
- **Costs:** proofs are ephemeral. Nothing to hand a third party; no independent
  re-checking; reproducing a result means re-running the prover. You trust *this*
  implementation of the ADT — and the host language's abstraction guarantee (an
  `Obj.magic`, a broken module seal, a host bug, and it is over).

### 0.2 de Bruijn / proof terms (Automath, Rocq, Lean, Agda)

Generation and checking are **independent programs**: the prover emits a term, a
small kernel checks it (§2.1).

- **Buys:** the artifact is real and portable. Anyone with a checker verifies it —
  including one they wrote themselves, in another language. The search engine may
  be arbitrarily untrusted: buggy, heuristic, ML-driven, adversarial. This is
  precisely axeyum's stated identity: **untrusted fast search, trusted small
  checking.**
- **Costs:** proof objects fill memory — the chief drawback already visible in
  Stanford LCF, and the reason Rocq users deploy so many tricks to reduce the
  burden (Paulson, ibid.). The kernel is larger than a `thm` ADT because it must
  implement defeq, universes, and recursor reduction. And a bigger kernel has
  bugs (§2.3).

### 0.3 The third option: certificate-first construction

Nobody in the ITP world takes this as the *primary* idiom, and axeyum is
unusually positioned for it — because it is already how the SMT side works.

A "tactic" is neither a function returning `thm` (LCF) nor a function building a
proof term (Lean). It is a **procedure that emits a certificate in a format with
an independent checker**. The certificate is the interface; a kernel term, if
wanted at all, is a derived artifact.

The precedents exist in pieces, unassembled: DRAT/LRAT (axeyum has both a
producer and `check_drat`), SMT proof formats (Alethe, LFSC, veriT), Rocq's
reflective tactics (`ring`, `micromega`/`lia` — literally "emit a certificate,
check it by computation"), and Lean's `bv_decide` (§1.5). Isabelle's Sledgehammer
is the same shape socially: untrusted external ATPs search, reconstruction
produces the `thm` (§4).

- **Buys:** each tactic's trust story is **local and testable in isolation**. A
  per-class checker is small enough to fuzz to death — which is exactly the muscle
  this repo already has (differential fuzzing, soundness-negative tests, corpus
  sweeps, degenerate-argument seed classes). It is also the natural interface for
  **agent drivers**: an agent emits a candidate certificate, a checker accepts or
  rejects, and no agent ever needs privileged access to a `Thm` constructor.
  Rejection is *data*, not a crash. And a checked certificate is immune to the
  brittleness that kills tactic scripts (§5.8): it does not care about goal order
  or hypothesis names.
- **Costs:** a format per tactic class, and N classes means N formats and N
  checkers absent a common substrate. Certificate→term reconstruction can be
  slower than direct construction — this is the known bottleneck in SMT-to-ITP
  integration.
- **The substrate question is CLOSED — see [`11-dedukti-and-substrates.md`](11-dedukti-and-substrates.md).**
  This note called λΠ-modulo "a serious candidate"; it was researched afterwards
  and **rejected**. Dedukti *grows* the TCB (small kernel **+** your rewrite theory
  **+** external confluence (CSI^HO) **+** termination (SizeChangeTool) **+** an
  adequacy proof). Logipedia's multi-system export is not free — it weakens content
  to *constructive simple type theory* first — and no Dedukti bit-vector theory
  carrying real BV proofs exists (that literature is LFSC/CVC4). CoqInE has chased
  CIC universe polymorphism since ~2012 and was still chasing it in 2024. **And
  three of the translated libraries this note cites below — Holide, Focalide,
  Universo — have since fallen off Deducteam's own software page.** Read the
  original claim as of its date, not as current.
- The original claim, for the record: λΠ-calculus modulo rewriting is a
  serious candidate: Dedukti implements LF + rewriting, and libraries from HOL
  Light, Matita, Zenon modulo, iProverModulo and FoCaLiZe have been translated in
  and checked
  ([Dedukti](https://www.semanticscholar.org/paper/Dedukti-:-a-Logical-Framework-based-on-the-%CE%BB-Modulo-Assaf-Burel/b83480c7d1578d8e6eb57fa1fda46d051a715ace);
  [Translating HOL to Dedukti](https://arxiv.org/pdf/1507.08720);
  [Logipedia](https://arxiv.org/pdf/2305.00064)). A Dedukti-family checker
  (Kontroli) was built specifically to be safe, fast and *concurrent*
  ([CPP'22](https://arxiv.org/pdf/2102.08766)) — evidence the small-checker story
  survives real libraries and real performance needs.

### 0.4 Summary — and the point that they are not exclusive

| | trusted base | artifact | can a tactic be unsound? | independent re-check |
|---|---|---|---|---|
| LCF | tiny ADT + host language | none (ephemeral) | no (type-sealed) | no |
| de Bruijn | kernel (defeq, universes, inductives) | proof term | no (kernel rejects) | yes |
| Certificate-first | per-class checker (small, fuzzable) | certificate (+ derived term) | no (checker rejects) | yes, per class |

The live option for axeyum is **all three at once**: a de Bruijn kernel (built),
a sealed Rust `Theorem` newtype over it (LCF's cheap win — §3.3), and
certificate-emitting procedures as the primary tactic idiom (our existing
culture). No system has assembled this combination, and the reason looks
historical rather than principled: LCF systems could not afford proof objects in
1979, and CIC systems inherited a human-first surface.

---

## 1. Lean 4 as a worked example of the proof-term point

Lean is the best-instrumented system in the space, so it is the most useful
specimen. Everything here is *one set of answers*, priced — not a specification.

### 1.1 The split

Lean is a *de Bruijn criterion* system (§3): the kernel is a small, independent
proof-term checker; everything else is untrusted machinery that *produces* terms
for it to check.

**Inside the kernel** ([Type Checking in Lean 4, "Trust"](https://ammkrn.github.io/type_checking_in_lean4/trust/trust.html);
[Lean4Lean, arXiv:2403.14064](https://arxiv.org/html/2403.14064v3)):

- Core CIC: `Expr` (bvar/fvar/mvar/sort/const/app/lam/forallE/letE/lit/mdata/proj),
  universe levels + constraint checking.
- Type inference and **definitional equality** (WHNF, δ/ι/β/η, structural eta,
  proof irrelevance, quotient reduction).
- Inductive type admission: positivity, universe computation, recursor
  generation, ι-reduction rules.
- Quotient types (`Quot.mk`/`lift`/`ind`) as a primitive.
- Primitive projections, nested inductives.
- **Accelerators**: GMP-backed `Nat` literals with ~15 built-in arithmetic
  functions, and `String` literals. These exist purely for performance and are
  a documented source of TCB growth.
- `reduceBool`/`reduceNat` native reduction hooks — *not* verified; using them
  (`native_decide`) pulls the entire Lean compiler into the TCB.

**Outside the kernel** — and therefore *untrusted*, which is the whole point:
parser, macro expander, elaborator, typeclass resolution, unifier, tactic
framework, `simp`, `omega`, `decide`, `bv_decide`, `grind`, the compiler, the
IDE. Per the trust page: tactics "do *not* need to be trusted *at all*" because
they emit kernel terms.

### 1.2 Size

The Lean 4 kernel is commonly cited at **~5–6k lines of C++**, with inductive
families adding ~700 more
([Grokipedia summary](https://grokipedia.com/page/Lean_(proof_assistant));
[Lean system description](https://lean-lang.org/papers/system.pdf)). Treat the
exact figure as approximate — it has grown with `Nat`/`String`/projections.

The ratio that matters: **kernel ≈ 6k lines; the rest of Lean 4 is on the order
of hundreds of thousands**. Elaborator + tactic framework + `simp` + the standard
library dwarf the kernel by ~50×. That ratio *is* the LCF/de Bruijn bargain.

axeyum's kernel at 15.5k Rust LoC is already ~2.5× Lean's C++ kernel. Rust is
more verbose, but this is worth watching: **kernel LoC is a liability, not an
asset.** Every line is trusted.

### 1.3 The elaborator — the part that is actually hard

`Syntax → Expr` is where the person-years go. It is responsible for:

- **Implicit argument insertion** (`{x : α}`, strict-implicit `⦃⦄`,
  instance-implicit `[Inst]`), and deciding *when* to insert (eager vs. postponed).
- **Unification**, including **higher-order pattern unification** (Miller
  patterns: `?m x₁ … xₙ` with distinct bound fvars ⇒ unique solution). Outside
  the pattern fragment, HOU is undecidable; Lean uses heuristics and postponement.
  This is the single largest source of "why doesn't my proof elaborate" pain.
- **Typeclass resolution** — tabled/memoized backward search over instances, with
  diamond/defeq issues (`Monad`/`Applicative` hierarchies, `outParam`).
  Notoriously performance-sensitive; a mis-set priority can blow up compile time.
- **Coercions** (`↑`, `CoeT`/`CoeHead`/`CoeTail` chains, coe-to-function,
  coe-to-sort).
- **Elaboration postponement**: `Syntax` elaborates to `Expr` with holes
  (metavariables) that get solved later; the elaborator is fundamentally a
  constraint solver, not a translator.

#### 1.3.1 Essential vs. Lean-specific accident

The list above is *Lean's* answer. Decomposed by what it buys and whether it is
forced:

| Feature | What it buys | Essential? |
|---|---|---|
| Implicit args + unification | `f a b` not `@f α β inst a b` — makes dependent types *writable* | **Essential if humans write terms.** Not if terms are machine-generated. |
| Typeclass resolution | ad-hoc polymorphism, algebraic hierarchy, `Decidable` inference | Essential *for a Mathlib-scale library*. A proof-search problem in disguise; Lean needed a whole tabled-resolution procedure for performance ([Lean 4 paper](https://link.springer.com/chapter/10.1007/978-3-030-79876-5_37)). |
| Coercions | `(n : ℕ) + (r : ℝ)` works | Convenience. Price: coercion diamonds. |
| Hygienic macros / notation | user-extensible syntax without capture bugs | Lean's distinctive bet ([Beyond Notations](https://arxiv.org/abs/2001.10490)). Good work; genuinely optional. |
| Overloading, `do`-notation, deriving | ergonomics; programming-language ambitions | Lean-specific. **Lean is a programming language as well as a prover**, and much of the elaborator serves that second identity — which axeyum does not have. |

**The observation that matters:** most of elaboration exists to close the gap
between *what a human wants to type* and *what the kernel demands*. The size of
that gap is a function of **who writes the terms.**

If the writers are agents and certificate-emitting procedures, the gap differs in
kind: machines do not mind `@f α β inst a b` and do not need coercions — but they
*do* need unification (to be goal-directed at all) and *do* benefit from something
typeclass-shaped (to find the right lemma). So "agents don't need elaboration" is
**too glib**: an agent writing explicit terms needs a type checker with
*machine-parseable* errors, and an agent searching needs metavariables. What
agents plausibly don't need is the **surface-syntax half** — notation, macros,
coercion insertion, overloading — which is also the larger and more
accident-laden half, and the half that poisons error messages (§5.6).

**What logical frameworks show about the floor.** Dedukti's answer is that a very
small core (λΠ + rewriting) can host *many* logics, including CoC-strength ones,
by **encoding rather than by growing the kernel**
([Embedding Pure Type Systems in λΠ-modulo](https://www.researchgate.net/publication/220727323_Embedding_Pure_Type_Systems_in_the_Lambda-Pi-Calculus_Modulo)).
The trade is explicit and instructive: **it has essentially no elaboration at
all.** It is not for humans to write in — it is for machines to emit into and
checkers to read. Logipedia demonstrates this past toy scale. That is a real,
working point in the space, and much closer to axeyum's culture than Lean's is.

**The cost of skipping elaboration, stated plainly:** a system with no elaborator
is one **humans will not author proofs in**, hence one that will not grow a
library, hence one whose lemma stock must come from *import* or *generation*.
That is a strategic commitment, not a free lunch — and it makes someone else's
library your dependency and their refactors your problem (§6).

### 1.4 The tactic framework

The monad stack is the architecture
([Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html),
[ch. 9](https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html)):

```
CoreM      -- Environment (constants), name generation, options, exceptions
  ↳ MetaM    -- + MetavarContext + LocalContext: isDefEq, whnf, inferType,
             --   forallTelescope, mkFreshExprMVar
    ↳ TermElabM -- + elaboration state: postponed elaboration problems,
                --   synthetic mvars, coercion insertion
      ↳ TacticM -- + the goal list ([MVarId])
```

The pivotal design decision: **a goal *is* a metavariable**. `MVarId` carries a
target type and a `LocalContext` (its hypotheses). A tactic "closing a goal" is
literally `MVarId.assign mvarId proofTerm`. `intro` creates a new mvar with an
extended local context and assigns the old one to a `lam` around it. Proof
construction and goal management are the same mechanism. This is elegant and it
is why Lean tactics compose.

Consequences worth internalizing:
- **Delayed assignment** mvars exist to handle `Expr` under binders — a wart, but
  a necessary one.
- You must check `isDefEq` between an mvar's type and its assignment; the
  metaprogramming book flags failing to do so as a standard bug class.
- Tactic *soundness* is not a concern (kernel re-checks). Tactic *usability* is
  the entire product.

#### 1.4.1 Is a metavariable/goal representation genuinely unavoidable?

**Essentially yes, for goal-directed proof.** "Goal-directed" *means* working
backwards from an unknown to be filled, and "an unknown to be filled" is a
metavariable under some name. The only choice is how explicit and principled the
representation is:

- a **hole in a term** (Lean's `MVarId`);
- a **subgoal in a sequent** (classic LCF tactics: a goal list + a validation
  function — same content, less general, *no dependency between goals*);
- a **hypothesis in a certificate to be discharged** (the §0.3 idiom).

What *is* avoidable is the expensive version: **dependent** metavariables, where
solving one goal changes the *type* of another, plus delayed assignment,
postponed unification constraints, and universe metavariables. That machinery is
most of why `MetaM` is big. A system whose goals are non-dependent — or whose
dependencies are resolved before search begins — gets a dramatically smaller
engine. This is roughly why HOL's tactic layer is so much smaller than Lean's,
and it is a **fragment choice, not a cleverness gap** — exactly the kind of
choice this repo makes well (cf. ADR-0014's first arithmetic fragment,
ADR-0025's bounded strings).

**The minimal machinery, honestly:** a goal type, a context, a way to say "this
goal is discharged by *this* evidence," a composition combinator (sequencing +
alternation), and a final check. Everything else — backtracking disciplines,
focusing, monadic state, hygiene — is scale management, and should be bought only
when scale demands it.

**The ceiling on typed tactic languages.** Ltac2 is the deliberate do-over for
Ltac1, consciously ML-lineage — noting that *historical ML was itself designed as
the tactic language for the LCF prover*
([Ltac2 docs](https://rocq-prover.org/doc/V8.19.0/refman/proof-engine/ltac2.html)).
The instructive admission is that even Ltac2 **cannot statically guarantee the
resulting term is well-typed**; well-typedness is deferred to dynamic checks, a
conscious concession (ibid.). You can type the *meta* level; the object level
stays dynamic unless you go fully dependent. So a typed tactic DSL buys
maintainability, not soundness — soundness already came from the kernel.

### 1.5 The automation tier — and the one that matters most for axeyum

| Tactic | Mechanism | Trust route |
|---|---|---|
| `decide` | `Decidable` instance, kernel evaluates it by ι/δ-reduction | Kernel only |
| `native_decide` | Compiles the `Decidable` instance, runs native code | **Compiler in TCB** (`ofReduceBool`) |
| `simp` | Untrusted rewriting; emits a chain of `Eq.mpr`/congruence lemmas | Kernel-checked proof term |
| `omega` | Linear integer/nat arithmetic (Omega test) | Certificate → proof term |
| `bv_decide` | **Bit-blast → CNF → external SAT (CaDiCaL) → LRAT certificate → verified checker run by reflection** | See below |
| `grind` | E-graph congruence closure + E-matching + linear arith + case splitting; SMT-inspired | Proof term |

**`bv_decide` is axeyum's own architecture, already built.** It bit-blasts a
QF_BV goal, ships it to a SAT solver, gets an **LRAT** UNSAT certificate, and
checks that certificate with a *verified-in-Lean* checker
([leansat](https://github.com/leanprover/leansat/blob/main/README.md);
[Lean.Elab.Tactic.BVDecide](https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/BVDecide.html)).
`bv_check file.lrat` replays a stored certificate without a solver present.

Two things to note, both directly decision-relevant:

1. This is **exactly** axeyum's "untrusted fast search, trusted small checking"
   identity, and axeyum already has the search half (`axeyum-bv` → `axeyum-cnf`
   → DRAT checker + proof-producing CDCL).
2. **Lean's version has a TCB compromise axeyum does not need to make.** Because
   the LRAT checker is run via reflection/`ofReduceBool`, `bv_decide` proofs
   depend on the Lean *compiler*. Lean took that hit because building explicit
   proof terms for every LRAT step "would exhaust memory"
   ([LRAT-Catcher, arXiv:2607.00815](https://arxiv.org/pdf/2607.00815);
   [PBLean, arXiv:2602.08692](https://arxiv.org/html/2602.08692v1)). Axeyum's
   `check_drat` is a *native Rust* checker outside any proof term — same
   engineering pressure, different resolution. **This tension (reflection vs.
   proof terms vs. external checker) is the central design question of the
   axeyum prover track** and §3 is about it.

`grind` (Lean ≥ v4.22, Morrison + de Moura) is the newest tier: congruence
closure over an E-graph, E-matching, linear arithmetic, case splitting — "a
tactic inspired by SMT solvers". Note the direction of travel: **Lean is growing
an SMT solver inside its tactic layer.** Axeyum is an SMT solver growing a kernel.
The two projects are converging on the same artifact from opposite ends, and
axeyum has `axeyum-egraph` already in tree.

---

## 2. The de Bruijn criterion, kernel diversity, and real soundness bugs

### 2.1 The criterion

A system satisfies the **de Bruijn criterion** if it generates proof objects
checkable by an *independent, simple* program that "a skeptical user could write
him/herself" — coined by Barendregt & Geuvers after de Bruijn's Automath, whose
checker fit in **~200 lines**
([PLS Lab](https://www.pls-lab.org/en/de_Bruijn_criterion);
[Geuvers, *Proof Assistants: history, ideas and future*](https://www.cs.ru.nl/~herman/PUBS/proofassistants.pdf);
[Barendregt & Geuvers, *Proof-Assistants Using Dependent Type Systems*](https://www.infomath-bib.de/tmp/data/Proof-assistants-using-dependent-type-systems.pdf)).

The operative property: **proof generation and proof checking are independent
programs.** Wiedijk's comparison of systems scores exactly this, alongside the
*Poincaré principle* (computation need not be recorded step-by-step)
([The Seventeen Provers of the World](https://www.cs.ru.nl/~freek/comparison/comparison.pdf)).

Note the deep tension: **the Poincaré principle is what makes defeq expensive and
the kernel big.** Lean's `Nat` GMP acceleration, Coq's `vm_compute`/
`native_compute`, and `bv_decide`'s reflection are all Poincaré-principle
concessions, and *every one of them has been a soundness-bug site* (§2.3).

### 2.2 Kernel diversity in practice

- **Lean**: `lean4checker`, **`nanoda`** (Rust!), `trepplein` (Scala, Lean 3 only),
  **Lean4Lean** (Lean 4 kernel in Lean 4, by Carneiro). Lean4Lean checks all of
  Mathlib at **20–50% slower** than the C++ kernel — i.e. *an independent kernel
  is affordable*. `nanoda` is incomplete w.r.t. all of Mathlib
  ([Lean4Lean](https://arxiv.org/html/2403.14064v3);
  [lean4lean repo](https://github.com/digama0/lean4lean)).
- **HOL Light**: the extreme of LCF minimalism — a few hundred lines of OCaml
  defining `thm` as an abstract type. Small enough that its soundness has been
  proven in HOL Light itself (Harrison) and in Isabelle/HOL (Kumar et al.,
  CakeML-verified HOL Light).
- **Metamath**: the extreme of the de Bruijn criterion. Proofs are pure
  substitution steps over a trivial grammar; **verifiers are routinely written in
  a weekend** (mmverify.py is a few hundred lines) and there are dozens in
  different languages. Highest checkability, no automation, no types.
- **Dedukti**: λΠ-calculus modulo rewriting as a *universal proof checker* —
  logical frameworks target it so that proofs from Coq/HOL/Matita can be checked
  by one small kernel. The "kernel as interchange format" play.
- **Isabelle**: LCF `thm` kernel, but *optionally* records proof terms — proving
  the two designs are not mutually exclusive.

**Takeaway**: the de Bruijn criterion's payoff is *empirically real* — it is why
independent Lean checkers exist at all, and why Lean4Lean could find kernel bugs
"entirely theoretically".

### 2.3 Actual kernel soundness bugs — the historical record

This is the most important empirical evidence in the note. **Kernels are small
and they are still wrong, repeatedly, for years at a time.**

**Rocq/Coq** maintains a public
[`dev/doc/critical-bugs.md`](https://github.com/rocq-prover/rocq/blob/master/dev/doc/critical-bugs.md).
Sampled categories and their **latency in the wild**:

| Bug | Versions affected | Latency |
|---|---|---|
| Template polymorphism not collecting side constraints on a parameter's universe level | V8.4 – V8.9, fixed V8.10.0 (Aug 2019) | **~5 years** |
| Universe polymorphism can capture global universes | V8.5 – V8.8 | ~3 years |
| Guard checker forgets to check non-structural arguments of fixpoint | V8.16 – V9.0.0 | multi-year |
| Guard checker incorrectly detects `match` on `match` as returning a subterm | V8.16 – V9.0.0 | multi-year |
| Guard checker does incorrect reduction across inner fixpoint, accepts wrong fixpoints | V8.16 – V9.0.0 | multi-year |
| Missing substitution when strengthening functors (module system) | V8.5 – V9.0.0 kernel-side | **~10 years** |
| Primitives incorrectly considered convertible to anything by module subtyping | V8.11.0 – V8.18.0 | ~3 years |
| Conversion compares the *mutated* version of primitive arrays (all three conversion machines) | V8.13 – V8.16.0 | ~2 years |
| Arbitrary code execution on arrays of floats | V8.13.0 – V8.14.0 | ~1 year |
| `native_compute`: Coq→OCaml identifier translation not bijective ⇒ **identifies `True` and `False`** | V8.5 – V8.5pl1 (May 2016) | months |
| Records with primitive projections became recursive without updating the guard condition | — | — |

Structural lessons, in order of importance for axeyum:

1. **Every acceleration is a soundness site.** VM/native compute, primitive
   arrays, primitive projections, `Nat` bignums. The Poincaré principle is where
   kernels bleed.
2. **Universe handling is the #1 recurring category.** Template polymorphism,
   algebraic universe subtyping, global universe capture. Universes are subtle in
   a way positivity is not.
3. **The guard/positivity checker is the #2 category**, and its bugs cluster
   (three separate V8.16-era guard bugs).
4. **Latency is measured in years**, not weeks — including in the most-scrutinized
   kernel in the field, with a dedicated `coqchk` re-checker.

**Lean 4**: Lean4Lean documents that when the kernel was extended for performance
(bignum arithmetic, nested inductives, primitive projections), "some soundness
bugs crept in", and translating C++→Lean found several more. The flagship
example: the kernel caches the largest unbound de Bruijn variable in a **20-bit
field**; on overflow the code called `panic!()` which "signals an error on stdout
but then continues execution with the default value … 0 for UInt64" — *the worst
possible answer*, since 0 enables incorrect optimizations. Carneiro: "a nice
example of a bug that was found entirely theoretically." The fix made
`looseBVarRange` opaque but the paper notes remaining reliance on "unsound
assumptions" about overflow bounds ([arXiv:2403.14064](https://arxiv.org/html/2403.14064v3)).

Directly relevant to axeyum's Rust implementation: **a panic-continues-with-default
in a cached expression-metadata field was a real kernel soundness bug.** Any
axeyum `Expr` metadata cache (loose-bvar range, has-mvar, hash) must saturate or
hard-abort, never silently default.

Also: **`native_decide` leakage** is a live, known soundness hole class in Lean
([Zulip: soundness bug: native_decide leakage](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/soundness.20bug.3A.20native_decide.20leakage.html)).
And [lean4#7637 "type theory edge case: projections and sort polymorphism"](https://github.com/leanprover/lean4/issues/7637)
shows the frontier is still open.

**Non-termination is by design, not a bug.** Lean's type theory is **not strongly
normalizing**: Coquand and Abel constructed a counterexample combining
**impredicativity + proof irrelevance + subsingleton elimination**, and it bites
ordinary defeq checks, not just exotic proof terms. Lean4Lean handles this with a
**fuel parameter, depth limit 1000**, which suffices for all of Mathlib. *A
dependent-type kernel needs a fuel/depth budget as a first-class parameter, and
that is normal, not a hack.*

### 2.4 The Prop large-elimination hole — found and fixed in-tree (resolved)

**The rule.** Most inductive *propositions* may eliminate only into `Prop`.
Allowing a general `Prop` inductive to eliminate into `Type` is **inconsistent
with proof irrelevance**: if `p q : P` are definitionally equal, but a recursor
lets you extract *which constructor / which data* built the proof, you get a
function that must return two different values on definitionally-equal inputs ⇒
`False`.

The exception is **subsingleton elimination** (a.k.a. singleton / large
elimination), permitted only under a **conservative syntactic criterion**
([Lean reference, Inductive Types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)):

> A proposition qualifies as a subsingleton iff:
> 1. **There is at most one constructor**, and
> 2. **every non-recursive constructor argument is either itself a proposition,
>    or appears in the output (index) type.**

That is precisely why `Eq`, `False`, `And`, `Acc` large-eliminate but `Or` and
`Exists` do not. It is a *syntactic under-approximation of "is a subsingleton"* —
deliberately conservative, because getting it wrong is unsoundness. (Historically,
Gabriel Ebner had to write a checker for the Lean 3 HoTT library that *rejects*
uses of singleton elimination, since it is also what breaks univalence — see
[Zulip/HoTT discussion](https://groups.google.com/g/homotopytypetheory/c/RxXqHX8W6Dw).)

**The historical finding (contained by ADR-0165).** At commit `2cb298e2`,
`crates/axeyum-lean-kernel/src/inductive.rs` stated that among the deferred items
were "the `Prop`-subsingleton large-elimination subtleties", and then:

> `//! The motive is always allowed to eliminate into an arbitrary `Sort v` here.`

Meanwhile `crates/axeyum-lean-kernel/src/tc.rs` implements
`proof_irrel_eq` (modelled on nanoda's `proof_irrel_eq`) and it is wired into the
defeq path at `tc.rs:916`.

**Those two facts together were the classical unsoundness.** The kernel had
(a) definitional proof irrelevance and (b) unrestricted large elimination for
`Prop`-valued inductives. The standard exploit shape was:

```lean
inductive B : Prop where | t : B | f : B
-- recursor generated with motive : B → Sort v, v arbitrary
def d (b : B) : Bool := B.rec true false b
-- d B.t ≡ true, d B.f ≡ false by ι
-- but B.t ≡ B.f by proof irrelevance ⇒ true ≡ false ⇒ False
```

**This was not hypothetical.** Commit `2cb298e2` preserved a complete term that
the trusted gate admitted as `theorem bad : False`. Commit `d26ad887` now applies
Lean's exact syntactic-subsingleton criterion, and the same complete exploit is
an active negative regression. The pinned real-Lean gate in `a10c8cde` checks a
regenerated restricted `Prop` recursor and its iota behavior.

**Resolution.** [ADR-0165](../../research/09-decisions/adr-0165-lean-compatible-prop-large-elimination.md)
records the rule, the adversarial universe/field matrix, the former-exploit
inversion, and a mandatory external compatibility gate. Commit `d26ad887`
applies the two-clause syntactic criterion in recursor generation: compute an
`elim_level` for the inductive; if its sort is `Prop` and it fails the criterion,
the motive is constrained to `Prop`. The complete former exploit is now an active
negative regression, and the pinned real-Lean gate in `a10c8cde` checks a
regenerated restricted `Prop` recursor and its iota behaviour. This closes the
P0; it does **not** by itself prove complete equivalence with Lean's kernel.

Residual work the record says to expect:

- The criterion needs care under **universe polymorphism** (`Sort u` that *might*
  be `Prop`) — exactly the recurring universe-bug category of §2.3, so the
  conservative answer (constrain unless provably not `Prop`) is the right one.
- A fuzz seed-class generating `Prop` inductives with 0/1/2+ constructors and with
  data fields present/absent from the output type — mirroring CLAUDE.md's hard
  rule about degenerate-argument fuzz classes for partial operators.

**Why this episode is the most useful evidence in the note.** It is a live,
in-tree instance of the exact bug family §2.3 catalogues (impredicativity ×
proof irrelevance × elimination), it was found by *reading the kernel against the
metatheory* rather than by testing, and it sat behind an admission gate that was
otherwise passing. §2.5 draws the posture lesson.

### 2.5 How these bugs are actually found — and what test posture catches them

Read across §2.3 and §2.4, the mechanisms that have *historically* found kernel
soundness bugs are a short and unflattering list:

1. **Attempting verification.** Lean4Lean found a real bug — the 20-bit
   `looseBVarRange` overflow — "entirely theoretically," before any proof was
   finished. Trying to prove the kernel correct localizes the lie.
2. **Independent re-implementation.** Lean4Lean, nanoda, trepplein, `coqchk`.
   Writing a second checker surfaces where the reference disagrees with its own
   paper.
3. **Adversarial paradox construction by experts.** Hurkens/Girard encodings,
   Coquand–Abel. People deliberately trying to derive `False`.
4. **Reading the code against the metatheory** — how axeyum's own §2.4 bug was
   found.

**Example-based testing appears nowhere on that list.** Every bug in §2.3 lived
at a *feature seam*, not inside a feature: template polymorphism × universe
constraints; primitive projections × the guard condition; module subtyping ×
primitives; impredicativity × proof irrelevance × subsingleton elimination.
Nobody finds these by testing one feature at a time, and latency is measured in
*years* even in the most-scrutinised kernel in the field.

Posture this repo can actually adopt, in value order:

- **A `derives_false` corpus where every entry asserts *rejection*.** Hurkens,
  Girard, the §2.4 `Prop` large-elimination exploit (already in place), negative-
  occurrence inductives, universe-constraint escapes. Cheap, and the highest value
  per hour available at this altitude.
- **CLAUDE.md's degenerate-argument rule, lifted to kernel altitude:** *every
  kernel restriction gets a fuzz generator that deliberately violates it.* A
  positivity checker with no fuzz emitting negative occurrences is not tested. The
  `a946f925` lesson — the fuzz "passed" only because it structurally could not
  emit `(div x 0)` — is precisely how a positivity hole would hide.
- **Fuzz the seams, not the features.** Generate *combinations*: impredicative
  `Prop` × proof irrelevance × eliminator; universe metavariable × `max`/`imax` ×
  cumulativity; nested inductive × primitive projection.
- **A slow reference checker as a differential control.** Our Z3-oracle and
  DRAT-recheck idiom at kernel altitude. Lean's bugs came from kernel
  *optimizations*; a deliberately naive, obviously-correct checker is the control
  that catches those. Caveat from §2.3: Coq's module-strengthening bug lived in
  **both** the kernel and `coqchk` — diversity only helps if the implementations
  are genuinely independent, which argues for borrowing someone else's checker
  over writing a second one ourselves.

---

## 3. LCF discipline vs. proof-term (de Bruijn) designs

### 3.1 The two architectures

**LCF (Milner, 1972 → HOL Light, Isabelle, HOL4).** Define an abstract data type
`thm`. The *only* way to construct a `thm` is via a small set of constructor
functions implementing the inference rules. The module system enforces this.
Milner's insight, per
[Paulson, "The de Bruijn criterion vs the LCF architecture"](https://lawrencecpaulson.github.io/2022/01/05/LCF.html):
**"remember the results of proofs, namely theorems"** and discard the steps.
Soundness is a *type-abstraction* argument, not a checking argument.

**de Bruijn (Automath → Coq/Rocq, Lean, Agda).** Build the proof object in full.
Check it afterwards with an independent program. Soundness is a *re-checking*
argument.

### 3.2 The honest tradeoff

Paulson's argument, which deserves to be taken seriously rather than dismissed:

- The de Bruijn criterion was memory-constrained in 1972 and **still is**:
  "modern machines are vastly larger, but proofs have expanded proportionally."
  He'd rather run six proof engines on 32GB than store proof objects.
- **"De Bruijn advocates claim moral superiority about proof storage, yet Coq
  users employ numerous tricks to minimize the memory burden anyway"** —
  `vm_compute`, `native_compute`, opacity, `Qed`-time discarding. The proof-term
  purity is partly notional in practice.
- Both camps ignore what Paulson thinks matters more: **legible formalization**
  (Isar). A human-readable proof lets a mathematician check the *statement and
  the definitions* — the thing no kernel can check. "We want both."

Points in favour of de Bruijn that Paulson understates:

- **Kernel diversity is only possible with proof objects.** You cannot write an
  independent checker for an LCF system's *results*; you can only re-run it. The
  existence of nanoda/trepplein/Lean4Lean/lean4checker is a direct dividend
  (§2.2). Metamath's dozens of verifiers likewise.
- **Proof objects cross system boundaries** (Dedukti; HOL Light → Isabelle
  import).
- **Certificates decouple search from trust**, which is the entire premise of
  modern SMT/SAT (DRAT/LRAT) — and of axeyum.

Points in favour of LCF that de Bruijn advocates understate:

- **LCF costs almost nothing to implement.** HOL Light's kernel is a few hundred
  lines. Axeyum's CIC kernel is 15,516.
- **No proof-term blowup.** `simp` calls that produce megabyte proof terms in Lean
  produce a `thm` in Isabelle.
- **Sledgehammer proves LCF scales socially**: Isabelle's flagship automation
  calls untrusted external ATPs (E, Vampire, Z3, CVC5), then **reconstructs** the
  proof through the trusted kernel via `metis`/`smt`. That is *certificate-first
  culture inside an LCF system* — the proof object is transient, only the `thm`
  survives.

### 3.3 Which suits Rust + a certificate-first culture?

The relevant observation is that **axeyum has already picked, and picked
de Bruijn, twice**:

1. Its stated identity is "untrusted fast search, trusted small checking."
2. Its existing evidence formats (DRAT via `check_drat`, model replay against the
   original term) are *certificates checked by an independent program* — the
   de Bruijn criterion applied to SAT.
3. It built a CIC proof-term kernel, not a `thm` ADT.

Rust specifically favours de Bruijn:

- **Rust's module system can enforce an LCF `thm` ADT** (private constructor,
  public smart constructors) — so LCF is *available*, and unlike OCaml, Rust gives
  you this with no `Obj.magic` escape hatch. This is a real, underrated point:
  a Rust LCF kernel is *more* airtight than HOL Light's.
- But Rust's story is `#![forbid(unsafe_code)]` + serializable data + independent
  re-checking, which is exactly proof objects. And `unsafe_code` is already denied
  workspace-wide.
- Rust's weakness for de Bruijn is **allocation/GC pressure on proof terms** —
  the very thing Paulson complains about. Axeyum already answers this with arena +
  structural interning in `axeyum-ir`/`axeyum-aig`; the same technique applies.

**The synthesis worth pursuing** is neither pure: **an LCF-disciplined API over a
de Bruijn kernel.** Concretely — expose a `Theorem` type whose only constructors
are kernel-checked admissions, *and* retain the `Expr` proof term for export.
This gives (a) the tactic-layer ergonomics and typed safety of LCF, (b)
independent re-checkability, (c) an export format for third-party checkers.
Isabelle does exactly this with optional proof terms; it is a proven point in the
design space, not a compromise.

The deeper strategic point: **for axeyum's actual near-term workloads
(QF_BV/SAT), the proof term is the wrong granularity anyway.** `bv_decide`'s
memory exhaustion problem (§1.5) says so. The right shape is Isabelle's: *the
external solver's certificate (LRAT/DRAT) is the proof, checked by a small
verified checker; the kernel-level artifact is just the `thm` that results.*
Axeyum should not try to reify a million LRAT steps as CIC applications.

---

## 4. The other systems, briefly

**Rocq (Coq).**
- *Ltac1*: untyped, dynamically-scoped tactic language. Universally agreed to be
  a design mistake that could not be removed — the canonical warning about
  shipping a tactic DSL before designing it.
- *Ltac2*: typed, ML-like, with an explicit FFI to OCaml. The do-over.
- *SSReflect*: a *discipline* plus a tactic language (`rewrite`, `case`, `elim`,
  `//`, `=>` intro patterns) built for small-scale reflection — proofs where
  computation replaces deduction. Underwrote the 4-colour and Feit–Thompson
  theorems. Later ported to Lean as a library
  ([arXiv:2403.12733](https://arxiv.org/pdf/2403.12733)).
- *`native_compute`/`vm_compute`*: the Poincaré principle taken to compilation.
  **And the source of the `True`≡`False` bug in §2.3.**
- *`coqchk`*: the independent re-checker. Note from §2.3 that some bugs existed
  in *both* the kernel and the checker (module strengthening) — **kernel
  diversity only helps if the implementations are genuinely independent.**
- *Coq Coq Correct!* verified typechecking + erasure for Coq in Coq
  ([POPL20](https://sozeau.gitlabpages.inria.fr/www/research/publications/Coq_Coq_Correct-POPL20.pdf)).

**Isabelle.**
- LCF `thm` kernel, Pure meta-logic, object logics (HOL, ZF) on top.
- *Isar*: structured, declarative, human-legible proof language. Paulson's "third
  dimension". The strongest counter-argument to tactic-script brittleness.
- *Sledgehammer*: fires the goal at E/Vampire/Z3/CVC5/SPASS in parallel, takes the
  ATP's unsat core, and **reconstructs** a kernel-checked proof (`metis`, `smt`,
  or a one-liner `by auto` suggestion). This is the highest-leverage automation
  UX in the field, and it is architecturally *identical* to what axeyum should
  build: untrusted search, trusted reconstruction. Note that it is *not*
  proof-term import — it is re-proving with hints.
- *Nitpick/Quickcheck*: counterexample finders. Ships `sat` evidence, not just
  `unsat`. Axeyum's model-replay discipline is the same instinct.

**HOL Light.** The minimal LCF kernel (~few hundred lines OCaml, simple type
theory + 3 axioms). Proves the value of a tiny TCB: Flyspeck (Kepler conjecture)
rests on it. Its automation is thin by comparison — the price of minimalism.

**ACL2.** First-order, quantifier-free, untyped Lisp. No proof objects; the
prover *is* the TCB (huge, ~10⁵ lines). Waterfall architecture + heavy
rewriting + induction heuristics. Industrially successful (AMD, Centaur, Intel
FP hardware) *precisely because* it drops the de Bruijn criterion and buys
automation with the savings. **The most honest data point against certificate
purity.**

**Metamath.** Maximal de Bruijn. `set.mm` has >40k theorems from ZFC. Verifiers
in dozens of languages, each a few hundred lines. Zero automation. Demonstrates
that checkability and usability are genuinely in tension.

**Mizar.** Declarative, human-readable, soft-typed; the MML is the oldest large
library. Its influence is Isar's ancestry. Monolithic non-diverse checker.

---

## 5. What is genuinely hard

Ordered by how much of the person-years they eat, from the literature and the
practitioner record:

1. **Unification, especially higher-order.** Pattern (Miller) fragment is
   decidable and unique; everything else is heuristics + postponement. Every ITP
   has a bespoke, undocumented, performance-critical unifier that nobody fully
   understands. This is the #1 source of user-visible mystery.
2. **Definitional equality performance.** `isDefEq` is called constantly. It
   needs WHNF caching, lazy delta, transparency settings (`reducible`/`instances`/
   `default`/`all`), and unfolding heuristics. Get it wrong and everything is slow;
   get it *too* clever and you get a soundness bug. And it does not terminate
   (§2.3) — you need fuel.
3. **Universe inference.** Recurring #1 soundness category (§2.3). Cumulativity,
   universe polymorphism, algebraic levels (`max`/`imax`/`succ`), level
   constraint solving, `Prop` impredicativity. `imax` is where `Prop` sneaks in
   and where the subsingleton problem lives (§2.4).
4. **Typeclass resolution.** Exponential search, diamond problems, defeq checks
   inside instance search, `outParam`. Mathlib's algebraic hierarchy is
   simultaneously its greatest asset and its worst compile-time cost.
5. **Proof-term size.** Real. `simp` and `decide` produce enormous terms;
   `bv_decide` would exhaust memory without reflection. Drives every Poincaré
   concession, which drives the soundness bugs. **The dominant force in the
   design.**
6. **Error messages.** Elaboration is a constraint solver; when it fails, the
   failure is a residual constraint, not a source location. "Failed to synthesize
   instance" and metavariable-laden type mismatches are the field's chronic UX
   wound. There is no known good answer.
7. **Library refactoring at scale.** See §6 — this dwarfs everything once you have
   a library.
8. **Proof brittleness.** Tactic scripts break on unrelated library changes
   (`simp` set grows → a `simp only` closes a goal differently → downstream
   `exact?` output no longer applies). Isar/declarative style and SSReflect
   discipline are the two known mitigations; neither is free.

---

## 6. Sizing: what a usable prover actually costs

Numbers, each with its date attached (they move):

| Thing | Size | Source |
|---|---|---|
| Lean 4 kernel | ~5–6k LoC C++ (+~700 for inductive families) | [Grokipedia](https://grokipedia.com/page/Lean_(proof_assistant)), [system description](https://lean-lang.org/papers/system.pdf) |
| axeyum-lean-kernel (today) | **15,516 LoC Rust** | measured in-tree, 2026-07-15 |
| Lean4Lean (verified kernel in Lean) | 20–50% slower than C++ kernel; checks all Mathlib | [arXiv:2403.14064](https://arxiv.org/html/2403.14064v3) |
| **Mathlib** | **~2.1M LoC, ~8,000 files** (late 2025) | [Mathlib statistics](https://leanprover-community.github.io/mathlib_stats.html) |
| Mathlib declarations | **274,045 theorems + 130,791 definitions** (2026) | [Mathlib statistics](https://leanprover-community.github.io/mathlib_stats.html) |
| Mathlib contributors | **772** | [Mathlib statistics](https://leanprover-community.github.io/mathlib_stats.html) |
| Mathlib throughput | >1,100 PRs merged in Aug 2025 (record month) | [Growing Mathlib, arXiv:2508.21593](https://arxiv.org/html/2508.21593v1) |
| HOL Light kernel | few hundred lines OCaml | — |
| Automath checker (de Bruijn, 1970s) | ~200 lines | [PLS Lab](https://www.pls-lab.org/en/de_Bruijn_criterion) |

**Timelines — the sobering part:**

- **Coq**: 1984 → present. **~40 years**, INRIA-funded, dozens of PhDs. Still
  shipping kernel soundness fixes in V9.0.0 (§2.3).
- **Isabelle**: 1986 → present. **~40 years**, Cambridge + TUM. From LCF to
  Isabelle/HOL is itself a ~35-year story
  ([arXiv:1907.02836](https://arxiv.org/pdf/1907.02836)).
- **Lean**: 2013 (Lean 1) → Lean 4 (2021) → today. **~13 years to reach an
  ecosystem**, with de Moura full-time, Microsoft Research then AWS then the
  **Lean FRO** (a funded nonprofit with a full-time engineering staff). Lean 4
  was an "almost ground-up rewrite" — *they threw away Lean 3 entirely.*
- **The Lean 3 → Lean 4 Mathlib port** (`mathport`/`mathlib4`): ~2 years of
  substantial community effort to move ~1M lines, with semi-automated
  translation. A cautionary tale about library lock-in.
- **Mathlib's maintenance** ([Growing Mathlib, CICM 2025](https://arxiv.org/html/2508.21593v1))
  is a *whole discipline*: a deprecation system for breaking changes, linters for
  code-quality enforcement, conscious library re-design to control compilation
  times, technical-debt tracking, and custom review/triage tooling. **The library
  is not the easy part after the prover; it is the larger project.**

**Honest estimate.** A *kernel* is 1–3 person-years (axeyum has largely done it).
A *usable prover* — elaborator, unifier, typeclasses, tactic framework, decent
errors — is where Lean spent roughly **20–50 person-years** before Mathlib was
viable. A *library worth using* is **hundreds of person-years** and is
open-ended. Mathlib's 772 contributors are not a bonus; they are the mechanism.

The Lean FRO's existence is the tell: **de Moura concluded that a usable prover
needs a permanently funded full-time engineering organization**, not a research
group and not volunteers.

---

## What this implies for axeyum

Design-space choices **open to us** — not a gap list. We are not behind; we are
unusually positioned, because we arrive with a kernel, a certificate culture, and
no library obligations. The systems in §6 are not ahead of us on a shared track;
they are at different points in a space, having paid different prices.

**1. The three architectures are not exclusive, and the combination is ours to
take.** De Bruijn kernel (built) + a sealed Rust `Theorem` newtype (§3.3 —
LCF's cheap win, near-zero cost, and `#![deny(unsafe_code)]` makes our seal
*stronger* than OCaml's) + certificate-emitting procedures as the primary tactic
idiom (§0.3 — our existing culture). No prover has assembled all three, and the
reason looks like historical accident rather than principle. Isabelle's
LCF-ADT-plus-optional-proof-terms is the existence proof that two of the three
compose.

**2. Certificate-first (§0.3) is the genuinely differentiated bet.** We already
ship DRAT + `check_drat` + replay-checked models. "Tactics emit checkable
evidence rather than terms" is not exotic *here*; it is the SMT stack's existing
idiom lifted an altitude, and it is the natural interface for agent drivers — an
agent proposes a certificate, a checker accepts or rejects, and no agent needs a
privileged constructor. The open questions deserve ADRs before commitment:
(a) **one** certificate substrate (λΠ-modulo? our own?) or N per-class formats;
(b) what certificate→term reconstruction costs, given reconstruction is the known
SMT-to-ITP bottleneck; (c) do agents emit certificates directly, or terms from
which we derive certificates?

**3. Elaboration is a dial, not a switch — decide *who writes terms* before
turning it.** The evidence (§1.3.1) says the surface-syntax half (notation,
macros, coercions, overloading) is the large, accident-laden,
error-message-poisoning half, and Metamath/Dedukti prove a system can deliver
real mathematics with *none* of it. The unification-and-implicits half is harder
to skip, because goal-directed search needs it. Provisional read: **skip the
surface half, keep a minimal unifier**, and accept the consequence honestly —
humans will not author here, so our lemma stock must come from import or
generation. That is a strategic commitment deserving an ADR, not a default. A
corollary that costs nothing if decided now and a lot if decided late: **the
error contract must be machine-parseable**, because our consumers are agents.

**4. Metavariables are unavoidable; *dependent* metavariables are a choice.**
(§1.4.1) Pattern unification + non-dependent goals is a dramatically smaller
engine than `MetaM`. Start in the small fragment, widen on evidence and an ADR —
the same discipline as ADR-0014 and ADR-0025.

**5. Our kernel bug (§2.4) is evidence our instincts are right — now make it
infrastructure.** The historical record (§2.5) says these bugs are found by
attempted verification, independent re-implementation, adversarial paradox
construction, and reading code against the metatheory — *not* by example tests,
and latency is measured in years. Concretely available now: a **`derives_false`
corpus** asserting *rejection* (Hurkens, Girard, our exploit, negative-occurrence
inductives, universe escapes); **CLAUDE.md's degenerate-argument rule lifted to
the kernel** — every restriction gets a generator that deliberately violates it;
**seam fuzzing** over feature *combinations*, since every historical bug lived at
an interaction; and **a slow reference checker as differential control**.

**6. Watch kernel LoC as a liability.** 15.5k Rust vs. Lean's ~6k C++. Every
deferred feature (nested inductives, mutual inductives, reflexive constructors,
indexed recursion) will *add* trusted lines. Budget for this and resist
accelerations: §2.3 shows that **every Poincaré-principle optimization — bignum
`Nat`, primitive arrays, VM compute, native compute — has been a soundness-bug
site in Coq or Lean.** If axeyum adds a fast-path `Nat`, it needs its own
soundness-negative suite.

**7. Rust-specific hazards from the record.** Lean's kernel bug was a **20-bit
cached de Bruijn field that overflowed and defaulted to 0** because `panic!`
continued execution. Audit every `Expr` metadata cache in
`axeyum-lean-kernel/src/expr.rs` for saturating/wrapping arithmetic and
default-on-error. In Rust, prefer `checked_*` + hard abort over saturate — a
too-large value is conservative; 0 is catastrophic. Also: defeq **does not
terminate** (Coquand–Abel), so a fuel/depth parameter is mandatory, not optional;
Lean4Lean's 1000 sufficed for all of Mathlib.

**8. `bv_decide` is the map — and axeyum can beat it on trust.** Lean's
bit-blast→SAT→LRAT→checker pipeline is architecturally identical to
`axeyum-bv`→`axeyum-cnf`→`check_drat`, but Lean's checker runs by reflection via
`ofReduceBool`, dragging the **entire Lean compiler into the TCB**. Axeyum's
native Rust DRAT checker has no such dependency. **This is a genuine competitive
advantage and should be stated as such**: axeyum's BV automation can carry a
strictly smaller TCB than Lean's. Do *not* give it away by reifying LRAT steps as
CIC proof terms — that is the path that exhausted Lean's memory and forced the
reflection compromise.

**9. Adopt the Isabelle/Sledgehammer shape, not the Coq shape.** The lesson from
§4 is that the winning integration of a fast untrusted solver with a trusted
kernel is *not* proof-term import. It is: solver finds it → certificate is
checked by a small independent checker → the kernel-level artifact is a `Theorem`.
Axeyum already has the solver and the checker. The missing piece is the
`Theorem`-producing bridge, and it is much smaller than a proof-term translation.

**10. LCF-disciplined API over a de Bruijn kernel.** Rust's privacy rules enforce
an abstract `Theorem` type *better than OCaml does* (no `Obj.magic`), and
`unsafe_code` is already denied workspace-wide. Take the LCF ergonomics *and*
keep the `Expr` proof term for export and third-party re-checking. Isabelle's
optional proof terms prove this is a real point in the design space. Concretely,
this argues for a `axeyum-lean-thm`-style boundary crate whose only constructors
route through the kernel's admission gate — and per ADR-0001, only once a
consumer proves the boundary.

**11. Build the export format early; kernel diversity is the payoff.** The reason
independent Lean checkers exist is a stable export format. Axeyum's kernel should
emit one (Lean's `.olean`-adjacent export text format is the obvious target —
it would let `lean4checker`/`nanoda`/Lean4Lean re-check axeyum's output, which is
*free, genuinely independent* validation of the highest-risk component). Caveat
from §2.3: Coq's module-strengthening bug lived in **both** the kernel and
`coqchk` — diversity only helps if implementations are truly independent, which
argues *for* borrowing someone else's checker rather than writing a second one.

**12. Be realistic about scope, and pick the narrow win.** Coq and Isabelle are
~40-year projects; Lean took ~13 years and now needs a funded FRO; Mathlib is
2.1M lines and 772 contributors. Axeyum will not have a Mathlib. **That is fine
and it should be the strategy**: axeyum's north star is *reasoning with
checkable evidence*, not a mathematics library. The kernel's job is to be the
trusted checking substrate for solver-produced evidence — a `Theorem` that says
"this QF_BV formula is unsat, and here is a certificate a 200-line program can
verify." That is a **narrow, achievable, defensible** target that plays to the
existing stack, and it is the one place where a Rust CIC kernel plus a fast SAT
core is a *better* combination than anything Lean or Isabelle currently ships.
Note the convergence: Lean is growing an SMT solver (`grind`) inside its tactic
layer while axeyum is growing a kernel under its SMT solver. Axeyum has
`axeyum-egraph` in tree already. The meeting point is real — but the elaborator,
unifier, and typeclass layers (§5, items 1–4, ~20–50 person-years) are the part
axeyum should be most reluctant to build, and should build *last*, if ever.

---

## Sources

- [Lean4Lean: Verifying a Typechecker for Lean, in Lean (Carneiro), arXiv:2403.14064](https://arxiv.org/html/2403.14064v3)
- [Type Checking in Lean 4 — Trust](https://ammkrn.github.io/type_checking_in_lean4/trust/trust.html)
- [Lean Language Reference — Inductive Types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)
- [Metaprogramming in Lean 4 — MetaM](https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html) and [Tactics](https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html)
- [leansat / bv_decide README](https://github.com/leanprover/leansat/blob/main/README.md), [Lean.Elab.Tactic.BVDecide](https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/BVDecide.html)
- [LRAT-Catcher: Importing SAT Solver Certificates into Lean 4 by Reflection, arXiv:2607.00815](https://arxiv.org/pdf/2607.00815)
- [PBLean: Pseudo-Boolean Proof Certificates for Lean 4, arXiv:2602.08692](https://arxiv.org/html/2602.08692v1)
- [Rocq/Coq `dev/doc/critical-bugs.md`](https://github.com/rocq-prover/rocq/blob/master/dev/doc/critical-bugs.md)
- [Coq Coq Correct! (POPL 2020)](https://sozeau.gitlabpages.inria.fr/www/research/publications/Coq_Coq_Correct-POPL20.pdf)
- [Paulson, "The de Bruijn criterion vs the LCF architecture"](https://lawrencecpaulson.github.io/2022/01/05/LCF.html)
- [Geuvers, "Proof Assistants: history, ideas and future"](https://www.cs.ru.nl/~herman/PUBS/proofassistants.pdf)
- [Barendregt & Geuvers, "Proof-Assistants Using Dependent Type Systems"](https://www.infomath-bib.de/tmp/data/Proof-assistants-using-dependent-type-systems.pdf)
- [PLS Lab: de Bruijn criterion](https://www.pls-lab.org/en/de_Bruijn_criterion)
- [Wiedijk, The Seventeen Provers of the World](https://www.cs.ru.nl/~freek/comparison/comparison.pdf)
- [Paulson, "From LCF to Isabelle/HOL", arXiv:1907.02836](https://arxiv.org/pdf/1907.02836)
- [Growing Mathlib: maintenance of a large scale mathematical library, arXiv:2508.21593](https://arxiv.org/html/2508.21593v1)
- [Mathlib statistics](https://leanprover-community.github.io/mathlib_stats.html)
- [lean4 issue #7637: type theory edge case: projections and sort polymorphism](https://github.com/leanprover/lean4/issues/7637)
- [Zulip: soundness bug: native_decide leakage](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/soundness.20bug.3A.20native_decide.20leakage.html)
- [lean4lean repository](https://github.com/digama0/lean4lean)
- [Small Scale Reflection for the Working Lean User, arXiv:2403.12733](https://arxiv.org/pdf/2403.12733)

---

## Addendum — kernel soundness, measured (2026-07-15, late)

Numbers marked **[measured]** were counted from source clones on 2026-07-15, not
taken from secondary claims. Several widely-repeated figures turned out stale.

### The one clean empirical win for kernel diversity

> **`lean4checker` rejected Carneiro's `native_decide` proof of `False` that
> Lean's own kernel accepted** — because it does not implement `reduceBool`.

That is the entire empirical case for independent checkers, and it is **one data
point**. It is also worth more than the abstract argument, and it is the best
justification for `axeyum-lean-kernel`'s existence that this track has found.

The exploit ([Zulip, Carneiro 2023-10-10](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/soundness.20bug.3A.20native_decide.20leakage.html))
proved `False` with **no axiom dependency showing**, probabilistically (~1/4),
because `reduceBool` executed compiled code twice with different results. Fixed by
[lean4#2654](https://github.com/leanprover/lean4/pull/2654), introducing
`trustCompiler` so `#print axioms` sees it.

### Genuine independence is rarer than assumed — three corrections

- **`coqchk` is NOT an independent checker.** Its `checker/dune` **links
  `rocq-runtime.kernel`** — the same 43,709-line kernel, same conversion machine.
  It is ~3,931 lines of *additional* logic layered on the shared kernel. **A kernel
  conversion bug is not caught by coqchk by construction.** Coq ships *no*
  independent kernel implementation.
- **`lean4lean` is explicitly not independent.** Its own README: "It is derived
  directly from the C++ kernel implementation, and as such **likely shares some
  implementation bugs with it (it's not really an independent implementation)**."
  Its value is *metatheory* and bug-discovery — it found
  [lean4#10475](https://github.com/leanprover/lean4/issues/10475) — not diversity.
- **`nanoda_lib` is Lean 4 and current** (last commit 2026-06-02, **9,203 lines**
  [measured]), not a Lean-3-era artifact.

**So a genuinely independent, from-scratch kernel is rare.** Ours (~15.5k lines)
is one — which is a stronger claim than anything in the thesis's differentiator
list, and it was sitting there unstated.

### TCB sizes [measured]

| System | Component | Lines |
|---|---|---:|
| HOL Light | `fusion.ml` (whole kernel) | **548 non-blank** (676 total) |
| Lean 4 | `src/kernel/` (C++, 37 files) | **7,888** |
| Coq/Rocq | `kernel/` | **43,709** |
| nanoda_lib | Rust | **9,203** |
| **axeyum-lean-kernel** | Rust | **~15,500** |
| mmverify.py | Python | **708** (653 non-blank) |

**Stale figures to stop repeating:** HOL Light's "~400 lines" (Wiedijk's, now
**548**); mmverify.py's "350 lines" (a 2002 number, now **708**).

HOL Light's real virtue is not LoC but surface: **exactly 10 primitive inference
rules** [measured].

### The finding that explains our P0

> **"Small trusted kernels get verified; the bugs live in the parts that aren't
> small."**

Coq's [`dev/doc/critical-bugs.md`](https://github.com/rocq-prover/rocq/blob/master/dev/doc/critical-bugs.md)
documents **78 critical bugs** [measured], **5 still unfixed**:

| Area | Bugs |
|---|---:|
| Conversion machines | 20 |
| **Typing constructions (incl. guard checker)** | **15** |
| Universes | 13 |
| Module system | 10 |
| Axiom conflicts in library | 7 |

*Coq Coq Correct!* ([DOI](https://doi.org/10.1145/3371076)), verbatim: "**on
average, one critical bug has been found every year in Coq.**"

**And the coverage is anti-correlated with the risk.** MetaCoq verifies PCUIC
"**without the module system, template polymorphism and η-conversion**" — i.e. it
excludes precisely the areas responsible for **23 of the 78**. The guard checker —
verified by nobody, 15 entries — produced a relative inconsistency that survived
from **V6.1 (1997) to 9.0.1 (2025)**, ~28 years
([#21053](https://github.com/rocq-prover/rocq/issues/21053)), and still has an
**open** issue ([#22024](https://github.com/rocq-prover/rocq/issues/22024), 2026).

**Read this against our own incident.** Our P0 lived in `inductive.rs` — at 1,081
lines, the largest trusted blob in the kernel, and the one P3.6's own task table
calls "the biggest trusted blob." The pattern is not ours; it is the field's.

### Lean's `native_decide` hole is being closed — a differentiator evaporating

`trustCompiler`, `reduceBool`, `ofReduceBool`, `ofReduceNat` now all carry
[measured]:

```
@[deprecated "in-kernel native reduction is deprecated; assert native evaluations
with axioms instead" (since := "2026-02-01")]
```

Per [Lean 4.29.0](https://lean-lang.org/doc/reference/latest/releases/v4.29.0/)
(2026-03-27), native computation (`native_decide`, **`bv_decide`**) is now **one
axiom per computation** asserting the specific equality obtained.

**Note 03 cites `bv_decide`'s `ofReduceBool` trust cost as an opening for us.
That opening is closing.** Do not build a plan on it.

Lean's remaining kernel trust surface [measured, `ee0963c`]: **14
kernel-accelerated `Nat` operations** computing on GMP (`type_checker.cpp:611-637`)
— each trusted C++ that must agree with the Lean-level definition; definitional
proof irrelevance (`:838-845`); function **and structural** eta; quotients as
primitives (`quot.cpp`, 117 lines, 4 constants); three axioms — `propext`,
`Quot.sound`, `Classical.choice`.

### Lean's kernel is sound only relative to a **trusted prelude** — and so is ours

`lean4lean/divergences.md` is unusually candid, and the parallel to our situation
is exact:

> "`checkPrimitiveDef`, `checkPrimitiveInductive`: **Lean does not check that
> primitives are declared with the correct types and definitional behavior**,
> except in the case of `Eq`… **This is required for soundness**, but Lean is able
> to get away with it because **Lean ships its prelude and using an alternative
> prelude is not supported**."
>
> "literal case: The original code was **not checking that the literal type
> actually exists**. Again, this is okay **provided that the prelude is trusted**."

**That assumption is invisible in the LoC count.** Lean's kernel is 7,888 lines
*plus a prelude nobody checks*. Ours is ~15,500 lines *plus 64 axioms nobody has
proved* (T6.0.6). Same shape, and ours is worse: Lean's prelude is at least
*definitional*, while our arithmetic carrier is an opaque `Declaration::Axiom`.

So when we state a TCB, "the kernel" is not the boundary — **the kernel plus its
prelude** is. Any comparison of kernel sizes that omits the prelude flatters
everyone, us included.

### Pollack-consistency — a class we have not considered

Wiedijk, [*Pollack-inconsistency*](https://www.cs.ru.nl/~freek/pubs/rap.pdf)
(ENTCS 285, 2012). The point is that **the de Bruijn criterion is necessary but
not sufficient**:

> "it also should not be possible to think that a theorem that actually is false
> has been proved... **not only the proof checking kernel has to be taken into
> account when considering the reliability of a system, but also the interface
> code.**"

| System | Verdict |
|---|---|
| HOL Light | **strongly Pollack-inconsistent**, weakly super-inconsistent |
| Isabelle | **strongly Pollack-inconsistent** — `notation True ("False")` then `lemma False` *prints as proved* |
| Coq | weakly Pollack-super-inconsistent (coercions: `Check 1` prints `0`) |
| **Metamath** | ✅ **Pollack-consistent** — parsing/printing are the identity |

**This bears directly on `lean_pp.rs`** (1,598 lines): it prints terms for a human
or for real Lean to re-check. If `parse(print(t)) ≠ t`, the cross-check validates
something other than what we proved. Wiedijk's fix is cheap — print, re-parse,
compare, fall back to a failsafe printer on mismatch — and **nobody has checked
whether our printer is well-behaved**. A candidate task for P6.0.

His community diagnosis is worth keeping: "*If no problem is felt, then in some
sense there is no problem.*" That is exactly the attitude that let our P0 sit.

### The de Bruijn criterion, canonically

Barendregt & Geuvers, *Handbook of Automated Reasoning* (2001), p. 1151:

> "**A proof assistant satisfies the de Bruijn criterion if it generates
> 'proof-objects' (of some form) that can be checked by an 'easy' algorithm.**"

And the tension we should name rather than paper over — the **Poincaré principle**
(computations need no proof) *trades against* it:

> "**This puts somewhat of a strain on the de Bruijn criterion** requiring that the
> verifying program be simple." … "If the Poincaré principle is adopted for
> βδι-conversion, the verifying program is more complex than the one for just
> βδ-conversion."

Every kernel accelerator — Lean's 14 GMP `Nat` ops, our `Lit` reduction plans —
buys speed by spending de Bruijn simplicity. That is the axis T6.0.4 and T6.0.7
are trading on, and it should be stated as a trade.

**And the bill is measured.** The largest single category of Coq's 78 critical
bugs is **conversion machines: 20 of 78** — the VM, the native compiler, the lazy
machine. That is the Poincaré principle's cost, empirically, exactly where
Barendregt & Geuvers predicted it in 2001. Lean's own docs on `native_decide`:
"**the Lean compiler and interpreter become part of your trusted code base. This
is extra 30k lines of code.**" And the field is self-correcting — Lean deprecated
in-kernel native reduction on **2026-02-01** in favour of per-computation axioms,
a move *back toward* de Bruijn.

**This is strong empirical support for a split axeyum already made.** The
DRAT/`check_drat` architecture — compute fast in untrusted code, emit an artifact,
check it with a small independent checker — is precisely the alternative to
putting the accelerator *inside* the kernel. Every shortcut inside the checker is
a shortcut no evidence artifact covers, and 20/78 is what that costs at scale.

**The direct consequence for T6.0.4 (`Lit` typing + bignum):** we are about to add
literal arithmetic to a trusted kernel. That is the same bargain Coq lost 20 times.
Either the literal ops must be *checked* rather than trusted, or the trade must be
made deliberately and written down — not inherited because Lean did it.

### Coverage boundary of this addendum — stated, per our own rule

*Verification Theatre*'s finding is that the undocumented **boundary** is what
bites, not bad work. So: what this addendum did **not** research, and must not be
read as covering.

| Area | Status |
|---|---|
| **Isabelle** | **Not covered.** Kunčar & Popescu's overloading inconsistency, Isabelle's TCB size, and Isabelle kernel bugs are all unresearched. Isabelle has no public equivalent of Coq's `critical-bugs.md` — itself a citable asymmetry. |
| **Metamath Zero** (Carneiro) | **Not covered.** A real omission: it is the central artifact for minimal-TCB arguments, and we are making a minimal-TCB argument. |
| Metamath quantitative claims | The "5 verifiers" rule, Metamath 100 count, set.mm size — **search-derived only**, unconfirmed against `us.metamath.org`. Only `mmverify.py`'s 708 lines is measured. |
| Dedukti / Logipedia | **Search-only.** No kernel LoC, no coverage percentages, no liveness check. |
| HOL Light bugs | Arthan's RJ2 is sourced. A "2006 `new_specification` bug" and a "`SUBST` bug" were looked for and **not substantiated** — probably misattributed. Candle not covered. |
| Girard 1972 / Coquand 1986 | Cited from secondary sources; primary documents **not verified**. |
| Lean bug coverage | **Illustrative, not a systematic label sweep.** |

Two premises that were checked and found **false** — recorded so nobody re-derives
them:

- **Coq #7825 is not a kernel/soundness bug.** It is a tactics/unification PR
  (verified via the GitHub API). Use #20413 / #21053 / #22024 as the modern
  guard-condition exemplars instead.
- **`nanoda_lib` is a current Lean 4 checker** (last commit 2026-06-02), not a
  Lean-3-era artifact. That matters: it is one of the very few *genuinely*
  independent implementations, and our kernel is ported from it.
