# The Anatomy of an ITP Above Its Kernel

Research note. Status: survey + orientation for the axeyum prover track.
Date: 2026-07-15.

Context: axeyum has `crates/axeyum-lean-kernel` (~15.5k LoC Rust: CIC, universes,
dependent Pi, inductives + recursors, WHNF, defeq, trusted admission gate) and
**nothing above it**. This note maps what "above it" actually contains, what it
costs, and what the load-bearing engineering decisions are.

**The single most urgent finding is in §2.4 — the in-tree kernel appears to have
the Prop large-elimination unsoundness *right now*. Read that section first.**

---

## 1. Lean 4: what is in the kernel, what is outside

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

### 2.4 ⚠ The Prop large-elimination hole — axeyum appears to have it

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

**The finding.** In `crates/axeyum-lean-kernel/src/inductive.rs`, the module
docs state, at line 37, that among the deferred items are
"the `Prop`-subsingleton large-elimination subtleties", and then:

> `//! The motive is always allowed to eliminate into an arbitrary `Sort v` here.`

Meanwhile `crates/axeyum-lean-kernel/src/tc.rs:735` implements
`proof_irrel_eq` (modelled on nanoda's `proof_irrel_eq`) and it is wired into the
defeq path at `tc.rs:916`.

**Those two facts together are the classical unsoundness.** The kernel has
(a) definitional proof irrelevance and (b) unrestricted large elimination for
`Prop`-valued inductives. The standard exploit shape:

```lean
inductive B : Prop where | t : B | f : B
-- recursor generated with motive : B → Sort v, v arbitrary
def d (b : B) : Bool := B.rec true false b
-- d B.t ≡ true, d B.f ≡ false by ι
-- but B.t ≡ B.f by proof irrelevance ⇒ true ≡ false ⇒ False
```

**This is not a hypothetical.** It is the exact bug class the user suspected, the
docs explicitly acknowledge it as unhandled, and the enabling half (proof
irrelevance) is implemented. The remaining question is only *reachability*: can a
user-facing declaration path admit a two-constructor `Prop` inductive and its
recursor? Given `check_inductive` accepts a `Sort`-tailed type and the motive is
unrestricted, it very likely can.

**Recommended action (P0, ahead of any prover-layer work):**
1. Write a **soundness-negative test** that attempts exactly the `B : Prop` /
   `Bool` extraction above and asserts the kernel **rejects** it. Per CLAUDE.md's
   hard rules, this is the "test it harder" response, not a defer.
2. Implement the two-clause syntactic criterion in recursor generation: compute
   an `elim_level` for the inductive — if the inductive's sort is `Prop` and it
   fails the criterion, the motive must be constrained to `Prop`.
3. Note the criterion needs care under **universe polymorphism** (`Sort u` that
   *might* be `Prop`) — this is exactly the recurring universe-bug category from
   §2.3, so the conservative answer (constrain unless provably not `Prop`) is the
   right one.
4. Add a fuzz seed-class generating `Prop` inductives with 0/1/2+ constructors and
   with data fields present/absent from the output type — mirroring the hard rule
   about degenerate-argument fuzz classes for partial operators.

Until then, the kernel's "trusted admission gate" is not trustworthy, and any
evidence artifact it underwrites is worth nothing. Everything else in this note
is subordinate to fixing this.

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

**1. Fix the Prop large-elimination hole before anything else (P0).**
`inductive.rs:37` grants arbitrary `Sort v` elimination to every inductive
including `Prop`-valued ones, while `tc.rs:916` implements definitional proof
irrelevance. That combination is the classical inconsistency (§2.4). Per
CLAUDE.md — "soundness is a method, not an excuse" — the response is a
soundness-negative test that *must* fail to admit `B : Prop | t | f` eliminating
to `Bool`, then the two-clause syntactic criterion in recursor generation, then a
fuzz seed-class over `Prop` inductives with 0/1/2+ constructors and data fields
in/out of the output type. **No prover-layer work should land above a kernel whose
admission gate is unsound**; the whole architecture's value is that the kernel is
the one thing you trust.

**2. Watch kernel LoC as a liability.** 15.5k Rust vs. Lean's ~6k C++. Every
deferred feature (nested inductives, mutual inductives, reflexive constructors,
indexed recursion) will *add* trusted lines. Budget for this and resist
accelerations: §2.3 shows that **every Poincaré-principle optimization — bignum
`Nat`, primitive arrays, VM compute, native compute — has been a soundness-bug
site in Coq or Lean.** If axeyum adds a fast-path `Nat`, it needs its own
soundness-negative suite.

**3. Rust-specific hazards from the record.** Lean's kernel bug was a **20-bit
cached de Bruijn field that overflowed and defaulted to 0** because `panic!`
continued execution. Audit every `Expr` metadata cache in
`axeyum-lean-kernel/src/expr.rs` for saturating/wrapping arithmetic and
default-on-error. In Rust, prefer `checked_*` + hard abort over saturate — a
too-large value is conservative; 0 is catastrophic. Also: defeq **does not
terminate** (Coquand–Abel), so a fuel/depth parameter is mandatory, not optional;
Lean4Lean's 1000 sufficed for all of Mathlib.

**4. `bv_decide` is the map — and axeyum can beat it on trust.** Lean's
bit-blast→SAT→LRAT→checker pipeline is architecturally identical to
`axeyum-bv`→`axeyum-cnf`→`check_drat`, but Lean's checker runs by reflection via
`ofReduceBool`, dragging the **entire Lean compiler into the TCB**. Axeyum's
native Rust DRAT checker has no such dependency. **This is a genuine competitive
advantage and should be stated as such**: axeyum's BV automation can carry a
strictly smaller TCB than Lean's. Do *not* give it away by reifying LRAT steps as
CIC proof terms — that is the path that exhausted Lean's memory and forced the
reflection compromise.

**5. Adopt the Isabelle/Sledgehammer shape, not the Coq shape.** The lesson from
§4 is that the winning integration of a fast untrusted solver with a trusted
kernel is *not* proof-term import. It is: solver finds it → certificate is
checked by a small independent checker → the kernel-level artifact is a `Theorem`.
Axeyum already has the solver and the checker. The missing piece is the
`Theorem`-producing bridge, and it is much smaller than a proof-term translation.

**6. LCF-disciplined API over a de Bruijn kernel.** Rust's privacy rules enforce
an abstract `Theorem` type *better than OCaml does* (no `Obj.magic`), and
`unsafe_code` is already denied workspace-wide. Take the LCF ergonomics *and*
keep the `Expr` proof term for export and third-party re-checking. Isabelle's
optional proof terms prove this is a real point in the design space. Concretely,
this argues for a `axeyum-lean-thm`-style boundary crate whose only constructors
route through the kernel's admission gate — and per ADR-0001, only once a
consumer proves the boundary.

**7. Build the export format early; kernel diversity is the payoff.** The reason
independent Lean checkers exist is a stable export format. Axeyum's kernel should
emit one (Lean's `.olean`-adjacent export text format is the obvious target —
it would let `lean4checker`/`nanoda`/Lean4Lean re-check axeyum's output, which is
*free, genuinely independent* validation of the highest-risk component). Caveat
from §2.3: Coq's module-strengthening bug lived in **both** the kernel and
`coqchk` — diversity only helps if implementations are truly independent, which
argues *for* borrowing someone else's checker rather than writing a second one.

**8. Be realistic about scope, and pick the narrow win.** Coq and Isabelle are
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
