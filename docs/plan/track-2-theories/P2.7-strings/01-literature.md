# P2.7 · 01 — Literature survey: SMT string/sequence solving

SOTA for QF_S / QF_SLIA / QF_SNIA. Citations verified across primary sources
(dblp, publisher pages, arXiv, smt-lib.org, SMT-COMP results).

## 0. The scoping fact (read first)

**Decidability of QF word equations + length constraints is OPEN** (≈ since 1968).
Proving it undecidable would yield a new route to Hilbert's 10th — it sits at a
deep Diophantine boundary. Adjacent results are outright **undecidable**. So **no
string solver is complete**; the winners are refutation-sound + solution-sound but
**deliberately incomplete and non-terminating in general**. axeyum adopts this
incompleteness honestly and returns `unknown` outside the decidable fragments.

## 1. Decidability landscape

| Claim | Citation |
|---|---|
| Word equations (with constants) **decidable** | Makanin, *Mat. Sbornik*, 1977 |
| Makanin non-elementary; recompression reproves & lowers to O(n log n) NSPACE | Jeż, *Recompression*, STACS 2013; *Word Equations in NLINSPACE*, ICALP 2017 |
| Word equations with constants **∈ PSPACE** | Plandowski, FOCS 1999 / *JACM* 51(3), 2004 |
| Exact complexity **open** (NP-hard ≤ · ≤ PSPACE; conjectured NP) | Day, Ganesh, He, Manea, Nowotka, RP 2018 |
| **Word equations + length: decidability OPEN** | Ganesh, Minnes, Solar-Lezama, Rinard, ADDCT/CADE 2013 |
| Concat + LIA-over-length + string⇄int conversion **UNDECIDABLE** | Ganesh & Berzish, CoRR abs/1605.09442, 2016 |
| transducers + word equations + length **undecidable** (even single `T(x,x)`) | Abdulla et al., *Chain-Free String Constraints*, ATVA 2019 |

**Decidable / semi-decidable fragments used in practice (the target menu):**

| Fragment | Citation |
|---|---|
| **Straight-line** (each var assigned ≤ once): decidable via **backward pre-image** | Lin & Barceló, POPL 2016; Chen, Hague, Lin, Rümmer, Wu (OSTRICH), POPL 2019 |
| **Acyclic** (underlies Norn) | Abdulla et al., CAV 2014/2015 |
| **Chain-free** (generalizes both; multi-occurrence like `xy=zz`) / **weakly-chaining** | Abdulla et al., ATVA 2019 |
| **Quadratic** WE + length (decidable when counter system flat; NP with PAD oracle) | Lin & Majumdar, ATVA 2018 / LMCS 17(4), 2021 |
| **regex + LIA-over-length** (no WE, no stacked complement): **PSPACE-complete** | Berzish et al., CAV 2021 (arXiv:2010.07253) |
| **Parikh's theorem** — regular/CF letter-count image is semilinear ⇒ ∃-Presburger | Kopczyński & Lin, LICS 2010 |

## 2. The four solver families

### A — Length-aware DPLL(T) normalization (cvc5/CVC4) — QF_Strings champion 2019–2023

- **Foundational:** Liang, Reynolds, Tinelli, Barrett, Deters, *A DPLL(T) Theory
  Solver for a Theory of Strings and Regular Expressions*, **CAV 2014**.
- **Architecture:** string theory = **congruence-closure (EUF) extension + theory
  derivation rules**, combined **Nelson-Oppen-style with a LIA solver over shared
  `len(x)` terms**. Refutation- & solution-sound; deliberately incomplete.
- **Core mechanics:** confluent/terminating normalization (flatten `++`, drop ε,
  fuse constants, push `len` through `++`) → **flat forms → normal forms** per
  equivalence class. Key rules: **`F-Split`** (arrangement: branch on which unequal
  prefix is a prefix of the other, fresh Skolem), **`F-Loop`** (break the loops
  that make star-unrolling diverge), **`Len-Split`** (`x≈ε ∥ len x>0`).
- **Extended functions:** lazy reduction + **Context-Dependent Simplification**
  (Reynolds et al., **CAV 2017**) + **high-level abstractions** (arithmetic-
  entailment, multiset, containment over/under-approx — Reynolds et al., **CAV
  2019**).
- **Recent:** *Even Faster Conflicts and Lazier Reductions* (Nötzli et al., **CAV
  2022**) — eager conflict detection via enriched congruence closure (constant
  prefix/suffix), lazier negated-regex reductions. cvc5 emits **fine-grained
  checkable proofs** (TACAS 2022).
- **Tradeoff:** strong on word-equation/extended-function-heavy sets; weaker on
  regex-heavy ones.

### B — Z3 sequence (`seq`) theory + symbolic derivatives

- Strings = special case of a **theory of sequences** over a parametric element
  sort; hybrid free-monoid equational solving + integer arithmetic for
  lengths/substrings.
- **Regex via symbolic Boolean derivatives** — Stanford, Veanes, Bjørner,
  *Symbolic Boolean Derivatives for … Extended Regular Expression Constraints*,
  **PLDI 2021**: handles **intersection and complement directly via derivatives**
  (no determinization), works **symbolically over an arbitrary character theory**
  (scales to Unicode), derivative count **linear** for Boolean combinations of
  classical regexes.

### C — Z3str line (arrangement-based)

- **Z3-str** (Zheng, Zhang, Ganesh, FSE 2013) → **Z3str2** (FMSD 2017,
  overlapping-variable detection, bidirectional str↔int pruning) → **Z3str3**
  (Berzish, Zheng, Ganesh, FMCAD 2017: **arrangement** → per-arrangement length
  query → **fixed-length equations reduced to bit-vectors** → CDCL backtrack;
  **theory-aware branching**) → **Z3str4** (FM 2021: **multi-armed portfolio**
  with a Length Abstraction Solver / CEGAR + Z3seq). *Caution:* Z3str4 and cvc5
  both had **soundness bugs flagged at SMT-COMP 2021**.

### D — Automata / derivative / flattening

- **Derivative foundations:** Brzozowski (*JACM* 1964, DFA, finite up to
  similarity ⇒ termination); Antimirov (*TCS* 1996, partial derivatives, NFA ≤ n+1
  states); Owens, Reppy, Turon (*JFP* 2009, Boolean ops + large-alphabet
  partitioning — precursor to symbolic derivatives).
- **Symbolic automata/transducers:** D'Antoni & Veanes, CAV 2017; the .NET 7
  nonbacktracking regex backend (Moseley et al., PLDI 2023).
- **OSTRICH** (POPL 2019, straight-line backward pre-image; POPL 2022 adds
  Prioritized Streaming String Transducers; **OSTRICH2** arXiv:2506.14363, 2025 —
  completeness for straight-line + chain-free, full Unicode/ECMAScript regex).
- **Trau / Z3-Trau** (*Flatten and Conquer*, PLDI 2017; FMCAD 2018 — parametric
  flat automata + Parikh, dual under/over-approximation CEGAR).
- **Sloth** (POPL 2018 — alternating finite automata + IC3-style emptiness; avoids
  determinization blowup). **Norn** (CAV 2014 — foundational acyclic automata).

## 3. Key sub-problem techniques

**Regex membership (`str.in_re`):**
- Naive star-unroll (`s∈r* ⇒ s≈ε ∨ (s≈xy ∧ x∈r ∧ y∈r*)`) is **non-terminating** —
  must be loop-guarded (cvc5 `F-Loop`).
- **Best practice = symbolic derivatives + transition regexes** (nested ite over
  character predicates): `nullable(R)` is the per-step acceptance check; complement
  propagates lazily into leaves via De Morgan (no determinization); linear
  derivative count for Boolean combos (PLDI 2021). **Bounded loops `R{k}` are a
  native derivative construct, never pre-unrolled** (Veanes, LPAR 2024).
- Competitive lazy-automata alternative: Z3str3RE (CAV 2021) — beat CVC4 2.4×,
  Z3seq 4.4×, OSTRICH 13× on 57k regex instances.

**Length constraints (Nelson-Oppen with LIA):** share **`len(x)` terms** (integer
variables), not raw string variables (Nelson & Oppen, *TOPLAS* 1979). cvc5 uses
**polite combination via care graphs** over a shared equality engine + model
manager. **Parikh/LIA length over-approximation** gives cheap UNSAT before regex
unfolding (CATRA, OOPSLA 2024; *Parikh's Theorem Made Symbolic*, POPL 2024).

**Extended functions:** layered — a minimal core (`++`, `len`, `in_re`) + lazy
reductions of the rest. `¬contains(x,y)` reduces to bounded universal
quantification over positions (expensive) ⇒ reduce **lazily** with
context-dependent simplification (often avoids the reduction entirely when a var
is partially concrete). `to_int`/`from_int`/`to_code` via dedicated **code-point
reasoning**, not word equations.

**Model construction / unbounded length:** cvc5 uses **length bucketing +
cardinality** — partition equivalence classes into buckets that *could* share a
length; on saturation give each bucket a unique concrete length, and a `Card` rule
guarantees enough distinct alphabet constants of that length to give each class a
distinct witness. Termination via flat/normal forms + loop-breaking, **not** a
global length bound. Z3str3RE instead **derives explicit length bounds from
regexes** and solves the LIA length subproblem first.

## 4. SMT-COMP winners (QF_Strings = QF_S + QF_SLIA + QF_SNIA)

| Year | Winner | Note |
|---|---|---|
| 2019–2020 | **CVC4** | DPLL(T) normalization |
| 2021 | **cvc5** | (cvc5 & Z3str4 soundness fixes flagged) |
| 2022 | **cvc5** | 15,394 solved |
| 2023 | **cvc5** | 30,291 solved, 0 errors |
| **2024** | **Z3-Noodler** | won "by a large margin" |
| **2025** | **Z3-Noodler-Mocha** | order: Noodler-Mocha > Z3-Noodler > OSTRICH > cvc5 > Z3-alpha |

- **cvc5** wins on word-equation/extended-function-heavy sets (DPLL(T)
  normalization + lazy reductions + CDS + eager congruence conflicts).
- **Z3-Noodler** (Chen et al., *Z3-Noodler: An Automata-based String Solver*,
  **TACAS 2024**) forks Z3, replacing only the string theory; backend = **MATA**
  C++ automata lib; core = **stabilization-based** WE + regex + lengths (*Solving
  String Constraints with Lengths by Stabilization*, **OOPSLA 2023**) + Nielsen
  transformation for quadratic equations. Wins because the automata/stabilization
  approach is **highly complementary** to the word-equation approach — dominating
  regex-/equation-heavy sets. Z3-Noodler 1.3 (TACAS 2025) adds model generation;
  the 2025 **Mocha** variant adds transducers.

## 5. Recommended target architecture (for the pure-Rust solver)

**Base family: DPLL(T) word-level normalization core (cvc5-style), augmented with
symbolic-derivative regex (Z3-style) and an automata/stabilization fallback arm
(Z3-Noodler-style) — on a pure-Rust automata substrate.**

Rationale:
- **Word-level + unbounded** by construction — the right replacement for the
  current bounded bit-blast (keep that only as a small-instance pre-check).
- **Plugs into axeyum's existing congruence-closure / e-graph** — the string
  theory is "EUF + derivation rules + a Nelson-Oppen link to LIA over `len`",
  reusing infrastructure rather than importing a separate C++ automata lib (MATA),
  which would violate the **no-C/C++ hard rule**.
- **Refutation- & solution-sound even when incomplete** — exactly axeyum's stance;
  the open-decidability boundary means we return `unknown`, never a wrong verdict.

Components to borrow (→ map to Phases A–E):
1. **Core theory solver** = congruence-closure extension + CAV 2014 derivation
   rules; confluent normalization as a hard invariant; `F-Split`/`Len-Split`/
   `F-Loop`; cvc5's eager constant prefix/suffix conflict detection (CAV 2022).
2. **Length/LIA combination** — reuse the LIA online solver; share `len(x)`
   Nelson-Oppen-style; add **Parikh/semilinear over-approximation** for cheap,
   checkable UNSAT.
3. **Regex** = **symbolic Boolean derivatives + transition regexes** (PLDI 2021),
   symbolic character theory, `nullable` acceptance, lazy complement, **native
   bounded loops** — the highest-leverage modern technique. Rust substrate:
   **`regex-automata`** (rust-lang DFA/NFA engines), **`aws-smt-strings`**
   (regex→DFA + derivatives + emptiness, pure Rust), **`smt-str`** (SMT-LIB string/
   regex semantics + regex→NFA, Rust) — evaluate as deps or design references.
4. **Extended functions** — lazy reduction into the core + context-dependent
   simplification (CAV 2017) + arithmetic-entailment/multiset/containment
   abstractions (CAV 2019); dedicated code-point reasoning.
5. **Model construction** — length bucketing + cardinality (CAV 2014); every SAT
   model replay-checkable.
6. **Automata fallback arm** — stabilization-style (OOPSLA 2023) for
   regex/equation-heavy instances where derivative+normalization stalls, on the
   pure-Rust `regex-automata`/`aws-smt-strings` substrate (not MATA).
7. **Alphabet** — **SMT-LIB Unicode Strings**: code points `0x00000–0x2FFFF`
   (Planes 0–2, 196,608), with a **total order** (load-bearing for the
   bucketing/cardinality model argument and determinism). `to_lower`/`to_upper`
   on the ASCII portion only.

## 6. Lean-parity bonus (Track 3)

The load-bearing soundness facts are mechanizable: *Finiteness of Symbolic
Derivatives in Lean* (ITP 2025), *Certified Symbolic Finite Transducers*
(arXiv:2504.07203). Regularity-preserving pre-image lemmas (OSTRICH) and
derivative finiteness (Brzozowski) are the certificates a trusted checker
re-derives. **An UNSAT via LIA/Parikh length abstraction is the easiest first
checkable-evidence target.**
