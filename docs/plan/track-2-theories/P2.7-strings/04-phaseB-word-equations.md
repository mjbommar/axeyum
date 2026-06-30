# P2.7 · Phase B — The word-equation core

**Size:** XL (the engine that makes strings unbounded) · **Depends on:** Phase A,
[P1.4 e-graph](../../track-1-engine/P1.4-egraph.md) · **The heart of P2.7.**

> This is the cvc5 CAV-2014 procedure: a congruence-closure extension with string
> derivation rules, computing **normal forms** per equivalence class and branching
> with **arrangement** rules. It targets the decidable fragments (straight-line,
> acyclic, chain-free) and is `unknown`-safe (loop-guarded) outside them.

## The normalization invariant (do this first, always)

A confluent, terminating rewrite applied before any reasoning:
- **flatten** nested `++`; **drop** ε components; **fuse** adjacent string
  constants; **push `len`** through `++` and constants.
This makes equal strings syntactically comparable and is the precondition for
flat/normal-form computation.

## Flat forms → normal forms

- **Flat form** of `x++y++z`: replace each component by its equivalence-class
  representative, drop ε. Lightweight.
- **Normal form** of an equivalence class `[x]`: a vector `[r₁,…,rₙ]` of sub-class
  representatives such that concatenating decomposed terms yields the same
  representatives. Computed **bottom-up** over an **acyclic ordering** of string
  classes (cycle detection first).

## The derivation / arrangement rules

| Rule | What it does |
|---|---|
| **cycle detection** | build containment order `e₁<e₂` if `e₁` in flat form of `e₂`; ensure acyclic (infer ε on cycles) |
| **normal-form inference** | `INFER_UNIFY` (same-length components at a position must be equal), `INFER_ENDPOINT_EQ` / `INFER_ENDPOINT_EMP` (tail handling) |
| **`F-Split`** (arrangement) | two unequal-length prefixes: branch on which is a prefix of the other, introduce a fresh Skolem |
| **`Len-Split`** | branch `x ≈ ε  ∥  len(x) > 0` |
| **`F-Loop`** | detect `x = … x …` repeating patterns; **break the loop** by emitting a regex constraint `str.in_re x R` instead of unrolling forever (the key **termination** device) |
| **disequality** | for equal-length classes with different reps, find the first differing position; split on lengths otherwise |

## Eager conflict detection (cheap, high-yield — cvc5 CAV 2022)

On partial assignments, infer **constant prefix/suffix** facts via an enriched
congruence closure and detect conflicts early (e.g. two classes forced to share a
length but with incompatible constant prefixes). Implement as notifications on
equivalence-class merge/new-class events.

## Inference manager (fact / lemma / conflict routing)

Each inference carries `(conclusion, premises, new-skolems)`:
- **Fact** (no new premises, conclusion in the e-graph) → assert to the equality
  engine.
- **Lemma** (introduces premises/skolems) → send to the SAT core.
- **Conflict** (conclusion false) → report.
Track explanation dependencies for minimal conflicts (cvc5's `d_expDep`).

## Tasks

| id | task | key refs | size | exit |
|---|---|---|---|---|
| T-B.1 | normalization invariant (flatten/drop-ε/fuse/push-len) | cvc5 `theory_strings_rewriter` | M | confluent; property-tested |
| T-B.2 | flat form + normal form + explanation tracking | cvc5 `normal_form`, `core_solver` | L | normal forms correct on test classes |
| T-B.3 | cycle detection + normal-form inference rules | cvc5 `core_solver::checkCycles/normalize` | L | inferences match cvc5 on shared examples |
| T-B.4 | `F-Split` / `Len-Split` arrangement branching | LRT CAV 2014 | L | straight-line/acyclic word equations decided |
| T-B.5 | **`F-Loop`** loop-breaking (regex constraint emission) | LRT CAV 2014 | M | star/loop equations terminate (no divergence) |
| T-B.6 | eager constant prefix/suffix conflict detection | cvc5 CAV 2022 | M | measured early conflicts; fewer branches |
| T-B.7 | inference manager (fact/lemma/conflict + explanations) | cvc5 `inference_manager` | M | minimal conflicts; integrates with CDCL(T) |

## Soundness & termination

- **Termination** is by flat/normal forms + **`F-Loop`** (regularizing loops into
  regex constraints), **not** a global length bound. Outside the decidable
  fragments the solver may not terminate → enforce a **budget** and return
  `unknown` past it (first-class).
- **`sat`** ⇒ a normal-form-derived assignment that replays. **`unsat`** ⇒ a
  derivation (premises → conflict) that is re-checkable; the LIA/Parikh abstraction
  (Phase A) catches a useful subset cheaply.
- **Test harder than usual** — the CAV-2014 procedure is subtle and the reference
  solvers shipped soundness bugs here. Differential-fuzz every rule.

## Exit criteria

- Variable `++`, `substr`, symbolic-index equality over **unbounded** strings in
  the straight-line / acyclic / chain-free fragments decide; loops terminate via
  `F-Loop`; budget-guarded `unknown` outside.
- Every `sat` replays; `unsat` derivations re-checkable.
- `str_differential_fuzz` vs Z3 DISAGREE=0 on a large random word-equation set.
