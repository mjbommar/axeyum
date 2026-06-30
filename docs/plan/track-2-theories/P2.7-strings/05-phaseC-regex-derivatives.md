# P2.7 · Phase C — Regex membership via symbolic Boolean derivatives

**Size:** L · **Depends on:** Phase B (the core solver it feeds inferences to) ·
**The single highest-leverage modern technique.**

> Replace the bounded Thompson-NFA simulation with **symbolic Boolean derivatives +
> transition regexes** (Stanford/Veanes/Bjørner, PLDI 2021): handles intersection
> and complement **directly via derivatives** (no determinization), works
> symbolically over the Unicode character theory, and has a **linear** derivative
> count for Boolean combinations of classical regexes.

## The technique

- A regex `R` over a **symbolic character theory** (predicates over code points,
  not enumerated bytes). Membership `s ∈ R` is decided by stepping:
  - **`nullable(R)`** — does `R` accept ε? (the per-step acceptance check)
  - **derivative `∂_a R`** — the regex matching the rest of the string after a
    leading character satisfying predicate `a`. Represented as a **transition
    regex**: a nested `ite` over character predicates whose leaves are regexes.
- **Boolean operators propagate through derivatives** by De Morgan, so
  `∩`, `∪`, complement `∁` are **lazy** — no determinization, no NFA product
  blowup. Complement pushes into the leaves.
- **Termination:** derivatives are finite up to similarity (Brzozowski 1964); the
  symbolic form keeps the alphabet partitioning compact for Unicode.

## Native bounded loops (do NOT pre-unroll)

`R{n,m}` is a **native derivative construct** (Veanes, LPAR 2024), never expanded
into `n..m` copies. This is the correctness-and-performance crux that the current
bounded encoder gets wrong (it pre-unrolls `Loop`).

## Integration with the core solver

- Membership atoms `str.in_re x R` and their negations are handled by this
  sub-solver; it emits **inferences** to the Phase-B inference manager (facts /
  splitting lemmas / conflicts).
- On a partial assignment, step the derivative by the known prefix; defer the rest
  (lazy unfolding at full effort), and use **`F-Loop`** (Phase B) to regularize
  loops that arise from word-equation reasoning.
- **Inclusion / intersection checks** between (sufficiently concrete) regexes prune
  early: `R₁ ⊆ R₂` via `R₁ ∩ ∁R₂ = ∅` (derivative emptiness).

## Pure-Rust substrate (no C/C++)

Evaluate as dependencies or design references (keep `forbid(unsafe_code)` + WASM):
- **`regex-automata`** (rust-lang/regex internals) — mature DFA/NFA engines.
- **`aws-smt-strings`** — regex→DFA, derivatives, emptiness, in pure Rust.
- **`smt-str`** — SMT-LIB string/regex semantics + regex→NFA, in Rust.

Do **not** depend on MATA (C++) — that is the line the no-C/C++ rule draws.

## Tasks

| id | task | key refs | size | exit |
|---|---|---|---|---|
| T-C.1 | symbolic character predicates over the Unicode alphabet (with total order) | PLDI 2021; smt-lib.org Unicode theory | M | predicate algebra (∧/∨/¬, sat, partition) |
| T-C.2 | `nullable` + transition-regex derivative `∂_a R` | Brzozowski 1964; Owens et al. JFP 2009; PLDI 2021 | L | derivatives correct vs reference matcher |
| T-C.3 | lazy Boolean ops (∩/∪/∁) via derivative De Morgan | PLDI 2021 | M | complement/intersection without determinization |
| T-C.4 | native bounded loop `R{n,m}` | Veanes LPAR 2024 | M | no pre-unrolling; correct & bounded |
| T-C.5 | membership sub-solver: step on partial prefix, emit inferences, inclusion/emptiness pruning | cvc5 `regexp_solver/operation` | L | regex constraints decided over unbounded strings |
| T-C.6 | evaluate/adopt pure-Rust substrate (`regex-automata`/`aws-smt-strings`/`smt-str`) | — | M | ADR: dep vs reference; WASM-green |

## Soundness

- Membership decisions feed the core; every resulting `sat` model is replay-checked
  by the ground evaluator's regex semantics.
- Derivative **finiteness** (the termination guarantee) is a Lean-mechanizable
  lemma (*Finiteness of Symbolic Derivatives in Lean*, ITP 2025) — a Track-3 target.
- Outside the supported regex fragment (e.g. backrefs) ⇒ `unknown`.

## Exit criteria

- `str.in_re` decided over **unbounded** strings via symbolic derivatives, with
  native bounded loops and lazy complement/intersection (no determinization).
- Measured: regex-heavy instances the bounded encoder can't touch now decide;
  DISAGREE=0 vs Z3 on a regex fuzz set.
- ADR records the pure-Rust automata substrate choice.
