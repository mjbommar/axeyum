# ADR-0054: Regex via symbolic derivatives — from-scratch in `axeyum-strings`

Status: accepted (2026-07-06 — the derivative engine + membership sub-solver + T-C.5/C.6 are landed, measured, and scoreboard-moving)
Date: 2026-07-03

## Context

The Phase-B word-equation core is live in both directions (ADR-0053; QF_S
52→57, word fuzz 96 sat + 305 unsat at DISAGREE=0), and the coverage-boundary
census ([Phase B doc](../../plan/track-2-theories/P2.7-strings/04-phaseB-word-equations.md),
2026-07-03) is unambiguous about what's next: **regex membership blocks 15 of
the 35 remaining gate-downgraded string unknowns** — the largest single
measured demand in the string program. The
[Phase C plan](../../plan/track-2-theories/P2.7-strings/05-phaseC-regex-derivatives.md)
prescribes the technique (symbolic Boolean derivatives + transition regexes,
PLDI 2021; native bounded loops, LPAR 2024) and requires an ADR for the
pure-Rust automata substrate (its T-C.6; deferred there by ADR-0053).

What exists today: `axeyum-smtlib/src/regex.rs` (~1131 lines) — a private,
**byte-oriented** SMT-LIB regex layer for the bounded packed-BV route
(Thompson NFA, concrete `matches(&[u8])`, length intervals, emptiness) that
pre-unrolls `re.loop` and enumerates complement/intersection through NFA
products. It is exactly the engine the Phase-C plan replaces for the
unbounded route — but it stays untouched as the bounded route's tool.

## Decision

**Build the symbolic-derivative engine from scratch inside `axeyum-strings`
(`src/regex/`), over the Unicode code-point alphabet as interval-set
predicates; adopt NO external automata dependency. `regex-automata`,
`aws-smt-strings`, and `smt-str` are design references only (shallow clones
under `references/`), alongside cvc5's `regexp_solver`.**

- **Why from-scratch, not a dependency.** (a) The technique is the point:
  transition-regex derivatives with lazy `∩`/`∪`/`∁` via De Morgan are not
  what `regex-automata` provides (it is DFA/NFA machinery without a
  complement/intersection algebra over symbolic predicates). (b) The
  derivative engine is future trusted-adjacent surface: derivative
  finiteness is a Lean-mechanizable lemma (ITP 2025) and Phase-C unsat
  evidence will cite derivative steps — we need to own the representation
  the proofs quote. (c) The engine is small relative to its importance
  (predicate algebra + `nullable` + `∂` + similarity-canonicalization), and
  `aws-smt-strings`/`smt-str` would be load-bearing external deps inside the
  soundness perimeter — against the grain of ADR-0002's dependency posture.
  WASM/`forbid(unsafe_code)` stay trivially green with no new deps.
- **Alphabet & predicates (T-C.1).** Characters are Unicode code points under
  the `BitVec(18)` order fixed by ADR-0051. A character predicate is a
  canonical **sorted set of disjoint inclusive ranges** (interval set) with
  `∧`/`∨`/`¬`, emptiness, a witness, and mintermization (partitioning a
  finite predicate set into disjoint atoms) — sufficient for `re.range`,
  literals, `re.allchar`, and all Boolean combinations; no enumeration of
  the 2^18 alphabet ever happens.
- **Engine (T-C.2..T-C.4).** `nullable(R)` + transition-regex derivative
  `∂(R)` as a nested if-then-else over predicates with regex leaves;
  Boolean nodes (`Inter`/`Union`/`Comp`) push through derivatives lazily —
  no determinization; `R{n,m}` is a native construct, never pre-unrolled
  (the known correctness/blowup defect class of the bounded encoder).
  Similarity-canonicalization (associativity/commutativity/idempotence
  normal form) bounds the derivative set (Brzozowski); a budget guards the
  remainder → first-class `unknown`.
- **Verdict discipline (the ADR-0053 contract extends unchanged).**
  Membership-constrained `sat` returns only with a concrete assignment that
  replays — the regex leg of replay is a **separate simple reference
  matcher** (structural recursion over the regex on the concrete string; no
  NFA, no derivative code shared with the engine — independence mirrors
  `check_derivation`). Membership-driven `unsat` is returned only when it
  carries a re-checkable derivation (a derivative-emptiness trace whose
  steps an independent checker replays); until that checker lands, regex
  unsat declines to `unknown`.
- **Front-end.** The parser's `WordProblem` side channel gains positive
  membership atoms (`str.in_re x R`) carrying a code-point regex AST;
  the byte-oriented bounded path and its `regex.rs` are untouched (per-route
  fork resolution, ADR-0053). Negative membership (`not in_re`) enters only
  as complement — which the engine handles natively — behind the same
  all-or-nothing conservatism.

## Evidence

- Measured demand: 15/35 census files are regex-blocked; the bounded route
  cannot grow to them (length-capped, pre-unrolled loops).
- The bounded engine's own history motivates the replacement technique: its
  `re.loop` pre-unrolling and product constructions are the shapes behind
  prior bound-bite wrong-unsat repairs (ADR-0052).
- Reference implementations exist for cross-checking behavior
  (`references/cvc5` regexp solver; the PLDI-2021 artifact semantics;
  `aws-smt-strings` derivative tests as an oracle for unit vectors).

## Alternatives

- **Depend on `aws-smt-strings` or `smt-str`.** Rejected: both put external
  code inside the future proof perimeter and neither provides the
  transition-regex representation the Lean-facing evidence will quote;
  consulted as references instead.
- **Extend `axeyum-smtlib/regex.rs`.** Rejected: it is byte-alphabet,
  NFA-product-based, and private to the bounded route; retrofitting symbolic
  predicates + derivatives would rewrite it anyway while risking the
  validated bounded surface.
- **DFA/NFA product approach (determinize for ∩/∁).** Rejected: the exact
  blowup the derivative technique exists to avoid; complement over Unicode
  without symbolic predicates is impractical.

## Consequences

- **Easier:** the 15-file regex demand becomes reachable; complement and
  intersection are native; the derivative trace is a natural evidence
  object for Track 3; the engine is reusable for `Seq(BitVec w)` alphabets
  later (predicates generalize to any ordered finite alphabet).
- **Harder / cost:** we own correctness of a subtle engine — mitigated by
  the reference matcher replay gate, differential fuzz vs Z3 over regex
  scripts (both directions, as the word fuzz), unit vectors cross-checked
  against reference implementations, and the decline-by-default unsat rule.
- **Revisited when:** the derivative-emptiness checker lands (opens regex
  unsat); Phase E model construction needs automata-style witnesses; or a
  measured performance wall argues for a compiled-DFA fast path (a later,
  additive ADR).

## Foundational-DAG / register updates

- Add the symbolic-derivative membership solver under the string-theory
  layer (new public fragment surface: unbounded `str.in_re` sat).
- Close the Phase-C T-C.6 substrate question with a link here.
