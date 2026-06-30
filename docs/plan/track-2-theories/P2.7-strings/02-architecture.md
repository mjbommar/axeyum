# P2.7 · 02 — Architecture: a word-level, length-aware string theory solver

## The target, in one diagram

```
        ┌──────────────────────────────────────────────────────────────┐
        │  CDCL(T) core (Track 1, P1.5) + e-graph / EUF (P1.4)           │
        └───────────────┬──────────────────────────────────────────────┘
                        │ string atoms (=, in_re, contains, …)
                        v
   ┌─────────────────────────────────────────────────────────────────────┐
   │  STRING THEORY SOLVER  (= EUF extension + derivation rules)           │
   │                                                                       │
   │  normalization invariant: flatten ++, drop ε, fuse consts, push len   │
   │  flat forms → normal forms per equivalence class                      │
   │  arrangement rules: F-Split · Len-Split · F-Loop (loop-breaking)      │
   │  eager conflict: constant prefix/suffix on partial assignments        │
   │                                                                       │
   │   ├─ regex sub-solver: symbolic Boolean derivatives + transition      │
   │   │     regexes (nullable, lazy complement, native {k})               │
   │   ├─ extended-function reductions (lazy + context-dependent simpl.)   │
   │   └─ model construction: length bucketing + cardinality               │
   └───────────────┬───────────────────────────────────┬──────────────────┘
                   │ shares len(x) terms (Nelson-Oppen) │ stalls?
                   v                                     v
        ┌──────────────────────┐         ┌──────────────────────────────────┐
        │ LIA online solver     │         │ automata/stabilization fallback  │
        │ (+ Parikh length      │         │ arm (pure-Rust regex-automata /  │
        │  over-approximation)  │         │ aws-smt-strings substrate)       │
        └──────────────────────┘         └──────────────────────────────────┘
```

The string solver is **not** a monolith bolted on — it is "**EUF on the e-graph +
string derivation rules + a Nelson-Oppen link to LIA over `len` terms**", reusing
the congruence-closure and linear-arithmetic infrastructure Tracks 1/2 already
build. The bounded bit-blast encoder (`strings.rs`) is kept as a **fast pre-check**
for provably-small instances.

## The first decision: how strings live in the IR

Today there is **no first-class string sort** — strings are parsed and lowered
ad-hoc, and string-*valued* results (variable `++`, `substr`) are awkward (the
"`Parsed = Term | Str`" friction noted in the old P2.7 stub). The architecture
needs strings to be **terms** like any other sort. Two options (ADR in Phase A):

| Option | What | Pro | Con |
|---|---|---|---|
| **(A) First-class `Sort::String` / `Sort::Seq(elem)`** in `axeyum-ir` | a real sort with `len`, `++`, `nth`, … operators | clean; sequences generalize; matches SMT-LIB | touches the IR core; more up-front |
| (B) Shared `BoundedString`-style value channel | extend the existing encoder's value type | smaller blast radius | doesn't reach unbounded; technical debt |

**Lean: Option A** — a first-class `Sort::Seq(elem)` with `Sort::String` as
`Seq(Unicode)`. Strings *are* sequences of code points; cvc5 unifies them and so
should we (it also future-proofs `Seq` for P2.10). This is the enabling refactor
of Phase A.

## Why this base family (not bounded-only, not pure-automata)

- **Bounded bit-blast can't reach unbounded** — it is structurally length-capped.
  Keep it as a pre-check; don't grow it.
- **Pure-automata (Z3-Noodler/MATA) is excellent but C++** — the no-C/C++ hard rule
  forbids depending on MATA/libpoly. We can still build a **pure-Rust** automata
  fallback arm (Phase E) on `regex-automata`/`aws-smt-strings`, but it is the
  *second* arm, not the base.
- **DPLL(T) word-level normalization reuses our e-graph + LIA** and is the
  long-time champion's core — best leverage per unit of new infrastructure.

## No-C/C++ consequence (explicit)

The two shortcuts the C++ winners take are **closed to us**: cvc5/Yices link
**libpoly**; Z3-Noodler links **MATA**. Every automaton, derivative, and
length-abstraction routine is **built in pure Rust** (or via vetted pure-Rust crates
that keep `forbid(unsafe_code)` and the WASM build green). This is the same
constraint that shapes the NRA plan ([P2.5](../P2.5-nra-cad.md)) and is a feature,
not a bug: it keeps the default build C-free and WASM-able.

## Crate / module layout

```
crates/axeyum-ir/          # Phase A: add Sort::Seq(elem) + Sort::String, str/seq ops
crates/axeyum-strings/     # NEW — the word-level string theory solver (pure Rust)
  src/
    normal_form.rs   # flat form / normal form + explanation-dependency tracking
    core_solver.rs   # cycle detection, normal-form inference, F-Split/Len-Split/F-Loop
    eager.rs         # eager constant prefix/suffix conflict detection
    length.rs        # len-term extraction; Nelson-Oppen link to LIA; Parikh over-approx
    regex/
      derivative.rs  # symbolic Boolean derivatives, transition regexes, nullable
      membership.rs  # str.in_re solver; native bounded loops; lazy complement
    extf.rs          # extended-function lazy reductions + context-dependent simpl.
    model.rs         # length bucketing + cardinality witness construction
    automata.rs      # Phase E fallback arm (regex-automata / aws-smt-strings)
crates/axeyum-solver/      # routing: bounded pre-check → axeyum-strings → unknown
```

> **ADR required** before `axeyum-strings` lands (per ADR-0001 boundary rule):
> the boundary is proven by use (the solver + SMT-LIB front end both consume it).
> The ADR also records the Option-A IR-sort decision and the pure-Rust automata
> substrate choice (`regex-automata` vs `aws-smt-strings` vs `smt-str` — as deps or
> references).

## Soundness contract (every component)

1. `sat` ⇒ a concrete string assignment that **replays** through the ground
   evaluator against the original term (the hard rule; the `str_differential_fuzz`
   enforces it vs Z3).
2. `unsat` ⇒ a derivation that is independently re-checkable — easiest first target
   is a **LIA/Parikh length-abstraction UNSAT** (a self-contained certificate);
   later, the cvc5-style proof rules.
3. Outside the decidable fragments / past budget ⇒ `unknown`. Never a wrong
   verdict. **Remember cvc5 and Z3str4 both shipped soundness bugs here — test
   harder, not faster.**

## Interaction with other tracks

- **P1.4 e-graph / P1.5 CDCL(T):** the congruence-closure substrate and the loop
  the string `TheorySolver` runs on. Until they land, the string solver runs as a
  one-shot/eager procedure (mirroring today's bounded path) as a bridge.
- **P1.6 theory combination:** the String+LIA (over `len`) Nelson-Oppen link is a
  direct application — closing the `str.len`-unsat gap is the Phase A deliverable.
- **P2.6 quantifiers:** `¬contains` reductions are bounded-universal; e-matching
  helps but is not required for the core.
- **Track 3 proofs:** LIA/Parikh UNSAT certificates and derivative-finiteness
  lemmas are the Lean-parity targets.
