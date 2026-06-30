# P2.7 · 00 — Current state: the bounded string encoder

Accurate baseline (grounded in `crates/axeyum-solver/src/strings.rs`, ~1305
lines). axeyum's strings are **sound and bounded** — the right starting point, but
fundamentally length-capped.

## Encoding — a `(len, content)` bit-vector pair

- **Representation:** each string is `(len, content)` where `len` is a
  `BitVec(len_width)` holding the actual length (constrained `len ≤ max_len`), and
  `content` is a `BitVec(max_len × 8)` with byte `i` at bits `[8i, 8i+7]`.
- **Bounds:** `max_len ∈ [1, 16]` (enforced at construction); content width
  capped at **128 bits** (the IR BV ceiling); `len_width = 32 − leading_zeros(max_len)`.
- **Well-formedness:** `len ≤ max_len` asserted per declared variable.
- This is the **HAMPI/Kaluza bounded** approach: everything lowers to a pure
  bit-vector / Boolean formula, solved by the existing BV→SAT path. Models replay
  through the ground evaluator; UNSAT carries a DRAT proof.

## Operators implemented (all within the bound)

- **Structural:** `len`, `=`.
- **Substring/scan:** `prefixof`, `contains`, `suffixof`, `indexof` (constant
  start), `substr` (constant + symbolic start).
- **Replace:** `replace` (first occurrence; result sort `BoundedString(2·max_len)`),
  `replace_all` (non-overlapping L→R; result sort `BoundedString(max_len²)`),
  `replace_same_len`.
- **Concat** `str.++` (result sort `BoundedString(max_len_x + max_len_y)`, capped 16).
- **Comparison:** lexicographic `<`, `≤`.
- **Symbolic:** `take`/`drop` (symbolic byte count).
- **Regex** `str.in_re`: Thompson NFA simulation.
- **Numeric:** `to_int`/`from_int` (decimal), `to_code`/`from_code`, digit check.

## Regex fragment

- **Automaton-expressible core:** `Empty, Char, Range, AnyChar, Concat, Union,
  Star, Plus, Opt, Loop` (bounded `a{n,m}`).
- **Boolean combinators top-level only:** `Inter, Comp, Diff` — **cannot** nest
  under `Concat`/`Union`/`Star` (violation ⇒ `IrError::Unsupported`).
- Thompson NFA compiled once; epsilon-closure precomputed; symbolically simulated
  position-by-position per input length.

## What is sound / what it can never decide

**Sound:** every operation lowers to BV/Boolean; replay + DRAT carry through. The
adversarial `str_differential_fuzz` vs Z3 is **DISAGREE=0 over 371 instances**.

**Cannot decide (⇒ `unknown` or rejected):**
- Strings longer than `max_len` (rejected at encoding, `IrError::InvalidWidth`).
- **Unbounded strings** — there is no first-class sequence/string sort in the IR.
- `replace_all` when `max_len² > 16`.
- Boolean combinators nested in repetitions; non-Thompson regex (lookahead,
  backrefs, advanced anchors).
- `str.len` **unsat** can be `unknown` — the BV+LIA combination gap (P1.6).

## Capability-vs-gap table

| Area | Decide today | Assurance | Boundary to close |
|---|---|---|---|
| Bounded ops | all `str.*` within `max_len ≤ 16` | validated (replay + DRAT) | **unbounded length** |
| Regex | Thompson NFA; Boolean top-level only | validated | nested Boolean; symbolic-derivative regex; complement under concat |
| `str.len` unsat | sometimes `unknown` | sound | **BV/String + LIA combination** (P1.6 / Phase A) |
| String⇄int | bounded decimal | validated | unbounded; undecidable in full (Ganesh–Berzish 2016) |

## The one-sentence gap

We decide the **bounded** SMT-LIB string fragment exactly; the **unbounded,
length-aware word-equation + regex + extended-function** theory that Z3/cvc5 solve
is missing — that is what Phases A–E build.

## What we reuse (don't rebuild)

- The bounded encoder stays as a **fast pre-check** for provably-small instances.
- The existing **LIA online solver** is the Nelson-Oppen partner over `len` terms.
- The **e-graph / EUF** core (P1.4) is the congruence-closure substrate the string
  theory extends.
- The **replay + DRAT + differential-fuzz** discipline is already in place.
