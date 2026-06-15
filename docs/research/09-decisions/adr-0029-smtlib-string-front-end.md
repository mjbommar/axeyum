# ADR-0029: SMT-LIB string front-end over the bounded-string BV lowering

Status: proposed
Date: 2026-06-14

## Context

The bounded-string theory (`axeyum-solver`'s `strings::BoundedString`, ADR-0025)
is now broad and well-tested: `str.len`/`=`/`++`/`at`/`substr`/`contains`/
`prefixof`/`suffixof`/`indexof`/`replace`/`replace_all`/`<`/`<=`/`to_int`/
`from_int`/`is_digit` and regex membership `str.in_re` (NFA-compiled). But it is
reachable **only through its Rust API** — the SMT-LIB text front door
(`solve_smtlib`, ADR-0018) has no `String` sort, no `"..."` literal lexing, and
no `str.*` dispatch. So real QF_S benchmarks cannot be fed as text, which is the
primary way the stack is exercised against Z3/cvc5 for parity.

The obstacle is structural, not algorithmic. The parser's every expression
builder returns `Result<TermId, SmtError>` — a single term handle. A
*string-valued* expression is not one term: `BoundedString` represents a string
as a `StrTerm { len, content }` **pair** of bit-vector terms (ADR-0025, no IR
`Sort::String`). String-producing operators (`str.++`, `str.substr`,
`str.replace`, `str.at`-as-string) compose, so a string subexpression can be an
arbitrary tree, not just a leaf. Threading that through requires the parser's
result type to carry both shapes. This is new public surface and a parser-wide
change, so it is decided here rather than in code.

Closes the "strings reachable from SMT-LIB text" half of ADR-0025's deferred
work; the unbounded string theory remains separate future work.

## Decision

**Wire strings into the SMT-LIB parser over the existing `BoundedString`
lowering, with no new IR sort.** Concretely:

- The parser gains a result type `Parsed = Term(TermId) | Str(StrTerm)` for
  expression translation; existing call sites that require a `TermId` (Bool/BV/
  Int/Real/FP contexts) reject a `Str` with a sort error, and the new `str.*`
  handlers accept/produce `Str`.
- A single `BoundedString` instance with a fixed `max_len` (default 16 — the
  ADR-0025 cap that keeps `content` within the 128-bit BV cap; overridable via a
  parser option / `set-option`) backs every string in a script. `String`-sorted
  `declare-fun`/`declare-const` allocate a fresh `StrTerm` (and assert its
  well-formedness, `len ≤ max_len`, as a side constraint).
- `"..."` string literals lex to constant `StrTerm`s; `str.*` operators and the
  `re.*` regex constructors dispatch to the matching `BoundedString`/`Regex`
  methods. Operators whose result exceeds the bound (a literal longer than
  `max_len`, a `++` that could overflow) are a clean `Unsupported`, never a
  silent truncation.
- **Model extraction**: a `sat` model's `StrTerm` (the lifted `len`/`content` BV
  values) is decoded back to a Rust `String` for `get-value`/the model, and the
  result stays replay-checkable through the bit-vector path (every `str.*`
  lowered to BV/Bool, so the existing "evaluate the original term against the
  lifted model" check applies unchanged).

The fragment is explicitly the **bounded-model-checking slice** (the shape
CBMC/Kani use): strings up to `max_len` decide soundly; longer ones are
`Unsupported`, never wrong.

## Evidence

- The `BoundedString` solver is already implemented, tested (28 cases incl.
  regex, `to_int`, `replace_all`), and BV-lowered — so this ADR is *plumbing*
  over a proven core, not a new decision procedure. The risk is confined to the
  parser, where a wrong translation surfaces as a parse/sort error or a
  replay-rejected model, not a wrong `sat`/`unsat`.
- The same "front door over a lowering" shape already works for FP
  (`(_ FloatingPoint eb sb)`, `fp.*`) and arrays — strings differ only in
  needing the two-term `StrTerm`, which the `Parsed` enum localizes.

## Alternatives

- **First-class `Sort::String`/`Sort::Seq` in the IR.** The complete approach and
  the prerequisite for *unbounded* strings, but it is the multi-crate `Sort`
  cascade ADR-0022 measured (~18 files) plus a native sequence decision
  procedure. Deferred: the bounded BV front-end lands a usable, sound slice now,
  exactly as bounded LIA/array elimination preceded their fuller procedures.
- **A separate string-only entry point** (not the main `solve_smtlib`). Rejected:
  real benchmarks mix strings with BV/Int constraints, so strings must live in
  the one parser, not a sibling.
- **Keep strings API-only.** Rejected: it blocks text-level QF_S parity testing,
  the whole point of the front door.

## Consequences

- *Easier:* QF_S benchmarks become text-parseable and differentially testable
  against Z3/cvc5 (within the length bound); the broad `BoundedString` surface
  becomes user-visible.
- *Harder / to watch:* the `Parsed` enum touches every parser expression site
  (mechanical but wide); `max_len` is a soundness-relevant knob (too small →
  more `Unsupported`, never wrong); model extraction must round-trip
  `len`/`content` to the exact significant bytes.
- *Revisited when:* unbounded strings are taken on (first-class `Sort::Seq`),
  which would supersede the bound — at which point this front-end becomes the
  fast bounded path under a complete procedure.
- *Unchanged:* no new IR sort; soundness rests on the existing BV path and model
  replay; `Unsupported`/`unknown` stay first-class.
