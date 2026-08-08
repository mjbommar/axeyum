# P2.7 · 00 — Current state: layered and sound-incomplete

Status: maintained implementation snapshot; last reviewed 2026-08-07

Axeyum no longer has only one bounded string encoder. The current implementation
is a portfolio with three distinct layers:

1. first-class `Sort::Seq` terms and values in `axeyum-ir`;
2. a packed-BV SMT-LIB fast path with explicit finite bounds; and
3. source-level word, membership, lexicographic, and length/LIA routes that can
   decide selected queries beyond the initial packed window.

This portfolio is sound-incomplete. It is not a complete unbounded SMT-LIB
string theory, and the public text front door does not uniformly translate
`String`/`Seq` syntax into first-class `Sort::Seq` terms.

## Current representations

### First-class IR sequences

`axeyum-ir` has `Sort::Seq(ArraySortKey)`, `Sort::string()`, `Value::Seq`, and
the first sequence operators (`SeqLen`, `SeqEmpty`, `SeqUnit`, and
`SeqConcat`). The ground evaluator covers those operators. This is the term
language used by the word-level `axeyum-strings` core.

Its existence does not settle the parser representation fork. The established
SMT-LIB path still lowers supported `String` and finite `Seq` syntax into packed
bit-vectors, while source-level side channels build first-class sequence
problems for selected later routes.

### Packed-BV fast path

A packed string stores a bounded length and byte content with canonical
padding. The limits belong to different APIs and must not be conflated:

| Surface | Current bound |
|---|---:|
| Rust `BoundedString` API | `max_len` in `1..=16` |
| Default declared SMT-LIB string window | 12 bytes |
| Front-door retry ladder | 24, 32, then 48 bytes |
| Direct string-literal adaptive limit | 256 bytes |
| Packed result/window hard cap | 512 bytes |

Variable concatenation sums operand bounds and declines if the packed result
would exceed the 512-byte cap. A wider-window `sat` is accepted only after model
replay. A wider-window `unsat` is still a bound artifact unless a separate
bounded-completeness or source-level checker justifies it.

## Current decision routes

| Route | What is landed | Assurance boundary |
|---|---|---|
| Packed BV | equality, length, concatenation, substring/scan, replacement, code/int conversions, bounded regex, and related supported shapes | returned SAT models replay; clausal UNSAT evidence remains modulo the trusted string lowering |
| Word equations | normalization, class/normal-form inference, budgeted arrangement search, and selected checked refutations in `axeyum-strings` | SAT assignments replay; UNSAT is returned only for admitted derivations that an independent checker re-derives |
| Boolean word structure | online CDCL(T)-style handling for admitted Boolean word skeletons | replay/checker guarded; unsupported skeletons decline |
| Regex membership | bounded Thompson-NFA lowering plus selected source-level membership decisions and certificates | route-specific; no fragment-wide string proof artifact |
| Lexicographic order | selected source-level lexicographic refutations | checked admitted shapes; broader formulas decline |
| Length + LIA | bounded `bv2nat` reasoning and a source-level length/LIA bridge, including over-window SAT witnesses | SAT replay and checked admitted UNSAT shapes; general word/length combination remains incomplete |
| String ↔ integer | bounded lowering plus selected exact source rewrites and word-obligation inversion | partial; unsupported `str.to_int`/`str.from_int` couplings return `unknown` |

The generated [support matrix](../../../research/08-planning/support-matrix.md)
therefore classifies strings as **sound, incomplete (unknown-safe)** and assigns
no general proof support. Selected checked subroutes do not upgrade the entire
fragment.

## What remains open

- one canonical `String`/`Seq` parser representation and lowering contract;
- general unbounded word equations combined with arithmetic and regex;
- symbolic-derivative regex and a general automata/stabilization fallback;
- complete extended-function reductions and model construction;
- a fragment-wide UNSAT artifact that closes every trusted lowering layer; and
- production-depth performance beyond the retained measured slices.

The open boundary is broader than a `str.len` BV+LIA gap: that original marker
has dedicated routes now. Remaining `unknown` results arise from unsupported
combinations, incomplete procedures, bounds, or resource limits.

## Authorities

- [`crates/axeyum-ir/src/sort.rs`](../../../../crates/axeyum-ir/src/sort.rs) and
  [`term.rs`](../../../../crates/axeyum-ir/src/term.rs) define first-class
  sequence IR.
- [`crates/axeyum-smtlib/src/parse.rs`](../../../../crates/axeyum-smtlib/src/parse.rs)
  defines packed-string parsing and hard limits.
- [`crates/axeyum-strings`](../../../../crates/axeyum-strings/src/lib.rs) defines
  word-level normalization, search, and checked refutation.
- [`crates/axeyum-solver/src/smtlib.rs`](../../../../crates/axeyum-solver/src/smtlib.rs)
  defines front-door route order, retry policy, and replay/checker boundaries.
- The generated [capability matrix](../../../research/08-planning/capability-matrix.md),
  [support matrix](../../../research/08-planning/support-matrix.md), and
  [trust ledger](../../../research/08-planning/trust-ledger.md) are the public
  status authorities.
