# ADR-0025: Bounded-Length Strings by Bit-Vector Lowering

Status: accepted (first slice implemented 2026-06-14)
Date: 2026-06-14

## Context

Strings/sequences (QF_S) are the last entirely-unbuilt Z3/cvc5 theory in the
stack, and matter for program reasoning over text. A full string solver
(unbounded length, `str.++`/`substr`/`contains`/`replace`/regex, length–content
interaction) is a large subsystem. We want a *sound* first step that reuses the
bit-vector backend rather than a new IR sort and a from-scratch decision
procedure — mirroring how `EnumSort`/`RecordSort` (ADR-0008) and the FP helpers
(ADR-0023) introduced finite theories as BV lowerings.

## Decision

**Introduce a bounded-length string theory as a bit-vector lowering, with no new
IR sort (`axeyum-solver`'s `strings` module, `BoundedString`).** A string of at
most `max_len` bytes is a pair `(len, content)`: `len` a small bit-vector in
`0..=max_len`, `content` a `BitVec(max_len · 8)` with byte `i` at bits
`[8i, 8i+7]`. Only the first `len` bytes are significant; padding is ignored by
every operation (one denotation, many bit representations). `max_len ≤ 16` keeps
`content` within the 128-bit bit-vector cap.

Operations build bit-vector/Boolean formulas, so solving and model replay reuse
the sound bit-vector path unchanged:

- `str.len` → the length term;
- `str.=` → equal lengths ∧ (for each position `i < len`, equal bytes) — a bounded
  conjunction with `i < len` guards, so padding is ignored;
- `str.at` at a constant index → the byte (guarded by `i < len`, else 0);
- string literals → constant `len`/`content`.

This is the **bounded-model-checking fragment** of the string theory (the shape
CBMC/Kani use): queries whose strings fit `max_len` are decided soundly; the
bound is explicit.

## Evidence

- The enum/record (ADR-0008) and FP (ADR-0023) helpers already prove out
  "finite/bounded theory as BV lowering, no new sort, reuse the BV backend";
  bounded strings fit the same mold (a length plus a content vector).
- Tests (`tests/strings.rs`): literal equality/inequality (content and length),
  `str.len`/`str.at` on literals, a symbolic string equal to a literal (`sat`),
  a length+char constraint (`sat`), and a length/literal contradiction (`unsat`),
  all through the bit-vector dispatcher.

## Alternatives

- **First-class `Sort::String`/`Sort::Seq` + a native string solver.** The
  complete approach (unbounded length, sequence/automata reasoning); deferred —
  it is a large subsystem and the multi-crate `Sort` cascade. The bounded BV
  lowering lands a sound, useful slice now, exactly as bounded LIA/array
  elimination preceded their fuller procedures.
- **Fixed-length only.** Rejected as too weak — the `len` field (with padding
  ignored by guarded equality) gives genuine variable-length-up-to-bound
  reasoning for little extra cost.

## Consequences

- **Easier:** bounded text constraints (equality, length, indexed access,
  literals) are decided soundly today via the BV backend, with replayable models
  that decode to concrete strings.
- **Harder / next:** the shift-heavy operations — `str.++` (concat shifts the
  second operand by a symbolic length), `substr`, `contains`/`indexof`, `replace`,
  and `to_int`/`from_int` — plus regex, and ultimately unbounded strings via a
  first-class sequence sort and a native solver. `str.++`/`substr`/`contains`
  are the natural next slice (bounded, but needing symbolic-length barrel shifts).
  *(Update 2026-06-14: `str.++`, `prefixof`, `contains`, `suffixof`, `substr`
  (const + symbolic start), `indexof`, lexicographic `<`/`<=`, `take`/`drop`,
  equal-length `replace`, and `str.in_re` regex membership are now implemented.
  `in_re` builds a Thompson NFA — Empty/Char/Range/Concat/Union/Star — precomputes
  its epsilon closure, and simulates it symbolically over the bounded positions,
  so regex membership reuses the same sound BV path. `str.to_int` (decimal parse,
  Horner over the significant positions, returning `(valid, value)`) is also in.
  Remaining: `from_int`, general-length `replace`, `replace_all`, and the
  unbounded sort.)*
- **Revisited when:** a workload needs unbounded strings or the structural
  operations (then the next bounded slice, and eventually the first-class sort).
