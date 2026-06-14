# ADR-0026: First-Class Floating-Point Sort in the IR

Status: accepted (implemented 2026-06-14)
Date: 2026-06-14

## Context

ADR-0023 introduced IEEE 754 floating point as **bit-vector lowering helpers
with no new IR sort**: a value of format `(eb, sb)` is a `BitVec(eb + sb)`, and
the format is a *caller convention*, not sort-checked. That was the right first
move — predicates, comparisons, classification, and (later) rounded arithmetic
all decide today on the existing sound, replayed BV path. ADR-0023 explicitly
named the upgrade path: "a first-class `Sort::Float` is the upgrade path if that
looseness bites."

It now bites, in exactly one place: **conversions**. The SMT-LIB conversion
operator `((_ to_fp eb sb) RM x)` is overloaded by the *sort* of `x`:

- `x : (_ FloatingPoint eb' sb')` → FP→FP reformat (e.g. `double`→`float`);
- `x : Real` → real→FP;
- `x : (_ BitVec m)` → **signed** bit-vector→FP.

The real-source form is already wired (ADR-0023 follow-up: `round_rational_to_format`,
dyadic-exact, sound). But because our lowering collapses both `FloatingPoint`
and `BitVec` to the single `BitVec` sort, the FP-source and signed-BV-source
forms are *indistinguishable* — same surface syntax, same operand sort. The
front-end currently rejects the bit-vector-operand form with a precise
`Unsupported` error rather than guess (a wrong guess is a wrong `sat`/`unsat`).

FP→FP reformatting is common in real QF_FP/QF_BVFP benchmarks and in the
program-verification north star (mixed `float`/`double` code), so the gap is
worth closing — and the only sound way to close it is to carry the format at the
sort level. The same sort-level typing also catches "a `float32` used where an
arbitrary 32-bit vector was meant" bugs that the current convention cannot.

This closes the deferral recorded in ADR-0023 ("Revisited when … sort-level FP
typing is wanted (then the `Sort::Float` ADR)").

## Decision

**Add a first-class `Sort::Float` to `axeyum-ir`, carrying the format inline, and
treat it as structurally a `BitVec(eb + sb)` for every lowering, evaluation, and
solving purpose — so FP keeps reusing the sound, replayed BV path while gaining a
distinct sort that disambiguates conversions and enables sort-level FP typing.**

Concretely:

- **Inline format, no circular dependency.** `FloatFormat` lives in `axeyum-fp`,
  which depends on `axeyum-ir`; `Sort` cannot reference it without a dependency
  cycle. So the IR stores the format *inline*, mirroring `Sort::Array { index,
  element }`:

  ```rust
  Sort::Float { exp: u32, sig: u32 }   // exp = exponent bits, sig = total
                                       // significand bits incl. the hidden bit
  ```

  `Sort` stays `Copy` (two `u32`s). `axeyum-fp::FloatFormat` gains
  `From<FloatFormat> for Sort` and a `TryFrom<Sort>` (or `Sort::float_format()`)
  so the builders translate at their boundary. `width()` = `exp + sig`.

- **Value stays `Value::Bv`.** A floating-point value *is* its bit pattern; the
  ground evaluator already evaluates every FP builder to a `BitVec`. The
  evaluator and model lifting keep producing `Value::Bv { width: exp + sig, … }`
  for a `Sort::Float` term. No new `Value` variant, so `sat` replay is unchanged
  (an FP model is a bit-vector model, replayed against the original term). This
  keeps the "every `sat` is checkable by ground evaluation" invariant intact.

- **Structural BV everywhere downstream.** `axeyum-bv` lowering, `axeyum-cnf`,
  the SAT-BV backend, `axeyum-bv`'s width queries, and `Sort::bv_width()` treat
  `Sort::Float { exp, sig }` as `BitVec(exp + sig)`. A new `Sort::lowered_width()`
  (returns the bit width for both `BitVec` and `Float`) centralizes this so the
  lowering sites do not each re-derive it.

- **Disambiguated conversions.** With the sort in hand, the front-end resolves
  `((_ to_fp eb sb) RM x)` by `arena.sort_of(x)`: `Float{..}` → `axeyum_fp::to_fp`
  (FP→FP, already implemented and validated), `Real` → `round_rational_to_format`,
  `BitVec(m)` → `axeyum_fp::sbv_to_fp` (signed-BV→FP). `((_ to_fp_unsigned …))`
  stays BitVec→FP. `fp.to_sbv/to_ubv` produce `BitVec`; `fp.to_real` produces
  `Real`. The ambiguity is gone because the operand's sort is now distinct.

- **Migration is staged and behavior-preserving.** The cascade is mechanical
  (~20 files with exhaustive `Sort` matches). Each stage compiles and is green:
  1. Add the variant + `lowered_width()`/format conversions; make every
     exhaustive `match` treat `Float{exp,sig}` exactly as `BitVec(exp+sig)`
     (most arms fold into the existing BV arm). No producer yet → dead but sound.
  2. Switch the SMT-LIB front-end: `Float16/32/64/128` and `(_ FloatingPoint eb
     sb)` parse to `Sort::Float{..}` (not `BitVec`); the `fp` literal and every
     FP builder return `Sort::Float`-typed terms; the writer round-trips them.
  3. Wire the FP-source and signed-BV-source `to_fp` overloads now that sorts
     distinguish them; drop the `Unsupported` rejection.

  Determinism, `unsafe`-free, and no-C-dependency rules are unaffected (pure data
  on an existing path).

## Evidence

- ADR-0022 already added a first-class sort (`Sort::Datatype`) through the same
  ~20-file exhaustive-match cascade; the pattern and its cost are known and
  manageable, and `Sort` remained `Copy` by storing recursion behind an id —
  here the analogue is storing the format inline as two `u32`s.
- ADR-0023 anticipated this exact upgrade and deliberately left the BV-lowering
  helpers shaped so the value representation does not change (`Value::Bv`), which
  is what makes this migration behavior-preserving rather than a re-implementation.
- The conversions that *don't* need the sort (real→FP dyadic, uBV→FP, FP→sBV/uBV)
  are already implemented and tested; only the sort-ambiguous overloads remain,
  isolating the value of this change to a well-understood surface.
- Z3/cvc5 carry FP as a first-class sort with the format in the sort; matching
  that is what lets standard QF_FP/QF_BVFP benchmarks parse without heuristics.

## Alternatives

- **Parser-local shadow typing.** Track which `TermId`s are "FP-typed" in a
  side table during parsing to disambiguate `to_fp`. Rejected: it is a silent
  architectural type system that is fragile across `let`, `ite`, and function
  results, leaks into every term-producing path, and violates "decisions are not
  made silently in code." The sort *is* the right place for this information.
- **Width heuristic.** Treat a 64-bit `to_fp` operand as F64, 32-bit as F32.
  Rejected as unsound: a 64-bit operand can equally be a signed integer; guessing
  risks a wrong `sat`/`unsat`, violating the core invariant.
- **Keep deferring.** Rejected: FP→FP reformatting is common enough that the gap
  is real, and the deferral has no cheaper resolution than the sort.
- **A new `Value::Float`.** Rejected: an FP value is exactly its bits; a separate
  value type would duplicate the BV model/replay machinery for no semantic gain
  and would complicate the "sat replays as a BV model" guarantee.

## Implementation note (as built)

The realized bridge uses a **single** new op, `Op::FpFromBits { exp, sig }`
(`BitVec(exp+sig) → Float`, identity on bits, lowered as identity), plus
leniency in `expect_bv`/`FloatFormat::check` so a `Float` term is accepted as its
bits. The FP formula builders are left untouched (they assume bit-vector
operands and freely mix with bit-vector constants): the SMT-LIB front-end
**unwraps** each `Float` operand to its bits right before a builder call — peeling
the `FpFromBits` wrapper when present (preserving `BvConst`s for the
constant-folding conversions) or `extract`-ing a symbolic float — and **re-stamps**
every FP-valued result with `fp_from_bits`. So `Float` is effectively a
parser-level tag that survives between ops and is unwrapped at each builder
boundary; no reverse `FpToBits` op was needed.

## Consequences

- **Easier:** all `(_ to_fp …)` overloads (FP→FP, real→FP, signed-BV→FP) parse
  and decide; FP operands are sort-checked, catching format/width mismatches that
  the convention silently accepted; QF_FP/QF_BVFP benchmarks ingest without
  conversion-shaped gaps.
- **Harder / cost:** a one-time ~20-file `Sort` cascade (staged, each stage
  green); every future exhaustive `Sort` match must handle `Float` (usually by
  delegating to the BV width via `lowered_width()`).
- **Unchanged:** solving and model replay (still the BV path with `Value::Bv`),
  determinism, the no-C-dependency and `unsafe`-free guarantees, and the existing
  validated FP builders (they only change the *sort* they stamp on results).
- **Revisited when:** FP arithmetic outgrows `MAX_BV_WIDTH = 128` (F64 `fp.fma`
  needs a 164-bit intermediate) — that is a separate `Value`/width decision,
  orthogonal to this sort change.
```
