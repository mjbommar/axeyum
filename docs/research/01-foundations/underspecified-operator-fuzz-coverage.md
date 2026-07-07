# Underspecified / Partial Operator — Fuzz Coverage Checklist

Status: living checklist
Last updated: 2026-07-07 (task #51, 11th review — GAP-Q1 closed: the first QF_SEQ
differential fuzz lands, `seq.nth` OOB UNDERSPEC confirmed sound `DISAGREE=0`; it
also surfaced a Z3 oracle gap, `seq.rev` unsupported → harness error-guard. Prior:
task #47 FP + RealDiv-0 GAPs; the FP signed-zero P0 fixed in task #50, see below)

## Purpose — make the Hard Rule enforceable

CLAUDE.md carries a Hard Rule:

> **Partial/underspecified operators carry a fuzz seed-class that generates the
> degenerate argument.** A wrong-unsat shipped (`a946f925`) because
> `div`/`mod`-by-**constant-zero** was folded to a fixed convention, and the
> differential fuzz that "passed" only ever emitted *variable* divisors — it
> structurally could not generate `(div x 0)`.

That paragraph is a policy. This file is its **enforced, per-operator checklist**:
every partial / underspecified / total-by-convention operator, its exact
semantics and evaluator convention, and the specific fuzz generator that
**deliberately** emits its degenerate shape. A new partial operator is not
"done" until it has a row here with a `✓` (or an explicitly tracked `GAP`).

See also
[bv-semantics-and-partial-operations.md](bv-semantics-and-partial-operations.md)
for the BV totality conventions this table references.

## Classification key

- **UNDERSPEC** — SMT-LIB leaves the result *any total value* (`int div/mod`-by-0,
  `seq.nth` OOB, `fp.min/max` opposite-sign zero, `fp.to_ubv` of NaN…). The
  dangerous class: the value must be modeled **free** (never folded to a
  convention that could force a wrong `unsat`), `sat` must be **replay-gated**,
  and a differential-vs-oracle fuzz must emit the degenerate shape so a stray
  constraint on the free value is caught.
- **TOTAL-BY-DEF** — SMT-LIB (or the cvc5/IEEE convention we adopt verbatim)
  pins a **fixed** value (`bvudiv`-by-0 = all-ones, `pow2(x<0)` = 0,
  `str.at` OOB = ""). The fuzz must emit the degenerate shape to **confirm**
  axeyum matches the convention the oracle also uses.
- **DECLINES** — axeyum refuses to fold (returns `Unknown` / `None` / a fresh
  unconstrained value) rather than commit a value. Sound by construction; the
  fuzz confirms it never commits a *wrong* value.
- **ERROR** — a non-representable input in the `i128`/rational reference range
  yields a graceful `ArithmeticOverflow`/`Unsupported` → a dependent `sat`
  degrades to `Unknown`. Never a wrong verdict.

The `a946f925` failure mode is specifically: an UNDERSPEC or TOTAL-BY-DEF
operator whose **constant** degenerate argument routes through a **separate
folding branch** the fuzz cannot reach because it only emits the *variable* form.
Rows below flag those separate branches explicitly.

## Coverage table

Citations: `eval.rs` = `crates/axeyum-ir/src/eval.rs`; `parse.rs` =
`crates/axeyum-smtlib/src/parse.rs`; `lib.rs` (FP) = `crates/axeyum-fp/src/lib.rs`.
Fuzz files are under `crates/axeyum-solver/tests/`.

### Integer (LIA/NIA)

| Operator | Degenerate input | Class | Convention (cite) | Fuzz emits degenerate shape | Status |
|---|---|---|---|---|---|
| `div` | divisor `0`, **const** | UNDERSPEC | `div a 0 = 0` (eval.rs:760) — separate const-0 fold branch (`eliminate_int_divmod`) | `qf_nia_divmod_const_differential_fuzz` forces ≥1 const-zero divisor per instance | ✓ (#40) |
| `div` | divisor `0`, var | UNDERSPEC | congruent free value | `qf_nia_divmod_var_differential_fuzz` | ✓ |
| `mod` | divisor `0` (const+var) | UNDERSPEC | `mod a 0 = a` (eval.rs:772) | same two divmod fuzzes | ✓ (#40) |
| `int.pow2` | exponent `< 0` | TOTAL-BY-DEF | `pow2(x<0) = 0` (cvc5) (eval.rs:789) | `qf_nia_pow2_differential_fuzz` seeds negative lower bounds + the 0 boundary | ✓ (#41) |
| `abs`,`-`,`+`,`*` | `i128::MIN` / overflow | ERROR | `ArithmeticOverflow` (eval.rs:748,779) | n/a (graceful → Unknown) | ✓ by-design |

### Real (LRA/NRA)

| Operator | Degenerate input | Class | Convention (cite) | Fuzz emits degenerate shape | Status |
|---|---|---|---|---|---|
| `/` (`RealDiv`) | divisor `0`, **const** | UNDERSPEC | free congruent value (eval.rs:311,859) — separate const-fold branch | `qf_lra_differential_fuzz` const-`0` divisor seed-class + `seed_realdiv_const_zero_*` | ✓ (#47) |
| `/` (`RealDiv`) | divisor var pinned `0` | UNDERSPEC | NRA purifies `x/y` via `r·y=x` (`eliminate_real_div`) | `nra_differential_fuzz` var divisor + `seed_nra_realdiv_symbolic_divisor_pinned_zero`; LRA `seed_realdiv_symbolic_divisor_pinned_zero` | ✓ (#47) |

### Bit-vector (QF_BV)

All BV totality corners are TOTAL-BY-DEF and **shared verbatim with Z3** via a
uniform bit-blast circuit (no per-value branch): the SAT search explores a
`0` divisor / over-shift as part of model search, so the `bv_differential_fuzz`
differential is not blind the way the *int const-0 fold* was. The remaining
nuance is the **constant-fold rewrite** (`BV_CONST_FOLD`, canonical.rs) which
folds `bvudiv <const> <const 0>` through the (total) ground evaluator.

| Operator | Degenerate input | Class | Convention (cite) | Fuzz emits degenerate shape | Status |
|---|---|---|---|---|---|
| `bvudiv` | divisor `0` | TOTAL-BY-DEF | all-ones (eval.rs:533) | `bv_differential_fuzz` (incidental at narrow widths; SAT explores var=0) | ✓ / see GAP-BV1 |
| `bvurem` | divisor `0` | TOTAL-BY-DEF | dividend (eval.rs:534) | as above | ✓ / GAP-BV1 |
| `bvsdiv` | `0` / `MIN÷-1` | TOTAL-BY-DEF | ∓1 / wrapped (eval.rs:535) | as above | ✓ / GAP-BV1 |
| `bvsrem` | `0` / `MIN%-1` | TOTAL-BY-DEF | dividend / 0 (eval.rs:544) | as above | ✓ / GAP-BV1 |
| `bvsmod` | divisor `0` | TOTAL-BY-DEF | dividend (eval.rs:552) | as above | ✓ / GAP-BV1 |
| `bvshl`,`bvlshr` | shift `≥ width` | TOTAL-BY-DEF | `0` (eval.rs:569,579) | as above | ✓ / GAP-BV1 |
| `bvashr` | shift `≥ width` | TOTAL-BY-DEF | all sign bits (eval.rs:586) | as above | ✓ / GAP-BV1 |
| `bv2nat` | value `> i128::MAX` | ERROR | `ArithmeticOverflow` (eval.rs:717) | n/a | ✓ by-design |

**GAP-BV1**: the fuzz relies on *incidental* constant zeros (frequent at width
1/4, rare at 32) rather than a **deliberate** const-0-divisor / const-over-shift
seed-class, and does not force the `BV_CONST_FOLD` path on `bvudiv <c> <0>`.
Low-risk (total-by-def, oracle-shared, replay-checked) but the letter of the
Hard Rule wants a deliberate seed. Tracked, not yet closed.

### String (QF_S) — lowered at parse time to a packed-BV byte model (ADR-0029)

These high-level ops are **not** IR `Op` variants; their conventions live in the
`parse.rs` lowering helpers, then bit-blast. Fuzzed by `string_differential_fuzz`
(SMT-LIB text vs the system Z3 binary's full `UnicodeStrings` theory). `str.at`
and `str.from_int` carry the `a946f925` shape: a **constant** argument routes
through a *separate* folding branch (`string_at_const`, `string_from_int_const`).

| Operator | Degenerate input | Class | Convention (cite) | Fuzz emits degenerate shape | Status |
|---|---|---|---|---|---|
| `str.at` | index `< 0` / `≥ len` (const+var) | TOTAL-BY-DEF | "" (parse.rs:9145; const branch `string_at_const` 5118) | `string_differential_fuzz` idx=`gen_int_expr` reaches `-1..`; const idx via `IntConst` arm | ✓ |
| `str.substr` | OOB/neg `off`/`n` | TOTAL-BY-DEF | "" / clamped (parse.rs:9162) | off,len = `gen_int_expr` (reaches negative) | ✓ |
| `str.indexof` | start `< 0` | TOTAL-BY-DEF | `-1` (parse.rs:9197) | start = `rng.in_range(-2, 3)` (deliberate negatives) | ✓ (#42) |
| `str.to_code` | empty / multi-char | TOTAL-BY-DEF | `-1` (parse.rs:5635) | arg literal len `0..=3` (empty & multi) | ✓ |
| `str.to_int` | non-numeric | TOTAL-BY-DEF | `-1` (parse.rs:5700) | `ALPHABET="ab012"` gives `"ab"` | ✓ |
| `str.to_int` | signed / interior non-digit `"-5"` | TOTAL-BY-DEF | `-1` (parse.rs:5700) | `gen_signed_numeric_literal` (`-`/`+`/`1-2`/`5a`) | ✓ (#42) |
| `str.from_int` | negative int | TOTAL-BY-DEF | "" (parse.rs:9280; const branch `string_from_int_const` 5823) | arg = `gen_int_expr` reaches `-1` | ✓ |
| `str.replace` | empty needle | TOTAL-BY-DEF | prepend `b` (parse.rs:9179) | needle=`gen_literal` (can be "") | ✓ |
| `str.replace_all` | empty needle / ground | TOTAL-BY-DEF | identity / all-occ (parse.rs:9211) | `str.replace_all` ground arm, needle can be "" | ✓ (#42) |
| `str.from_code` | code point `< 0` | TOTAL-BY-DEF | "" (parse.rs:5657) | `gen_sound_codepoint` includes `-2,-1` | ✓ (#42) |
| `str.from_code` | code point `128..=255` | TOTAL-BY-DEF | **WRONG** — folds to "" | `from_code_out_of_range_p0_repro` (`#[ignore]`, failing) | **P0 / GAP-S1** |

### Sequence (Seq) — packed-BV, parse-lowered (ADR-0029/0051)

Fuzzed by `seq_differential_fuzz` (SMT-LIB text vs the system Z3 binary's `Seq`
theory under `(set-logic ALL)`), over `(Seq Bool)`, `(Seq (_ BitVec 4))`, and
small `(Seq Int)` (the exactly/safely representable element sorts — `(_ BitVec 8)`
is reserved for `String`, and out-of-range `Int` element literals decline, so the
differential carries no modeling-difference false positives). The generator plants
the UNDERSPEC `seq.nth` OOB shapes (negative / `≥ len` / empty-sequence indices,
biased) and exercises **both** verdicts (560 jointly-decided, 403 sat / 157 unsat,
`DISAGREE=0`).

| Operator | Degenerate input | Class | Convention (cite) | Fuzz emits degenerate shape | Status |
|---|---|---|---|---|---|
| `seq.nth` | index OOB | UNDERSPEC | fresh free value + eager congruence (parse.rs:8104; `seq_nth_oob_value` 8090) | `seq_differential_fuzz::seed_seq_nth_oob_is_free_not_folded` (neg/≥len/empty idx; `nth != 0` SAT proves no zero-fold) + the sweep | ✓ (#51) |
| `seq.extract` | OOB start/len | TOTAL-BY-DEF | clamp/empty (parse.rs:7893) | `seq_differential_fuzz::seed_seq_extract_oob_is_empty` + Family D | ✓ (#51) |
| `seq.at` | OOB | TOTAL-BY-DEF | empty seq (parse.rs:8154) | `seq_differential_fuzz::seed_seq_at_oob_is_empty` + Family D | ✓ (#51) |
| `seq.len`,`seq.++`,`seq.unit`,`seq.empty` | — | total | — | `normalize_denotation_fuzz` (axeyum-strings) + `seq_differential_fuzz` (length/concat facts) | ✓ (total, not partial) |
| `seq.rev` | — | total | involution (parse.rs:8209) | **not adjudicable** — Z3 4.13.3 lacks `seq.rev` (see the harness note) | n/a (oracle gap) |

**Bounded-model soundness (the seq wrong-unsat guard).** The packed layout bounds
each sequence's length (`SEQ_LEN_SOFT_CAP`) and, for `(Seq Int)`, the element
width. axeyum's unbounded length abstraction (P2.7 A.2) downgrades a bounded
`unsat` to `unknown` whenever the encoding bound could have caused it (an over-cap
`(= (seq.len s) 12)` decides `unknown`, never a wrong `unsat`). So axeyum is
*incomplete* on many sequence unsats (they SKIP), but the fuzz confirms it never
emits a **wrong** verdict — including that a *free* OOB `seq.nth` value cannot
rescue an independent length contradiction
(`seed_seq_nth_oob_does_not_rescue_length_contradiction`).

**Harness note (Z3 oracle gap, task #51).** Z3 4.13.3 does **not** implement
`seq.rev`: it emits `(error … unknown constant seq.rev)` and then answers
`check-sat` for the *remaining* (weaker) assertion stack — a bogus verdict that
manufactured a false `WRONG-UNSAT` on the first run (axeyum's `unsat` was in fact
correct: `rev(rev(unit)) = unit`, so `not (= …)` is unsat). The fuzz's `z3_decide`
now captures **both** streams and treats any `(error …)` as a hard SKIP, and the
generator omits `seq.rev`. This is a real defensive lesson: an oracle that drops an
unsupported command silently answers a different formula.

### Array / Datatype

| Operator | Degenerate input | Class | Convention (cite) | Fuzz emits degenerate shape | Status |
|---|---|---|---|---|---|
| `select` | unwritten index | TOTAL-BY-DEF | well-founded default (0 for BV) (eval.rs:664,139) | `abv_differential_fuzz` (reads of unwritten indices are the norm) | ✓ |
| `dt.select` | wrong constructor | TOTAL-BY-DEF | well-founded default (eval.rs:337); uninhabited field → error | `qf_dt_differential_fuzz` | ✓ |

### Floating-point (QF_FP) — term-builders/bit-blasters, not `apply`

FP arithmetic ops are **not** IR `Op` variants (only `FpFromBits` is); they are
built in `axeyum-fp` and bit-blast. The IEEE corners (`fp.div`-by-0 = ±∞,
`fp.sqrt` of `<0` = NaN, `fp.rem`-by-0 = NaN) are TOTAL-BY-DEF; the underspecified
ones (`fp.min`/`fp.max` opposite-sign-zero sign) are the genuine risk axis. The
differential fuzz is `fp_differential_fuzz` (SMT-LIB text vs the system Z3 binary
`4.13.3`'s full `FloatingPoint` theory), with explicit `seed_*` degenerate
witnesses. It found a **P0** (see below).

| Operator | Degenerate input | Class | Convention (cite) | Fuzz emits degenerate shape | Status |
|---|---|---|---|---|---|
| `fp.div` | `0/0`,`∞/∞`,`x/0` | TOTAL-BY-DEF | NaN / ±∞ (lib.rs:1267) | `fp_differential_fuzz` (div-by-`±0` seed bias) + `seed_div_by_zero_infinities`, `seed_div_zero_over_zero_and_inf_over_inf_is_nan` | ✓ (#47) |
| `fp.sqrt` | `x<0` / NaN | TOTAL-BY-DEF | NaN (lib.rs:982) | `seed_sqrt_negative_is_nan` (+ sweep) | ✓ (#47) |
| `fp.rem` | `y=0` / `x=∞` | TOTAL-BY-DEF | NaN (lib.rs:1751) | `seed_rem_zero_divisor_is_nan` (+ sweep) | ✓ (#47) |
| `fp.min`/`fp.max` | opposite-sign zeros `+0`/`-0` | **UNDERSPEC** | fresh free sign bit (lib.rs:3286) | `seed_min/max_opposite_sign_zero_free_both_ways` (observed via `1/min(±0)`∈{±oo}; BOTH signs SAT, no wrong-unsat) | ✓ (#47) |
| `fp.isNegative`/`fp.isPositive` | signed zeros `-0`/`+0` | edge (sign-bit) | sign-bit based, excl. NaN only (`-0` neg, `+0` pos; lib.rs:359,368) | `signed_zero_sign_predicates_agree` + the sweep (predicates re-enabled) | ✓ (#50, was GAP-F2 P0) |
| `fp.to_ubv`/`to_sbv` | NaN/∞/OOB/neg | UNDERSPEC → DECLINES | `None` / fresh BV (lib.rs:2886,3041) | `seed_fp_to_int_real_out_of_domain_is_free` | ✓ (#47) |
| `fp.to_real` | NaN/∞ | UNDERSPEC → DECLINES | `None` (lib.rs:2823) | `seed_fp_to_int_real_out_of_domain_is_free` (axeyum declines → sound skip) | ✓ (#47) |

## P0 finding (task #47) — FP signed-zero sign predicates — ✅ FIXED (task #50)

> **FIXED (task #50):** `axeyum_fp::is_negative`/`is_positive` are now sign-bit
> based (`sign_bit ∧ ¬isNaN`), so `-0` is negative and `+0` is positive, matching
> Z3/cvc5. An internal `is_strictly_negative` (sign ∧ ¬nan ∧ ¬zero) preserves the
> `sqrt(-0)=-0` path (lib.rs:979). The `fp.rs::sign_predicates` unit test was
> corrected, the reproducer un-ignored (`signed_zero_sign_predicates_agree`, now
> green), and the two predicates are back in the fuzz generator menu at DISAGREE=0.
> The finding below is retained as the record of the bug.

**GAP-F2 / P0 (FIXED) — `fp.isNegative(-0)` and `fp.isPositive(+0)` were wrong verdicts.**
The SMT-LIB `FloatingPoint` theory (confirmed against **both** Z3 4.13.3 and
cvc5) makes the sign bit decisive for these predicates: `-0` **is** negative and
`+0` **is** positive. axeyum instead treats *both* signed zeros as neither
positive nor negative (`is_negative(-0) = false`, `is_positive(+0) = false` — the
convention is even encoded in `crates/axeyum-solver/tests/fp.rs::sign_predicates`).
End-to-end through `solve_smtlib` this is a **wrong-UNSAT** (the worst class) on
the affirmative forms and a wrong-SAT on their negations:

| script (`QF_FP`) | axeyum | Z3 / cvc5 |
|---|---|---|
| `(assert (fp.isNegative (_ -zero 8 24)))`       | **unsat** | sat   |
| `(assert (not (fp.isNegative (_ -zero 8 24))))` | **sat**   | unsat |
| `(assert (fp.isPositive (_ +zero 8 24)))`       | **unsat** | sat   |
| `(assert (not (fp.isPositive (_ +zero 8 24))))` | **sat**   | unsat |

`fp.isNegative(+0)` and `fp.isPositive(-0)` are correct (both false), so only the
same-sign-as-the-zero pairing is wrong. Reproducer (failing, `#[ignore]`d):
`crates/axeyum-solver/tests/fp_differential_fuzz.rs::p0_signed_zero_sign_predicate_repro`.
The random FP sweep holds `fp.isNegative`/`fp.isPositive` out of its classifier
menu until this is fixed (they would keep it red and mask the otherwise-clean FP
surface); everything else is fuzzed `DISAGREE=0` (598/598 jointly decided, both
verdicts). **Fix (an `axeyum-fp` semantics change, out of scope for this
fuzz-closure slice):** `is_negative(x) = sign_bit(x) ∧ ¬isNaN(x)`,
`is_positive(x) = ¬sign_bit(x) ∧ ¬isNaN(x)` (so `±0` are covered), then flip the
`fp.rs::sign_predicates` expectations and re-run FP + carcara + fpa2bv gates.
Report, do not paper over.

## P0 finding (task #42) — string `str.from_code`

**GAP-S1 / P0 — `str.from_code` of a code point in `128..=255` is a wrong-sat.**
axeyum's byte string model represents characters as bytes `0..=255`, and
`str.to_code` of a byte-`i` string is exactly `i` for all `0..=255`
(`bv2nat`, parse.rs:5641). But `string_from_code` (parse.rs:5657) folds every
`i > 127` to the empty string. So, confirmed differentially vs Z3 4.13.3:

```
(set-logic QF_S)
(assert (= (str.from_code 200) ""))
(check-sat)
```

axeyum → **sat**; Z3 (and SMT-LIB `UnicodeStrings`) → **unsat** (`str.from_code
200` is the non-empty length-1 character U+00C8). The model even
self-contradicts: `(= (str.to_code (str.from_code 200)) 200)` is a theorem yet
axeyum makes `str.from_code 200 = ""`. Reproducer:
`crates/axeyum-solver/tests/string_differential_fuzz.rs::from_code_out_of_range_p0_repro`
(`#[ignore]`d, failing until fixed). **Fix (a parser change, out of scope for
this fuzz-coverage slice):** widen the sound byte range in `string_from_code` to
`0..=255` (byte = `i`), or DECLINE `128..=255` to `Unknown` rather than commit
`""`. Report, do not paper over.

## Tracked gaps (documented > silent blind spot)

- ~~**GAP-R1**~~ — **CLOSED (#47)**. `qf_lra_differential_fuzz` now emits a `/`
  seed-class biased to a constant-`0` divisor (+ a variable divisor pinnable to
  0) and explicit `seed_realdiv_*` congruence witnesses; the NRA purification
  (`r·y=x`) path is covered by the existing variable-divisor sweep plus
  `seed_nra_realdiv_*`. All `DISAGREE=0` — RealDiv-by-0 is a sound free congruent
  value on both the LRA and NRA routes.
- **GAP-F2** — **P0, open** (see the FP P0 finding above): `fp.isNegative(-0)` /
  `fp.isPositive(+0)` disagree with SMT-LIB/Z3/cvc5 (a wrong-unsat). Held out of
  the FP random generator; pinned by an `#[ignore]`d repro. Needs a dedicated
  `axeyum-fp` semantics fix slice.
- **GAP-BV1** — BV div/rem/shift lack a *deliberate* const-0-divisor /
  const-over-shift seed-class and don't force `BV_CONST_FOLD` on `bvudiv <c> <0>`.
  Low-risk (total-by-def, oracle-shared, replay-checked).
- ~~**GAP-Q1**~~ — **CLOSED (#51)**. `seq_differential_fuzz` now emits the
  UNDERSPEC `seq.nth` OOB shapes (negative / `≥ len` / empty-sequence indices,
  biased) plus `seq.extract`/`seq.at` OOB and length/concat/order facts, over
  `(Seq Bool)`/`(Seq (_ BitVec 4))`/small `(Seq Int)`. `DISAGREE=0` on 560
  jointly-decided scripts (403 sat / 157 unsat, both verdicts). The OOB value is a
  sound **free** value on axeyum (`nth != 0` is SAT — no zero-fold), and the
  bounded-`unsat`→`unknown` downgrade means no over-cap wrong-unsat. The one
  non-adjudicable operator is `seq.rev` (Z3 4.13.3 does not implement it; the
  harness now SKIPs any Z3 `(error …)` — see the sequence-section harness note).
- ~~**GAP-F1**~~ — **CLOSED (#47)**. `fp_differential_fuzz` (SMT-LIB text vs the
  system Z3 binary) now fuzzes the FP fragment with explicit degenerate seeds:
  `fp.div`/`fp.rem`/`fp.sqrt` edges, NaN/±∞ propagation, and the UNDERSPEC
  `fp.min`/`fp.max` opposite-sign-zero free sign (observed through `1/min(±0)` ∈
  {±oo}: BOTH signs SAT, no wrong-unsat). `DISAGREE=0` on 598/598 jointly-decided
  scripts (both verdicts). The one exception is the signed-zero **sign
  predicates**, now split out as the **GAP-F2 P0** above.

## How to extend (for the next partial operator)

1. Classify it (UNDERSPEC / TOTAL-BY-DEF / DECLINES / ERROR) against the
   authoritative reference (SMT-LIB, cvc5 `evaluator.cpp`, IEEE 754).
2. If it has a **separate constant-folding branch**, the fuzz MUST emit the
   **constant** degenerate argument, not only the variable form (the `a946f925`
   lesson).
3. Add / extend a differential-vs-oracle fuzz whose generator **deliberately**
   constructs the degenerate shape, and assert both `sat` and `unsat` are
   exercised on it at `DISAGREE=0`.
4. Add the row here with the `file:test` that emits the shape. A row without a
   `✓` is a standing work item.
