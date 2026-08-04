# ADR-0376: Integer literals wider than `i128` — measured non-cause, deferred IR widening

Status: deferred
Date: 2026-08-04

## Context

`TermNode::IntConst(i128)` (`crates/axeyum-ir/src/term.rs:361`) and
`Value::Int(i128)` (`crates/axeyum-ir/src/value.rs:37`) bound the modeled `Int`
range to `i128`. The SMT-LIB front door turns a wider numeral into a hard parse
failure at `crates/axeyum-smtlib/src/parse.rs:15719`:

```rust
let value = a.parse::<i128>().map_err(|_| {
    SmtError::Unsupported(format!("integer literal `{a}` exceeds the modeled `Int` range"))
})?;
```

The QF_UFLIA residual population contains Certora EVM benchmarks carrying
`uint256` bounds (`2^256`, `2^255`, `2^160`, …). Six of them are decided by the
reference solver and not by us, and the working hypothesis was that this parse
ceiling is what costs us those six files — motivating a bignum widening of the
IR's integer representation, mirroring what `WideUint` / `TermNode::WideBvConst`
did for bit-vectors wider than 128 bits.

The widening is the largest-blast-radius change available in the arithmetic
group: 184 `TermNode::IntConst` match sites and 361 `Value::Int` sites across
the workspace, and `IntConst` would lose `Copy`. That cost is only justified by
a measured payoff. This ADR records the measurement that was run before writing
any of it.

## Decision

**Do not widen `TermNode::IntConst` / `Value::Int` now. The `i128` literal
ceiling is real but is *not* the binding constraint on the six target files, so
the widening would deliver zero decided files at the cost of touching the core
IR everywhere.** The parse ceiling stays; the six files stay `unknown`; the
representation design below is recorded so the change can be made correctly
when a downstream constraint actually makes it pay.

## Evidence

All runs: `MEM_LIMIT_GB=8 timeout 29 ./scripts/mem-run.sh
target/release/examples/smtcomp_cli <file> --timeout-ms 24000`, sequential, on a
host with a concurrent certification sweep (`load average: 3.2-7.6`,
`up 22 days`, 2026-08-04 07:10-07:22).

**1. The parse ceiling is real, and sits exactly at `i128::MAX`.** A two-line
bisect on a synthetic file:

| literal | verdict |
|---|---|
| `12345` | `sat` |
| `170141183460469231731687303715884105727` (`i128::MAX`) | `sat` |
| `170141183460469231731687303715884105728` (`i128::MAX + 1`) | `unknown` |
| `2^256` | `unknown` |

So the diagnosis of the *mechanism* was correct: these files do fail at parse,
and they fail because of the `i128` width.

**2. The target population is 6, not 26.** Of the 107 QF_UFLIA files we do not
solve, **26** carry a literal above `i128::MAX`. All 26 are declared
`:status unknown`. The reference decides only **6** of them (5 `sat`, 1
`unsat`); it also fails on the other 20. Those 6 are the entire available prize:

```
sat    3106_1c933134166dbad31f79_41_QF_UFLIA.smt2
sat    44289_e5a2e5c780236919ee6a_18_QF_UFLIA.smt2
sat    63058_64ab9a7ef7b6c3492507_22_QF_UFLIA.smt2
unsat  63058_aa742630eef64f949de269382c1f9035_25_UFLIA.smt2
sat    65782_cd31513fdcd15701933b_7_QF_UFLIA.smt2
sat    72771_f9d228efc97cf1458e38_64_QF_UFLIA.smt2
```

(all under `.../QF_UFLIA/20230314-Jaroslav-Bendik-Certora/`). cvc5 confirms all
six at 114 ms - 11.4 s, so they are genuinely decidable.

**3. Removing the width problem does not decide any of them.** Three
independent ablations, each of which leaves a file with *no* literal above
`i128::MAX` — i.e. each simulates a perfect bignum IR or better:

| ablation | result on the 6 |
|---|---|
| every wide literal rescaled to `2^60 + i` | 6/6 `unknown` |
| every wide literal rescaled to `1000 + i` | 3/6 `unknown`, 3/6 `unsat` (over-constrained artifact, see below) |
| every assertion mentioning a wide literal **deleted** (50-1314 asserts each) | 6/6 `unknown` |

The third ablation is the decisive one: with every wide constant gone from the
problem entirely, the residual QF_UFLIA formula is *still* beyond our route on
all six files. No integer representation can recover a file whose
wide-constant-free residue we already cannot decide.

The `1000 + i` row is not a counterexample. Shrinking a `x < 2^256` type bound
to `x < 1000` makes the problem over-constrained, and the three `unsat` answers
there are answers to a strictly harder formula than the original — note that two
of them are files whose true status is `sat`. That row measures over-constraint,
not tractability.

**4. The magnitude cliff sits ~100 binary orders below `i128`.** Sweeping the
wide literals of `65782_cd31513fdcd15701933b_7` through powers of two:

| bound | `2^8` | `2^16` | `2^24` | `2^32` | `2^40` | `2^48` | `2^64` | `2^96` | `2^126` |
|---|---|---|---|---|---|---|---|---|---|
| verdict | `unsat` | `unsat` | `unsat` | `unknown` | `unknown` | `unknown` | `unknown` | `unknown` | `unknown` |

The route dies between `2^24` and `2^32`, while `i128` reaches `2^127`. The
mechanism is the bit-blasting integer route, not the literal type:
`MAX_INT_BLAST_WIDTH = 64` (`crates/axeyum-rewrite/src/int_blast.rs:30`) and the
width ladder declines above it at `crates/axeyum-solver/src/auto.rs:4446`
(`Some(w) if w <= axeyum_rewrite::MAX_INT_BLAST_WIDTH => w`). A `2^256` bound
needs `w = 257`; even a `2^60` bound needs `w = 61` plus product headroom. The
`i128` literal ceiling is roughly 63 binary orders *beyond* where the decision
procedure has already given up.

## Alternatives

**Widen `IntConst(i128)` to `IntConst(BigInt)` in place.** Rejected on cost and
on zero measured payoff. `num-bigint` is already an unconditional `axeyum-ir`
dependency (per ADR-0045), so there is no dependency or licensing obstacle — the
obstacle is that `IntConst` stops being `Copy`, breaking the `*value` deref at
all 184 match sites and the `i128`-typed helper signatures in
`crates/axeyum-ir/src/eval.rs` (`int_bin` at :1342, `int_cmp` at :1356), and
that every `arena.int_const(0)` / `int_const(1)` on the hot LIA path becomes a
heap allocation. ADR-0045 is explicit that bignum must not infect the core
`i128` `Rational`; this would do exactly that by the back door.

**Add `TermNode::WideIntConst(BigInt)` mirroring `WideBvConst`.** This is the
design that *should* be used when the widening is finally justified, and it is
recorded here so the next attempt does not re-derive it:

- **Representation: `num_bigint::BigInt`, not a hand-rolled limb type.**
  `WideUint` exists because bit-vectors need fixed-width *wrapping* semantics
  mod `2^width` plus a `width` field — semantics `BigInt` deliberately does not
  model. Mathematical integers are unbounded and exact, which is precisely
  `BigInt`. Mirroring `WideUint`'s hand-rolled limbs here would be
  reimplementing `BigInt` for no reason; the *structural* precedent
  (a second variant for the out-of-native-range case) is what to copy, not the
  payload type.
- **Canonical form (the interning-determinism requirement).** `TermNode` and
  `Value` derive `Hash`/`Eq` and are interned through a `HashMap<TermNode,
  TermId>` (`crates/axeyum-ir/src/arena.rs:43`, `:243`), so a value with two
  representations silently breaks structural sharing. The invariant is:
  *`WideIntConst(b)` is well-formed iff `b.to_i128().is_none()`* — every value
  representable in `i128` is `IntConst`, never `WideIntConst`. The arena
  constructor must normalize down (`int_const_big` demotes to `IntConst` when it
  fits), exactly as `bv_const` promotes up at `arena.rs:398-409`. `BigInt` is
  itself canonical (num-bigint normalizes sign+magnitude, so no `-0` and no
  leading-zero limbs), so with the demotion rule each integer has exactly one
  node. The test that matters is a round-trip: for a set of values straddling
  `i128::MIN`/`MAX`, interning the same value twice must yield the same
  `TermId`, and `i128::MAX as BigInt` must intern equal to `IntConst(i128::MAX)`.
- **Evaluator.** `Value::WideInt(BigInt)` with the same invariant; the
  `TermNode::IntConst(value) => ... *value` deref at `eval.rs:269` becomes a
  `.clone()`, as `WideBvConst` already does at `eval.rs:266`. Arithmetic on the
  widened type is checked *by construction* — `BigInt` cannot overflow — which
  preserves the existing contract at `eval.rs:468` that an out-of-range result
  is `IrError::ArithmeticOverflow`, never a wrapped wrong value. This matters
  because every `sat` replays through the evaluator against the original term.
- **Declining is sound.** Every consumer that does not understand
  `WideIntConst` must decline to `unknown`, never coerce it to `0` or skip it.
  Most of the 184 sites are `Option`-returning extractors whose wildcard arm
  already returns `None`; the ones needing an explicit audit are the
  distinctness checks (`incremental.rs:5897`, `abv.rs:1400`), which must return
  "not known distinct" rather than "equal".

## Consequences

- The six Certora files stay `unknown`, and the honest reason is recorded: our
  QF_UFLIA route cannot decide their wide-constant-free residue, so this is a
  *decision-procedure* gap, not a *representation* gap. Chasing it through the
  IR would have produced a large, risky, zero-yield diff.
- `docs/research/08-planning/foundational-dag.md:301` continues to state `Int`
  arithmetic over an `i128` reference; that row stays accurate and needs no
  edit.
- The parse-time error message at `parse.rs:15719` is accurate as written and is
  deliberately `Unsupported` (→ `unknown`), not `Syntax` (→ parse error), so
  these files already report the first-class `unknown` the hard rules require.
- **Revisit when, and only when,** the integer route stops being width-bound —
  i.e. when a non-blasting QF_LIA/QF_UFLIA path (bignum-capable simplex plus
  branch-and-bound, lifting the `MAX_INT_BLAST_WIDTH = 64` ceiling) can decide
  these formulas at `2^32`+ magnitudes. At that point the literal ceiling
  becomes the next binding constraint and the `WideIntConst` design above should
  be implemented as specified. Widening the IR before then optimizes a
  constraint that is 63 binary orders of magnitude from binding.
