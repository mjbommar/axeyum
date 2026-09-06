# Lane: s9-int-wide-parser — integer literals wider than `i128` reach the solver

<!-- plan-section: lane-status -->

**ADR-1702 slice 2 landed: the SMT-LIB front door admits an integer literal
outside `i128`, and every route that meets one declines with a named reason**
(`WIP`, s9-int-wide-parser, 2026-09-06, ADR-1702, ADR-0376). All 26 QF_UFLIA
files that carried EVM `uint256` bounds now parse and dispatch instead of being
refused at the parser. `TermNode::WideIntConst(WideInt)` and
`Value::WideInt(WideInt)` are sibling variants of the `i128` ones, exactly as
`WideBvConst`/`WideBv` already split at 128 bits.

**The parity plan's "+6 measured against cvc5" for row S9 is not supported, and
the measurement that says so was run before any code was written.** ADR-0376
deferred this widening in August on an ablation, not on cost: with every
out-of-range literal removed from the problem, the six files cvc5 decides were
*still* `unknown`, because the binding constraint is the decision procedure
(`MAX_INT_BLAST_WIDTH = 64`, and a measured magnitude cliff between `2^24` and
`2^32`) and not the literal type. That is a claim about a tree a month old, so
both arms were re-run on today's HEAD: rescaling every wide numeral to a
distinct `2^60 + i` gives **6/6 `unknown`**, and deleting every assert that
mentions one (50–1,314 per file, matching ADR-0376's counts exactly) gives
**6/6 `unknown`**. The +6 is the count cvc5 decides, not a measured axeyum gain.

**The design deviates from the brief, deliberately, toward the one ADR-0376
already recorded.** The brief asked for `Value::Int` to take the shape ADR-1702
gave `Rational` — a payload with a fast and a promoted path. That move worked
for `Rational` because it is a `struct` consumed by value in ~5,500 places, so
keeping the layout kept the consumers. `Value::Int` is an enum *variant*, and
the analogous "consumers stay correct by construction" move for a variant is a
SIBLING variant, not a payload change: changing the payload breaks all ~390
`Value::Int` and ~210 `IntConst` sites and, per ADR-0376, turns every
`arena.int_const(0)` on the hot LIA path into a heap allocation. With the
sibling the `i128` sites are stronger than "panic rather than truncate" — they
cannot observe a wide value at all.

**The hazard discipline is kept where it belongs.** `WideInt::to_i128` returns
`i128` and panics rather than truncating or saturating, the same contract
`WideUint::to_u128` and `Rational::numerator` carry; `Value::as_int` returns
`None` for a wide value. A `should_panic` test pins it, and the mutation control
is that replacing the panic with a wrapping or saturating cast kills exactly
that test.

**The real soundness hole this closes was a panic on user input in the
evaluator.** `int_bin`/`int_cmp` and eleven siblings read operands with
`as_int().expect("builder guaranteed Int operand")`, and `as_int` is `None` for
a wide value — so a parsed `2^256` literal would have panicked on the one path
every `sat` is replayed through. `eval` now takes a wide-integer detour
mirroring the wide-BV one beside it: an explicit operator list evaluates exactly
in `BigInt` and everything else declines with `IrError::Unsupported` before
reaching the `expect`. Narrow-by-narrow arithmetic is untouched, so
`i128::MAX + 1` still reports `ArithmeticOverflow` rather than silently
promoting — the lesson ADR-1702 learned from `axeyum-cas`, applied again.

**The audit was compile-driven, which is the point of the sibling design.**
Adding the two variants broke 62 `match` sites across 13 crates; the compiler
enumerated the audit instead of a grep guessing at it.

**Nothing has opted in, and `Features::has_wide_int` is where a route says so.**
`wide_int_admission` declines at the dispatch boundary with a named `unknown`.
It changes no verdict — every route already fails closed — but it changes cost
and explanation: without it a 15 MB Certora file walks the whole ladder before
every rung declines for the same reason. Opting the LIA route in is out of
scope for this slice and the ablation above says why: it would decide nothing
on this population, and `IntCollector::linearize` is shared by every LIA query,
so the regression risk is real and the measured gain is zero.

<!-- plan-section: landed-changes -->

| 2026-09-06 | `af8a1d550` | The census of the 26 QF_UFLIA files (largest literal's bit length, digit count, occurrence count, syntactic position), cross-checked against the real front door over the WHOLE 200-file population in both directions with zero difference; plus ADR-0376's two ablation arms re-run on today's HEAD, both reproducing 6/6 `unknown`. |
| 2026-09-06 | `c04442c28` | `TermNode::WideIntConst(WideInt)` and `Value::WideInt(WideInt)` with the canonicality invariant enforced by demoting constructors, `WideInt::to_i128` panicking rather than truncating, and evaluator/renderer/stats support. |
| 2026-09-06 | `f19800cdb` | The 62-site compile-driven audit: exact `BigInt` evaluation for the operators that have one and `IrError::Unsupported` for the rest, `IntBlastError::WideConstantOutOfRange`, and a decline at every other route boundary rather than a narrowing. |
