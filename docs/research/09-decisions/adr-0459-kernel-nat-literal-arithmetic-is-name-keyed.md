# ADR-0459: Kernel `Nat` literal arithmetic is name-keyed, and the trust that buys

Index-summary: Literal `Nat` arithmetic in the trusted kernel, keyed on declaration name and type as Lean's kernel is
Status: accepted
Date: 2026-08-15

## Context

`axeyum-lean-kernel` had no reduction rule for binary `Nat` operations on
literals — only `Nat.succ` folding (`reduce_nat_succ`) and offset equality. That
was adequate for the hand-picked 40-declaration import corpus and is not adequate
for anything larger, because **`Char`, `UInt8/16/32/64`, `USize` and `Fin` are
`Nat` under bounds like `2^32` and `1114112`**, and reaching those by successor
steps is unbounded rather than slow.

Measured 2026-08-15 on official Lean 4.30.0 exports
(`docs/formalized-math-2026-08/diary-import-scale.md`):

- `Nat.Linear.Expr.denote_toPoly_go`, one declaration in `Init`, consumed 25 GB
  in under four minutes without producing a verdict, and is the single reason the
  96,591-declaration `Init`+`Std` stream cannot be censused in one pass;
- `Option.repr` and `Lean.Parser.Attr.extIff` each exhausted an 8 GB address
  space in 80–95 s.

With the rule, all three complete in 0.04–0.05 s.

The decision that has to be made explicitly is **not** whether to have the rule.
It is what the rule may key on, because it widens definitional equality inside
the trusted kernel and the honest answer involves a trust assumption this
repository has not previously taken.

## Decision

**Literal `Nat` arithmetic is keyed on the declaration's name and validated
shape, exactly as Lean's kernel keys it, and the residual trust — that an
environment declaring `Nat.add` really declares addition — is accepted, recorded
here, and pinned by a passing test rather than left implicit.**

`Kernel::reduce_nat_binop` is a port of `type_checker::reduce_nat`
(`references/lean4/src/kernel/type_checker.cpp:609`) for the fourteen
two-argument cases — `add sub mul div mod gcd pow land lor xor shiftLeft
shiftRight beq ble` — tried after `whnf_core` and before δ, with:

- arbitrary precision (`NatLit`'s `BigUint`), never a machine word;
- Lean's totality conventions verbatim: `x / 0 = 0`, `x % 0 = x`, truncated
  `sub`, `gcd 0 y = y`, `pow x 0 = 1`;
- Lean's `ReducePowMaxExp` bound of `1 << 24` on the `pow` exponent, reused as a
  `shiftLeft` bound that Lean does not impose. Bounding only ever *refuses* a
  reduction, so it is fail-closed relative to Lean.

`build_nat_binop_table` admits an operation only when the environment declares it
as a **`Definition`** (never an axiom, never an opaque), with **no universe
parameters**, and with **exactly** `Nat → Nat → Nat` or `Nat → Nat → Bool`; and
only in an environment whose `Bool` is Lean's — parameter-free, index-free,
non-recursive, in `Type`, constructors `[false, true]` in that order at indices 0
and 1, both nullary. Any of those failing empties the table and no arithmetic
fires at all.

Two mechanical constraints are part of the decision, not incidental:

- **The declared type is checked by walking the two `Pi` layers, not by comparing
  interned ids.** Binder names are part of an interned `Pi` node and the official
  export names `Nat.add`'s binders, so an id comparison against a locally built
  arrow never matches.
- **Names are looked up, never interned** (`Kernel::lookup_name_str`). Name ids
  are dense and assigned in insertion order and the lean4export writer emits them
  in that order, so a reduction that minted `Bool.true` while checking a
  declaration renumbers the entire subsequent export. This is not hypothetical:
  `axeyum_built_prelude_round_trips` failed on the first version of this rule.

## Evidence

- **Guard-by-guard controls.** Each clause was removed in turn and the suite
  re-run. Rule not installed → four positives fail. Type check off, kind check
  off, arity check off, `pow` bound off → each flips exactly one negative test.
  The two `Bool`-order clauses (constructor names, constructor indices) are
  **individually redundant and jointly load-bearing**: dropping either alone
  changes nothing, dropping both flips
  `a_bool_whose_constructors_are_in_the_wrong_order_disables_the_table`.
- **Differential against a real recursive definition.**
  `accelerated_addition_agrees_with_unaccelerated_recursion` declares
  `Trusted.add` with the *same value expression* as `Nat.add`; the acceleration
  is keyed on the name, so the copy reduces by ι alone and agreement is evidence
  rather than tautology.
- **Differential against official Lean.**
  `tests/real_lean_nat_arithmetic_crosscheck.rs` generates its obligations from
  this kernel's own `whnf` output for 24 argument pairs — both totality
  conventions, truncated `sub`, `gcd` with a zero, `pow 0 0`, values past `2^32`
  and `2^64` — and Lean 4.30.0 accepts all 24. Mutating one convention (`x % 0`
  from `x` to `0`) makes Lean reject, so the crosscheck discriminates. Registered
  in `scripts/check-lean-gate.sh`; floor raised 105 → 107.
- **Our reconstruction preludes are unaffected by mechanism.**
  `build_logic_prelude` declares `Bool` as `[true, false]`, which is not Lean's,
  so the table is refused for every prelude-built environment.
  `tc_tests::the_reconstruction_prelude_is_not_accelerated` asserts the
  constructor order, asserts the table is `None`, and checks the prelude's
  `Nat.add` still computes. The 119-theorem `nat` inventory and its empty axiom
  footprint therefore cannot move because of this rule.

## Alternatives rejected

- **Validate each operation against its own definition at bootstrap** (reduce
  `Nat.add 2 3` with the rule disabled and compare). This is the check that would
  retire the trust assumption, and it **cannot be made to work for the operations
  that need the rule most**: Lean's `Nat.div`, `Nat.mod` and `Nat.gcd` are
  well-founded recursions whose unaccelerated kernel reduction is stuck by
  construction — which is precisely why Lean's kernel accelerates them. A
  validation that silently disables `div`/`mod`/`gcd` would be worse than none,
  because it would look like a stronger guarantee while covering less.
- **Accelerate only `add`/`mul`/`beq`, where a body can be checked.** Leaves
  `Char`/`UInt`/`Fin` bounds — the actual blocker — unreduced, so it does not
  address the constraint at all.
- **Take the operation from a wire annotation rather than the name.** The
  lean4export 3.1.0 format carries no such annotation, and inventing one would
  move the trust from Lean's environment to our exporter's fidelity without
  reducing it.
- **Do nothing and accept that large exports do not import.** Rejected on the
  measurement: it is not a performance ceiling but an unbounded one, and it
  blocks the whole `Init`/`Std`/Mathlib surface rather than a corner of it.

## Consequences

- **Easier:** every official Lean export that computes with `Char`, `UInt*`,
  `USize` or `Fin` bounds becomes checkable. A 400-declaration random Mathlib
  sample now has **no Mathlib-specific root blocker** — every refusal is in
  Lean's `Init`/`Std` core.
- **Harder / newly explicit:** the trusted kernel now has a rule whose
  correctness depends on the environment being an honest one.
  `axeyum-lean-import` consuming official exports only becomes a load-bearing
  statement rather than a habit, and
  `acceleration_trusts_the_declared_type_not_the_body` is the test that says so.
- **Precedent, bounded.** This ADR authorises name-keyed literal evaluation for
  `Nat` on the shape checks above. It does **not** pre-authorise the same pattern
  for `String`, `Float`, `UInt*` or any future literal type; each is a separate
  decision with its own bootstrap and its own negative suite. The `String`
  literal slice — the next binding constraint, blocking 52% of `Init`+`Std` and
  79% of Mathlib sampled declarations — is sized but deliberately not taken here.
- **Revisit when** either a wire-level operation annotation exists, or the
  project stops consuming third-party exports, or someone finds a validation that
  covers the well-founded operations. Any of those would let the trust assumption
  shrink.
