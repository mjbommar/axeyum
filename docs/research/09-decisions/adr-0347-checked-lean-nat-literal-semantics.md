# ADR-0347: Type Lean Nat literals only against a checked canonical bootstrap

Status: accepted

Date: 2026-07-22

## Context

TL2.6 made `Lit::Nat` arbitrary precision but deliberately left every literal
untyped. TL2.7 must now reproduce the pinned Lean 4.30 kernel boundary without
absorbing TL2.8's accelerated Nat-operation program.

Lean's core expression contract assigns a raw `.natVal` literal the type
`Nat`. Its kernel definitional-equality loop recognizes `Nat.zero` and literal
zero as the same offset, and recognizes either a positive literal or a unary
`Nat.succ` application by peeling one predecessor. Nat recursor reduction also
converts a literal major premise one constructor layer at a time. Separately,
the official kernel has optimized reductions for `Nat.add`, `Nat.mul`, division,
bitwise operations, and other functions; those are not needed to type a
literal or establish constructor/literal equality.

Official Lean starts from its bootstrapped environment. Axeyum's format-3.1
importer intentionally starts from an empty independent kernel and admits the
exported `Nat` family itself. Returning `Const Nat` for a literal without first
checking what the fresh environment assigned to the reserved `Nat`,
`Nat.zero`, and `Nat.succ` names would make the primitive typing rule depend on
unvalidated name coincidence.

## Decision

**Enable Nat literal typing only when the checked environment contains the
canonical non-polymorphic `Nat : Type` family with exactly the constructors
`Nat.zero : Nat` and `Nat.succ : Nat -> Nat`. Then type every `Lit::Nat` as
`Const Nat`, implement Lean's zero/successor offset definitional equality,
reduce `Nat.succ (Lit n)` to `Lit (n+1)`, and let Nat recursors expose one
literal constructor layer. Keep every other Nat operation and every String
literal unsupported in this slice.**

The canonical bootstrap check consumes only declarations admitted through the
existing trusted inductive gate. It requires:

- `Nat` has no universe parameters, parameters, or indices;
- its stored type is exactly `Sort 1`;
- it is recursive and lists exactly `Nat.zero`, then `Nat.succ`;
- `Nat.zero` is constructor index 0 with no fields and type `Nat`;
- `Nat.succ` is constructor index 1 with one field and type `Nat -> Nat`;
- all three declarations carry no universe parameters.

Missing or mismatched bootstrap declarations produce a typed
`KernelError::NatLiteralBootstrapMismatch`, never a guessed type. String
literals retain `KernelError::UnsupportedLit` until TL2.9.

The conversion rules are deliberately narrow:

1. `Lit 0` is definitionally equal to `Nat.zero` in either direction.
2. `Lit (n+1)` and `Nat.succ t` are definitionally equal exactly when
   `Lit n` and `t` are definitionally equal.
3. `Nat.succ (Lit n)` weak-head reduces to `Lit (n+1)`; no `Nat.add`,
   `Nat.mul`, comparison, division, bitwise, or native reduction lands here.
4. A Nat recursor with major `Lit 0` selects its zero rule; with major
   `Lit (n+1)` it selects its successor rule with `Lit n` as the field.
5. Same-valued literals remain structurally interned; unequal literals do not
   become equal through the offset rule.

The format-3.1 importer may now append a validated `natVal` expression and let
the ordinary declaration gate decide its use. The exact official Nat closure
must admit before the `literal-nat-typing` decline code is retired. Parsing a
literal alone is not independent-admission credit.

## Evidence and exit gates

TL2.7 is complete only when:

1. Nat literals infer as the exact checked `Nat` constant, including values
   above `2^128`;
2. empty, missing, renamed, reordered, or malformed Nat bootstrap shapes reject
   with the typed mismatch before a literal can admit a declaration;
3. zero, one-step successor, a complete small unary chain, and an above-`u128`
   literal/predecessor pair are definitionally equal in both directions;
4. adjacent false pairs reject, and wrapper/delta cases do not bypass the
   offset rule;
5. `Nat.succ` reduction and `Nat.rec` computation over literals agree with
   constructor computation without enabling any other Nat operation;
6. the deterministic seam-fuzz literal family changes from universal rejection
   to a typed split: canonical-Nat cases must infer/replay safely, String cases
   must remain fail-closed, and every attempted `False` admission must reject;
7. the pinned official Nat stream's 90 expressions and five records become ten
   independently checked declarations with zero axioms, and the imported
   `importNatLiteral` unfolds to literal 37;
8. a malformed-bootstrap fixture mutation rejects at the kernel gate;
9. pinned Lean 4.30 accepts the same zero/successor, unary, recursor, and
   above-`u128` positive equalities and rejects an adjacent false equality;
10. compatibility and documentation contracts remove only
    `literal-nat-typing`; String and quotient declines remain explicit.

Primary sources:

- [Lean 4.30 `Literal.type` and raw Nat literal contract](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Expr.lean)
- [Lean 4.30 offset equality and Nat reduction](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/type_checker.cpp)
- [Lean 4.30 literal-to-constructor recursor conversion](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/inductive.h)

## Alternatives

### Return `Const Nat` without checking the fresh environment

Rejected. That mirrors the expression-level result but omits the bootstrap
precondition official Lean inherits. Axeyum must authenticate the reserved
declarations it imports into an initially empty environment.

### Expand every literal to a complete unary constructor tree

Rejected. It destroys the compact arbitrary-precision representation and is
impossible at realistic large values. Lean peels one offset layer when needed.

### Enable all optimized Nat reductions now

Rejected. Typing and constructor conversion have a small exact semantic
surface. Bulk arithmetic acceleration has different resource and differential
gates and remains TL2.8.

### Admit the official stream without native constructor/recursor tests

Rejected. The selected closure uses only a projection-backed `OfNat` instance;
it would not by itself prove the kernel's literal/construction computation
boundary.

## Consequences

- Nat literal inference becomes environment-dependent on a checked reserved
  bootstrap shape; this dependency is explicit and testable.
- One-step predecessor/successor conversion allocates canonical bignums but
  never narrows them.
- Small unary terms can compare linearly; large values stay compact and can be
  compared one constructor layer at a time.
- Nat recursors compute over raw literals with the same existing checked rules;
  no new recursor rule or trusted arithmetic oracle is introduced.
- The exact Nat root becomes a K1 passing row, but this grants no String,
  `Init`, `Std`, mathlib, frontend numeral elaboration, or accelerated Nat
  operation claim.
