# ADR-0385: A proved `Nat` prelude for the Lean kernel

- Status: proposed
- Date: 2026-08-12
- Deciders: (pending review)

## Context

`axeyum-lean-kernel` (ADR-0036) shipped two preludes with a gap between them.

`build_logic_prelude` admits the propositional connectives and — importantly
— **`Nat` as a genuine recursive inductive with a genuine `Nat.rec`**. So
induction over the naturals was available in the kernel from the start, with
no axiom required.

`build_arith_prelude` (the P3.7 / LRA-reconstruction foundation) axiomatizes
a *linear ordered field*: 30 `Declaration::Axiom`s for a carrier `R` with
`add`/`mul`/`neg`/`le`/`lt` and the order and field laws. That is the right
shape for reconstructing Farkas refutations, where the axioms are exactly the
rules a Farkas chain invokes, and where the carrier is deliberately opaque.

Between them there was **nothing**: no arithmetic on `Nat`, and no `Eq`
combinators at all — no `Eq.symm`, no `Eq.trans`, no `congrArg`. Every
consumer wanting to state and prove an ordinary arithmetic fact had to build
that layer for itself from `Eq.rec` and `Nat.rec`.

This was not hypothetical. A development proving a mathematical theorem
(`tests/rado_shell_arithmetic.rs`) built, inside a single test file: `add`,
`mul` and `pow` as structural recursions; twelve algebraic lemmas; the `Eq`
combinators; an induction helper; and the declaration plumbing. Roughly 650
lines of it were entirely generic and would have to be rewritten verbatim by
the next consumer.

The distinction that matters for the trusted base: over the *axiomatized*
field these facts would have to be **assumed**, whereas over the *inductive*
`Nat` they are **provable**. Choosing the field carrier for naturals-shaped
work would have silently traded theorems for axioms.

## Decision

Add `build_nat_prelude` (`crates/axeyum-lean-kernel/src/nat_prelude.rs`),
declaring everything through the trusted `Kernel::add_declaration` gate, with
**zero axioms**.

- **Definitions** `Nat.add`, `Nat.mul`, `Nat.pow` by `Nat.rec` on the second
  argument, so their defining equations hold *definitionally*.
- **Defining equations as named theorems** (`add_zero`, `add_succ`,
  `mul_zero`, `mul_succ`, `pow_zero`, `pow_succ`), each an `Eq.refl` proof,
  so callers may rewrite without knowing the recursion scheme.
- **Algebra**: `zero_add`, `succ_add`, `add_comm`, `add_assoc`,
  `add_right_comm`, `zero_mul`, `succ_mul`, `mul_comm`, `left_distrib`,
  `mul_assoc`, `one_mul`, `mul_one`.
- **Order**: `Nat.le` as an indexed `Prop` inductive with Lean's own
  constructor shape (`le.refl`, `le.step`), plus `zero_le`, `le_succ_succ`,
  `le_trans`, `le_add_right`, proved with the kernel-generated `Nat.le.rec`
  (i.e. induction on the derivation).
- **`NatOps`**: the reusable machinery as *provided* trait methods over two
  required accessors — the `Eq` combinators (`symm`, `trans`, `congr`,
  `chain`, `transport`, `eq_motive`), the `Nat.rec` `induct` helper, and
  `define_binary` / `theorem` / `try_theorem` plumbing.

Declarations live under the **`Nat` namespace**. `lean_pp::render_name`
remaps that root segment to `AxNat`, so the exporter emits `def AxNat.add`
and cannot shadow real Lean's builtin `Nat.add`; top-level names would also
have collided with `int_prelude`'s axiomatized `add`/`mul`.

`NatOps` is a trait rather than a struct owning the kernel so that a
development keeps its own operators as inherent methods and its proof
closures continue to take `&mut ItsOwnDev`.

## Consequences

**Zero axioms, enforced.** `the_nat_prelude_declares_no_axioms` walks the
environment for `Declaration::Axiom` and requires the list to be empty. This
is the property that distinguishes the prelude from `arith_prelude`, and it
is a test rather than a comment.

**Negative controls.** Eight tests require the kernel to *reject* swapped
lemma arguments, the wrong lemma, an omitted induction step, a wrong base
case, a transposed conclusion (a *true* claim with an invalid proof), a false
identity, a bogus order fact, and a reversed bound — and assert that none of
them reached the environment. A checker that has never rejected anything is
untested.

**The extraction is verified faithful.** `tests/rado_shell_arithmetic.rs` was
rewritten to consume the prelude: 92 lines added, 651 removed, and its proof
scripts are byte-identical. It proves the same theorems and passes the same 9
tests. Crate `--lib` count moved 199 → 206.

**`Nat.le` ships narrowly and is documented as such.** ADR-0390 has since added
reducible `lt` and checked `le_of_succ_le_succ` through a predecessor-style
motive. Antisymmetry, totality, `min`, and decidability remain absent. Its
constructor shape is exactly Lean's, so these additions carry no redesign
risk, but callers must not mistake the fragment for a complete order library.

**What remains missing** is library work, not expressiveness: complete order,
subtraction, and the larger divisibility/valuation layer. ADR-0389 has
since promoted the proved `Nat.dvd` / `dvd_mul` / `dvd_add` foundation from the
Rado capability probe; cancellation, congruence, Euclidean division, gcd, and
valuation remain open.

**Relationship to the north star.** ADR-0036's aim is that every
`unsat`/`valid` carry a proof a Lean-grade kernel accepts. `arith_prelude`
serves that for LRA reconstruction, where axioms are appropriate. This
prelude serves the *mathematics* side, where they are not — and it
establishes that the kernel can carry proved induction with nothing assumed.
