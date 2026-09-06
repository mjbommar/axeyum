# ADR-1651: Robinson's Q is an `FO.Context`, and the two `fo_*` chains have to share one `fo_syntax`

Status: accepted
Date: 2026-09-06
Index-summary: Lands Robinson's Q as `FO.Q : FO.Context` over `0, S, +, ·, <`, a new ℕ structure that interprets it (the existing `FO.natStructure` has NO multiplication at any symbol index — measured, not assumed), `ℕ ⊨ Q`, the consistency of Q via soundness, and the numeral arithmetic Q proves (`add_numeral`, `mul_numeral`). Representability of `FO.Code.pair` lands as one polynomial equation, positive half only; the uniqueness half is refused because Q has no induction. Also opens three `declare_*_over` entry points so the arithmetization chain and the calculus chain can live in one kernel.
Index-status: accepted

## Context

ADR-1636 built the first-order model theory group (`fo_syntax` → `fo_semantics`
→ `fo_substitution` → `fo_provable` → `fo_soundness`); ADR-1640 built the
arithmetization (`fo_code` → `fo_numbering` → `fo_decode` → `fo_roundtrip`),
which owns `FO.Term.numeral` and `FO.Code.diagAux_code`, the arithmetization
half of the diagonal lemma. ADR-1648 named what the **provability-level**
diagonal lemma still needed, and the first item on that list was: *`Γ_Q` written
down as an `FO.Context`*. Nothing in `fo_*.rs` related `FO.Provable` to any
particular theory.

## Decision

### 1. The two `fo_*` chains get `declare_*_over` entry points

Both chains descend from `fo_syntax.rs`, and every `build_*_prelude` rebuilds
the whole chain beneath it. So calling two of them on one kernel fails at the
second `FO.Term` with `KernelError::DeclarationExists` — which means **no kernel
could hold `FO.Provable` and `FO.Term.numeral` at the same time**, and the
provability-level diagonal lemma was blocked on a build-plumbing fact rather
than on any mathematics.

`fo_semantics.rs`, `fo_provable.rs` and `fo_soundness.rs` each gained a
`declare_*_over` function taking the already-built dependency, in the shape
`fo_substitution.rs`'s `declare_fo_substitution_over` already used for exactly
this reason (its comment names the same `DeclarationExists` failure). Each
`build_*_prelude` keeps its signature and delegates; no declaration count moves
and no existing caller changes. `build_fo_robinson_prelude` is the first builder
to hold both chains — 132 declarations over the `Nat` prelude, all axiom-free.

### 2. `FO.natStructure` cannot be the model, so there is a second structure

The obstruction is measured, and the first draft of the test that measures it
was **wrong**, which is why the test now carries two witnesses.

`FO.natStructure`'s binary family is `fn2 k x y := Nat.add (Nat.add x y) k`,
i.e. `x + y + k` at every symbol index `k`. Multiplication is not any member of
that family, so `Q6`/`Q7` cannot even be interpreted there. The naive check —
"is `fn2 k 2 3` equal to `2 · 3`?" — is **false as a test**: at `k = 1` it gives
`6`, which *is* `2 · 3`. `fo_robinson/tests.rs` therefore uses two witness pairs,
`(3, 4)` and `(2, 5)`, which agree with multiplication only at `k = 5` and
`k = 3` respectively, plus a positive control that every index really computes
`x + y + k`.

`FO.natStructureQ` keeps four of the five families verbatim and dispatches `fn2`
on the symbol index through `Nat.rec`, so `f2 0` ι-reduces to `Nat.add` and
`f2 (succ _)` to `Nat.mul`. `f0 0`, `f1 1` and `rel2 0` stay definitionally
`Nat.zero`, `Nat.succ` and `Nat.lt` — which is what makes `FO.Term.numeral`
(from the *other* chain) the numerals of this signature rather than a
translation of them.

### 3. Seven axioms, and `axCases` is the DISJUNCTION

```text
axSuccNeZero := all (imp (eqf (S (var 0)) 0) bot)
axSuccInj    := all (all (imp (eqf (S (var 1)) (S (var 0))) (eqf (var 1) (var 0))))
axCases      := all (or_ (eqf (var 0) 0) (ex (eqf (var 1) (S (var 0)))))
axAddZero    := all (eqf (var 0 + 0) (var 0))
axAddSucc    := all (all (eqf (var 1 + S (var 0)) (S (var 1 + var 0))))
axMulZero    := all (eqf (var 0 · 0) 0)
axMulSucc    := all (all (eqf (var 1 · S (var 0)) (var 1 · var 0 + var 1)))
```

`axCases` is `x = 0 ∨ ∃y. x = S y`, not the classically equivalent
`¬(x = 0) → ∃y. x = S y`. This kernel has no `Classical.em`, so the two are
different formulas here and the disjunction is the stronger one — it is what ℕ
satisfies constructively (by `Nat.rec`), and the implication is derivable from
it. Taking the weaker form would have been a silent weakening of Q.

`<` is in the signature and is interpreted, but none of the seven axioms
mentions it. That is Robinson's Q as usually presented; the order is a
definitional extension. This matters below.

### 4. `ℕ ⊨ Q` is seven one-liners, four of them `Eq.refl`

`Nat.add` and `Nat.mul` recurse on their RIGHT argument in this kernel, so
`x + 0 = x`, `x + S y = S (x + y)`, `x · 0 = 0` and `x · S y = x · y + x` are
the DEFINING equations — i.e. exactly Q4–Q7. `FO.Q.consistency` is then
`FO.soundness` at `FO.natStructureQ` with the constant-zero valuation, the same
one-liner `FO.consistency` is at the empty context.

### 5. Numeral arithmetic, and the one lemma the de Bruijn encoding forces

`FO.Provable.all_elim`'s conclusion is an unreduced
`Formula.subst p (Subst.cons t Subst.id)`. For a **single**-variable axiom that
reduces away completely, because the axiom bodies contain no numerals and
`Term.subst (var 0) σ` IS the instance term definitionally — the base cases of
`add_numeral`/`mul_numeral` need no repair at all. For a **two**-variable axiom
it does not: the outer instantiation leaves the outer numeral under
`Subst.lift`, i.e. as `Term.subst (Term.subst (numeral a) Subst.shift) σ`, stuck
because `FO.Term.numeral` is a `Nat.rec` on a symbolic argument.
`FO.Term.subst_numeral` unsticks it.

Both numeral theorems are `Nat.rec` on the SECOND argument, mirroring the
recursion in `Nat.add`/`Nat.mul` and in `axAddSucc`/`axMulSucc`, so each
successor step is ONE `eqf_subst`. `mul_numeral` depends on `add_numeral`:
`axMulSucc` gives `a · S k = a · k + a`, and rewriting `a · k` to its numeral
leaves an object-level SUM rather than a numeral.

### 6. Representability of the pairing: the positive half, and a refusal

`FO.Code.pair a b = FO.Code.tri (a + b) + a` and `tri` is a `Nat.rec`, so the
pairing is not first-order definable by unfolding it. The doubling identity
`FO.Code.tri_two : tri n + tri n = n·n + n` removes the recursion entirely and
turns the graph into one polynomial equation:

```text
FO.Q.pairGraph x y z := eqf (z + z) (((x+y)·(x+y) + (x+y)) + (x+x))
```

`FO.Q.pair_represented : Π a b, Provable Q (pairGraph ā b̄ pair(a,b)‾)` is the
positive half — six Leibniz steps, five evaluating the polynomial side down to a
single numeral from `eqf_refl`, and a sixth transferring the result.

**The uniqueness half is refused, and this is a decision, not a stopping
point.** `Q ⊢ ∀z (pairGraph(ā, b̄, z) → z = pair(a,b)‾)` needs Q to prove
something about a universally quantified variable; Q has no induction and none
of its seven axioms constrains a variable, so `Q ⊢ ∀z (z + z = m̄ → z = k̄)` is
not derivable at this strength. The textbook route adds the order axioms — the
`<` this ADR deliberately left unconstrained — plus the numeral case-split
`∀x (x < n̄ → x = 0̄ ∨ … ∨ x = (n-1)‾)` and Σ₁-completeness on top. That is a
strictly larger theory than the seven axioms, and it belongs in its own slice
with its own ADR.

`fo_robinson/tests.rs` asserts the **absence** of any `FO.Q.pair_unique` /
`FO.Q.pair_functional` in the environment, so the refusal cannot go stale
silently: if a later slice lands one, that test is what says so.

## Consequences

- Gödel I stays hypothesis-carrying and open. What it now lacks is one
  ingredient rather than four: the negative twin
  `a ≠ b → Q ⊢ ¬(ā = b̄)`, whose derivation lives under an `imp_intro` — i.e.
  in `cons φ FO.Q`, not in `FO.Q` — and every helper in `fo_robinson.rs` is
  written at the fixed context `FO.Q`. Generalising them over the context is
  five signatures (`Rob::prov_q`, `q_axiom_derivation`, `all_elim_at`,
  `cast_derivation`, `leibniz`).
- The `Leibniz` plan's formula shape is data (`Tm`/`EqShape`), not a closure,
  which is what made six further rewrite sites cheap. Any later slice that
  needs object-level rewriting should extend that type rather than write another
  closure.
- `crates/axeyum-lean-kernel/examples/fo_robinson_inventory.rs` is the
  `checker_command` for the `F:fo-q-*` facts. It fails on absence: a named
  filter matching nothing exits non-zero.

## Alternatives rejected

- **Redefining `FO.natStructure`'s `fn2` in place.** It would have changed the
  meaning of `FO.nat_sat_lt_irrefl` and `FO.nat_sat_no_greatest`, which are
  another slice's theorems, and the `+ k` shift is load-bearing in their proofs.
- **Duplicating `FO.Term.numeral` under a `FO.Q` name** instead of opening the
  `declare_*_over` entry points. Cheaper by three small edits, and it would have
  made the eventual bridge to `FO.Code.diagAux_code` a translation between two
  numeral functions rather than an identity — i.e. it would have bought a
  three-line saving with the exact obstruction ADR-1648 was written to remove.
- **Stating `axCases` in the implication form.** Weaker in a kernel with no
  `Classical.em`, for no gain.
