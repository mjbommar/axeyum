# ADR-1636: first-order model theory lands on de Bruijn, and the eigenvariable condition is a shift

Status: accepted
Date: 2026-09-05
Lane: `model-theory`

Index-summary: The `fo_*.rs` group lifts the `ipc_*.rs` pattern from
propositional to first-order logic — `FO.Term`/`FO.Formula` over de Bruijn
indices with a signature restricted to arities 0/1/2, `FO.Structure` as a
record over a **parameter** carrier, `FO.sat` as constructive `Prop`-valued
Tarski satisfaction, the substitution lemma, a 16-rule natural deduction
calculus whose eigenvariable condition is a de Bruijn **shift of the premise's
context** rather than a side condition, soundness, and `FO.consistency`
(`⊥` is not derivable) via the ℕ model. Completeness is deliberately not
attempted and stays `open`.

## Context

`ipc_heyting.rs` / `ipc_provable.rs` / `ipc_eval.rs` / `ipc_soundness.rs`
already carry the full arc for *propositional* intuitionistic logic: syntax as
an inductive, semantics as a recursor application, a derivation relation, and
soundness by induction on derivations — all axiom-free, all through
`Kernel::add_declaration` and `Kernel::add_inductive`. Nothing in the kernel
had first-order syntax: `--name-like Structure`, `satisfies`, `Term.eval` and
`Model` were all absent before this lane.

The roadmap item (W3-6) asks for the same arc one quantifier level up. Four
design decisions were forced along the way, and each had a cheaper-looking
alternative that costs more later.

## Decision

### 1. Variables are de Bruijn indices, and substitution is parallel

`FO.Term.var : Nat -> FO.Term` is an index. With names, `all` would bind a
`Nat`, syntactic identity would stop being α-equivalence, and every theorem in
the group would have to be stated modulo an α-relation that itself needs an
inductive definition and a congruence proof. With indices, `Eq FO.Formula` is
the right notion everywhere.

Substitution is **parallel** — `FO.Term.subst : Term -> (Nat -> Term) -> Term`,
with a substitution being a total function `Nat -> FO.Term`. This is cheaper
than single-variable substitution, not more expensive: the substitution
lemma's binder case composes two substitutions, whereas the single-variable
version needs an auxiliary "substitution commutes with shifting" lemma before
it can even be stated. `FO.Subst.cons`/`lift`/`shift`/`id` are the four
operations the binder cases need.

### 2. The signature has arities 0, 1, 2, as `Nat`-indexed families

```text
FO.Term.f0 : Nat -> Term        FO.Term.f1 : Nat -> Term -> Term
FO.Term.f2 : Nat -> Term -> Term -> Term
FO.Formula.rel1 : Nat -> Term -> Formula
FO.Formula.rel2 : Nat -> Term -> Term -> Formula
```

The textbook `Term.app : Nat -> List Term -> Term` is a **nested** inductive
(`List` applied to the type being defined), and substitution, evaluation and
the substitution lemma over it each need a simultaneous induction over `Term`
and over lists of `Term`s. That is a second recursor and a doubling of all
four inductions in this group, for a generalisation the concrete work does not
yet need: ℕ with `0`, `succ`, `+`, `<` uses exactly arities 0/1/2 and relation
arities 1/2. Every definition and lemma treats the three function families
uniformly, so raising the arity bound is mechanical (one constructor, one
minor premise per recursion). This is a restriction on the **signature**, not
on the logic — the language still has `Nat`-indexed infinite families at each
arity.

### 3. `FO.Structure` is a record over a **parameter** carrier

```text
FO.Structure : Type -> Type
FO.Structure.mk : Π (M : Type), (Nat -> M) -> (Nat -> M -> M)
                  -> (Nat -> M -> M -> M) -> (Nat -> M -> Prop)
                  -> (Nat -> M -> M -> Prop) -> FO.Structure M
```

A record carrying its own carrier as a *field* would need the projection
`Structure.carrier : Structure -> Type` — a large elimination producing a
sort — and then every induction in `fo_substitution.rs` and `fo_soundness.rs`
would quantify over terms whose **type** is a stuck projection. Making the
carrier a parameter, exactly as `sigma_prelude.rs`'s `Sigma` does, keeps every
type in this group a syntactic `Sort`, and loses nothing: `Π (M : Type)
(S : FO.Structure M), …` is the same quantification with the carrier out
front.

The carrier sits at `Type` (`Sort 1`), not at a universe parameter, so the
group is universe-monomorphic and every recursor application carries a single
explicit level.

Equality is **not** one of the five interpreted families. `FO.Formula.eqf` is
a logical constructor and `FO.sat` sends it to the kernel's own `Eq M`, so no
structure can interpret `=` as anything else — standard first-order logic with
equality, and the reason `eqf_refl` needs no congruence side condition on the
structure.

### 4. The eigenvariable condition is a shift of the premise's context

```text
FO.Provable.all_intro : Π g p, Provable (FO.Context.shift g) p -> Provable g (all p)
FO.Provable.ex_elim   : Π g p q, Provable g (ex p)
                        -> Provable (Context.cons p (Context.shift g)) (Formula.shift q)
                        -> Provable g q
```

The textbook proviso ("the generalized variable is not free in Γ") is, in de
Bruijn form, the statement that the premise's context was shifted: every free
index in `g` has been raised by one, so index `0` — the one `all` is about to
bind — cannot occur in it. This is enforced by the constructor's *type*,
rather than by an `occursIn : Nat -> Formula -> Prop` predicate carried as an
extra hypothesis with a decidable occurs-check behind it. `ex_elim` carries
the condition twice over (context **and** conclusion), and
`fo_soundness.rs`'s minor for it uses both halves.

## Consequences

### What landed

| declaration | statement |
| --- | --- |
| `FO.Term`, `FO.Formula` | the two syntax inductives, with recursors |
| `FO.Term.subst`, `FO.Formula.subst` | parallel substitution |
| `FO.Subst.id`/`shift`/`cons`/`lift`, `FO.Term.shift`, `FO.Formula.shift` | the de Bruijn plumbing |
| `FO.Structure` + five projections | structures over a parameter carrier |
| `FO.Val.cons`, `FO.Term.eval`, `FO.sat` | valuations and Tarski satisfaction |
| `FO.natStructure`, `FO.nat_sat_lt_irrefl`, `FO.nat_sat_no_greatest` | ℕ as a structure, two sentences satisfied in it |
| `FO.Context`, `FO.Context.shift`, `FO.ctxSat` | contexts and their satisfaction |
| `FO.Provable` (16 rules) + three example derivations | the calculus |
| `FO.Val.cons_congr`, `FO.Term.eval_congr`, `FO.sat_congr` | the coincidence lemmas |
| `FO.Term.eval_subst`, `FO.sat_subst` | the substitution lemma |
| `FO.sat_shift`, `FO.sat_inst` | its two corollaries |
| `FO.ctxSat_shift`, `FO.soundness` | soundness |
| `FO.consistency` | `Not (Provable nil bot)`, via the ℕ model |

Everything is axiom-free, asserted in tests after `Environment::contains`.

### The coincidence lemmas are what a `funext`-free kernel costs

`FO.sat_subst`'s `∀` case produces a satisfaction claim at
`fun n => Term.eval M S (Subst.lift s n) (Val.cons M a w)` and needs it at
`Val.cons M a (fun n => Term.eval M S (s n) w)`. Those agree pointwise but are
not the same term, and this kernel has no `funext` (no `Classical.em`, no
`propext`, no `Quot.sound`). `FO.sat_congr` — "satisfaction only reads the
valuation pointwise" — is the bridge, and it must be an `Iff` rather than a
one-directional implication, because `FO.sat`'s `imp` clause puts a subformula
in negative position and the forward direction there consumes the backward
direction at the antecedent.

What the kernel gives back for free is the **shift**: `FO.Val.cons` is a
`Nat.rec`, so `fun m => FO.Val.cons M a v (Nat.succ m)` ι-reduces to
`fun m => v m` under the binder and the kernel's η rule closes it against `v`.
So `FO.sat_shift`'s proof term is a single application of `FO.sat_subst` with
no rewriting at all, and the `Nat.succ` case of both binder keys is a bare
instance of `FO.Term.eval_subst`. That claim is measured, not asserted:
`fo_semantics.rs`'s test
`shifting_past_the_new_slot_is_definitionally_the_old_valuation` checks it at
a symbolic carrier, element and valuation.

### `Prop`-valued satisfaction makes soundness *cheaper* than the IPC case

`ipc_soundness.rs` could not state soundness as "every valuation satisfying
the context satisfies the goal" — over its 3-element Heyting chain that
statement carries no induction through `imp_intro`, and it had to run the
induction on the *meet* of the context with the sat-shaped version recovered
afterwards. Here the obvious statement works, because `FO.sat M S (imp p q) w`
**is** the kernel's own function type. Nine of the sixteen minors are one
application of `And.intro`/`And.left`/`Or.inl`/`Or.elim`/`False.rec`/`Eq.refl`,
with no algebra layer in between. The chain lemmas that dominated
`ipc_soundness.rs` have no analogue here.

### Consistency is where the model earns its keep

```text
FO.consistency : Not (FO.Provable FO.Context.nil FO.Formula.bot)
  := fun d => FO.soundness Nat FO.natStructure nil bot d (fun _ => Nat.zero) True.intro
```

An arbitrary `FO.Structure M` would *not* do: `M` could be empty and the
argument still needs a valuation `Nat -> M` to exist. Using a structure whose
carrier is inhabited is what makes the corollary constructive, and it is the
first-order analogue of `ipc_soundness.rs`'s
`ipc_excluded_middle_not_provable` — a negative fact about a proof system,
obtained by pushing a derivation through a model.

### What is deliberately absent

- **Completeness.** Not attempted, and not a gap this ADR is hiding: it needs
  a term model over a maximal consistent extension (Lindenbaum), and in a
  kernel with no `Classical.em` the classical completeness theorem is not the
  statement to aim at. Recorded as the `open` fact
  `F:fo-completeness-henkin`, with `depends_on` naming what exists.
- **The Leibniz rule** (from `s = t` and `φ[s]` infer `φ[t]`). Sound, but its
  soundness case needs a congruence of `FO.sat` along an equality between the
  evaluations of two terms under a substitution — a fifth induction over
  `FO.Formula`. Recorded as the next increment rather than claimed.
- **Arities above 2**, for the reason in decision 2.

## Alternatives considered

- **Named variables with an α-equivalence relation.** Rejected: every theorem
  becomes a statement modulo α, and the eigenvariable condition becomes a
  decidable occurs-check the rule has to carry.
- **`Term.app : Nat -> List Term -> Term`.** Rejected for this increment: a
  nested inductive plus a mutual recursor, doubling four inductions, for a
  generality nothing downstream needs yet.
- **A structure record carrying its carrier as a field.** Rejected: a large
  elimination producing a sort, and stuck `Structure.carrier S` types
  throughout every induction.
- **A `Bool`-valued or classically-read `sat`.** Not available: the kernel has
  no `propext` and no excluded middle, so a truth-table semantics would need
  decidability of every atom. The constructive `Prop`-valued reading is both
  the only available one and the one that makes soundness cheap.
