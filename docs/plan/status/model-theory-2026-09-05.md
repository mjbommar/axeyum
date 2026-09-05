# Lane: model-theory — first-order syntax, structures, Tarski satisfaction and soundness (W3-6)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, model-theory, 2026-09-05).** W3-6 is landed: the
`ipc_*.rs` arc — syntax as an inductive, semantics as a recursor application,
soundness by induction on derivations — lifted one quantifier level, in five
new files
(`crates/axeyum-lean-kernel/src/fo_syntax.rs`, `fo_semantics.rs`,
`fo_provable.rs`, `fo_substitution.rs`, `fo_soundness.rs`) registered from the
crate root exactly the way the `ipc_*` modules are, plus one new example
binary. Every declaration has an empty `Kernel::axiom_footprint`
([ADR-1636](../../research/09-decisions/adr-1636-first-order-model-theory-lands-de-bruijn-and-the-eigenvariable-condition-is-a-shift.md)).

1. **Syntax.** `FO.Term` (de Bruijn `var`, plus `f0`/`f1`/`f2` — `Nat`-indexed
   families of function symbols at arities 0, 1, 2) and `FO.Formula` (`eqf`,
   `rel1`, `rel2`, `bot`, `and_`, `or_`, `imp`, `all`, `ex`), **parallel**
   substitution on both, and the de Bruijn plumbing `FO.Subst.id` / `shift` /
   `cons` / `lift`, `FO.Term.shift`, `FO.Formula.shift`.
2. **Semantics.** `FO.Structure` (a five-field record over a **parameter**
   carrier), its five projections, `FO.Val.cons`, `FO.Term.eval`, and `FO.sat`
   — constructive `Prop`-valued Tarski satisfaction. Plus `FO.natStructure`
   (ℕ with `0`, `succ`, `+`, `<`) and two sentences shown satisfied in it by
   kernel reduction, `FO.nat_sat_lt_irrefl` and `FO.nat_sat_no_greatest`.
3. **The substitution lemma.** `FO.sat_subst`, with the coincidence lemmas it
   needs (`FO.Val.cons_congr`, `FO.Term.eval_congr`, `FO.sat_congr`), the term
   half (`FO.Term.eval_subst`), and the two corollaries soundness consumes
   (`FO.sat_shift`, `FO.sat_inst`).
4. **Calculus and soundness.** `FO.Context`, `FO.Context.shift`, `FO.ctxSat`,
   `FO.Provable` (16 rules), three example derivations, `FO.ctxSat_shift`,
   `FO.soundness`, and `FO.consistency : Not (Provable nil bot)` — the
   underivability of `⊥`, obtained by pushing a hypothetical derivation
   through the ℕ model.

**The eigenvariable condition is a shift, not a side condition.**
`all_intro`'s premise is a derivation over `FO.Context.shift g`, so de Bruijn
index `0` — the one `all` is about to bind — cannot occur anywhere in the
premise's context. That is the whole proviso, enforced by the constructor's
*type*, with no `occursIn : Nat -> Formula -> Prop` predicate and no decidable
occurs-check to carry. `ex_elim` carries it twice (context **and**
conclusion). The soundness minor for `all_intro` is where it pays: the
induction hypothesis is available at `Val.cons M z w` precisely because the
context it constrains is the shifted one.

**`Prop`-valued satisfaction makes soundness CHEAPER than the IPC case, not
harder.** `ipc_soundness.rs` could not state soundness as "every valuation
satisfying the context satisfies the goal" — over its 3-element Heyting chain
that statement carries no induction through `imp_intro`, and it had to run on
the *meet* of the context with eleven chain lemmas underneath it. Here the
obvious statement works, because `FO.sat M S (imp p q) w` **is** the kernel's
own function type: `imp_intro`'s minor is a lambda, `imp_elim`'s is an
application, and nine of the sixteen minors are a single
`And.intro`/`And.left`/`Or.inl`/`Or.elim`/`False.rec`/`Eq.refl`. There is no
algebra layer at all. A lane extending this calculus should expect the
propositional rules to stay free and the quantifier rules to cost one
substitution-lemma corollary each.

**What the absence of `funext` costs, and what η gives back.** The
substitution lemma's `∀` case produces a claim at
`fun n => Term.eval M S (Subst.lift s n) (Val.cons M a w)` and needs it at
`Val.cons M a (fun n => Term.eval M S (s n) w)`. Those agree pointwise and are
not the same term, and this kernel has no `funext`. So `FO.sat_congr` exists,
and it must be an `Iff` rather than a one-directional implication — `FO.sat`'s
`imp` clause puts a subformula in negative position, so the forward direction
there consumes the backward direction at the antecedent, and a single-direction
induction does not close.

The **shift**, by contrast, is free, and this is the finding worth carrying
forward. `FO.Val.cons` is defined by `Nat.rec`, so
`fun m => FO.Val.cons M a v (Nat.succ m)` ι-reduces to `fun m => v m` under
the binder and the kernel's η rule (`tc.rs`'s `try_eta_expansion`) closes it
against `v`. Consequences: `FO.sat_shift`'s proof term is a **single
application** of `FO.sat_subst` with no rewriting; the `Nat.succ` case of both
binder keys is a **bare instance** of `FO.Term.eval_subst`; and the `Nat.zero`
case is `Eq.refl`. Any later development that extends a valuation should
define the extension by `Nat.rec` for exactly this reason. The claim is
measured, not asserted —
`fo_semantics.rs`'s `shifting_past_the_new_slot_is_definitionally_the_old_valuation`
checks it with the carrier, the element and the valuation all **bound**. Both
halves of that phrasing were bought by a failed first run: a check at a
*literal* valuation reduces both sides to the same closed term and never
exercises η, and a check at a *bare free variable* cannot pass however the
kernel behaves, because η-expansion needs the non-lambda side's type and a
variable made by `Kernel::fvar` carries none. The first draft used free
variables and failed for that reason, not because the claim was wrong.

**Arity is bounded at 2, and that is a signature restriction, not a logical
one.** `Term.app : Nat -> List Term -> Term` is a nested inductive, and
substitution, evaluation and the substitution lemma over it each need a
simultaneous induction over `Term` and over lists of `Term`s — a second
recursor and a doubling of all four inductions here. ℕ with `0, succ, +, <`
needs exactly arities 0/1/2 and relation arities 1/2. Every definition and
lemma treats the three function families uniformly, so raising the bound is
one constructor and one minor premise per recursion.

**Mutation table — both RUN, neither predicted.** Baseline
`scripts/cargo-serialized.sh test -j 4 -p axeyum-lean-kernel --lib -- fo_
--test-threads=4`: **41 passed, 0 failed**. Both mutants collected the same 41
tests, so both rows are `killed N` measurements and not a change in
collection. Both were restored byte-for-byte and `git status` is clean on both
files.

That baseline is **41** because the mutants were run before the clippy pass,
which deleted `test_fvar_block_is_disjoint_from_the_definition_block` — it
asserted a constant, so it measured nothing. A re-run today collects **40**.
The kill counts below are the numbers actually measured, not rescaled.

| mutant | edit | outcome |
| --- | --- | --- |
| A — delete the eigenvariable condition | `fo_provable.rs`, `rule::ALL_INTRO`: premise `Provable (Context.shift g) p` becomes `Provable g p` | **killed 6** (35 passed / 6 failed) |
| B — `∃` reads the wrong valuation shift | `fo_semantics.rs`, `declare_sat`'s `m_ex`: `ip (Val.cons M x v)` becomes `ip v` | **killed 27** (14 passed / 27 failed) |

Mutant A kills `fo_provable::tests::all_intro_quantifies_over_the_shifted_context`
(which reports the two types side by side: got
`Provable x0 x1 -> Provable x0 (all x1)`, want
`Provable (Context.shift x0) x1 -> Provable x0 (all x1)`) **and all five
`fo_soundness` tests**, because the `all_intro` minor of `FO.soundness` no
longer type-checks — `TypeMismatch` out of `add_declaration`, so
`build_fo_soundness_prelude` fails outright. That is the finding worth keeping:
the unsound rule is not merely unguarded by a test, it is **unprovable**. The
induction hypothesis would only constrain `w`, and the goal needs it at
`Val.cons M z w`.

Mutant B kills 27 of 41 — everything from `fo_semantics` upward — because
`FO.nat_sat_no_greatest` stops admitting (`DeclarationValueMismatch`) and
`build_fo_semantics_prelude` fails, taking `fo_provable`, `fo_substitution` and
`fo_soundness` with it. The 14 survivors are exactly `fo_syntax`'s, which does
not depend on the semantics. A kill that broad is less *discriminating* than
A's, and the reason is worth stating: the sentence `∀x ∃y, x < y` is the only
declaration in the group whose admission depends on the `∃` clause reading the
right valuation slot, and it sits at the bottom of the dependency chain. The
narrow guard for the same defect is
`fo_semantics::tests::sat_of_a_two_binder_sentence_reads_the_right_valuation_slots`,
which compares the reduced form against both the correct reading and the
swapped one.

**Not landed, with the obstruction sized.**

- **Completeness** — not attempted, per the brief. It needs a term model over
  a maximal consistent extension (Lindenbaum), and in a kernel with no
  `Classical.em` the classical statement is not the one to aim at. Recorded as
  the `open` fact `F:fo-completeness-henkin`.
- **The Leibniz rule** (from `s = t` and `φ[s]` infer `φ[t]`). Sound, and the
  only equality rule missing — `eqf_refl` is landed. Its soundness case needs
  a congruence of `FO.sat` along an equality between the *evaluations of two
  terms*, which is a fifth induction over `FO.Formula` of roughly `sat_congr`'s
  size (nine minors). Sized at one slice.
- **Higher arities**, as above.
