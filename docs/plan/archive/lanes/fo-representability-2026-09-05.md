# Lane: fo-representability — Robinson's Q is now a kernel object, and the pairing is one polynomial equation

<!-- plan-section: lane-status -->

**Q as an `FO.Context` with the ℕ model, its consistency, the numeral arithmetic
it proves, and the positive half of representability for `FO.Code.pair`**
(`DONE`, fo-representability, 2026-09-06, ADR-1651).

## What landed

`build_fo_robinson_prelude` (`crates/axeyum-lean-kernel/src/fo_robinson.rs`) is
the first builder that holds BOTH `fo_*` chains in one kernel — 132 declarations
over the `Nat` prelude, every one axiom-free, checked as a set difference
against the authority rather than against a list.

| declaration | statement |
| --- | --- |
| `FO.natStructureQ` | `FO.Structure Nat` with `+` at `f2 0` and `·` at `f2 1` |
| `FO.Q.axSuccNeZero` … `FO.Q.axMulSucc` | the seven Robinson axioms, as `FO.Formula` |
| `FO.Q` | `FO.Context` — the seven, in that order |
| `FO.Q.natModels` | `Π v, FO.ctxSat Nat FO.natStructureQ FO.Q v` |
| `FO.Q.consistency` | `Not (FO.Provable FO.Q FO.Formula.bot)` |
| `FO.Term.subst_numeral` | `Π s n, Term.subst (numeral n) s = numeral n` |
| `FO.Q.add_numeral` | `Π a b, Provable Q (numeral a + numeral b = numeral (a+b))` |
| `FO.Q.mul_numeral` | `Π a b, Provable Q (numeral a · numeral b = numeral (a·b))` |
| `FO.Code.tri_two` | `Π n, tri n + tri n = n·n + n` |
| `FO.Code.pair_two` | `Π a b, pair a b + pair a b = ((a+b)·(a+b) + (a+b)) + (a+a)` |
| `FO.Q.pairGraph`, `FO.Q.pairFormula` | the defining formula, and it as one `FO.Formula` |
| `FO.Q.pair_represented` | `Π a b, Provable Q (pairGraph ā b̄ pair(a,b)‾)` |

## The brief's premise that had to change

`FO.natStructure` — the ℕ structure `fo_semantics.rs` already builds — **has no
multiplication at any symbol index**: its binary family is `x + y + k` for every
`k`. So `ℕ ⊨ Q` could not be proved against it and Q6/Q7 could not even be
interpreted. The lane built `FO.natStructureQ` instead, dispatching `fn2` on the
symbol index, and kept the other four families verbatim so
`FO.Term.numeral` (from the arithmetization chain) is the numeral function of
this signature rather than a translation of it.

The first version of the test that measures this was **wrong at one data
point**: `fn2 1 2 3 = 6 = 2 · 3`. It now uses two witness pairs plus a positive
control, which is the general shape a "this family is not that function" check
needs.

## What did NOT land, sized

- **The uniqueness half of representability**,
  `Q ⊢ ∀z (pairGraph(ā,b̄,z) → z = pair(a,b)‾)`. Not effort: Q has no induction
  and none of its seven axioms constrains a variable, so
  `Q ⊢ ∀z (z + z = m̄ → z = k̄)` is unavailable. Needs the order axioms plus the
  numeral case-split — a strictly larger theory, its own slice, its own ADR. A
  test asserts the ABSENCE of `FO.Q.pair_unique` so the note cannot rot.
- **The negative twin** `a ≠ b → Q ⊢ ¬(ā = b̄)`, which is the last ingredient
  for *numeralwise* uniqueness. Its derivation lives under an `imp_intro`, i.e.
  in `cons φ FO.Q`; every helper in `fo_robinson.rs` is written at the fixed
  context `FO.Q`. Cost: generalise five signatures over the context.
- **`unpair`, `diag`, the provability-level diagonal lemma.** Gated on the two
  above.

## Gates

`cargo test --release -p axeyum-lean-kernel --lib -- fo_robinson:: --test-threads=4`
runs **18** tests, all passing. Two mutants were RUN from a clean tree, each
rebuilt and re-measured in the same foreground call, each killing **18 of 18**
at `Kernel::add_declaration` with a `TypeMismatch`:

| mutant | RUN / PREDICTED | kills |
| --- | --- | --- |
| `axSuccNeZero` asserts `S x = 0` instead of refuting it | RUN | 18 / 18 |
| `add_numeral`'s conclusion swaps `a` and `b` | RUN | 18 / 18 |

Both are blunt: the package is one build, so a rejected declaration takes every
test with it. Neither isolates the theorem it targets, and that is a property of
the prelude-shaped fixture, not of the guards.

<!-- plan-section: landed-changes -->

| 2026-09-06 | `eab182faf` | `declare_fo_semantics_over` / `declare_fo_provable_over` / `declare_fo_soundness_over`. Both `fo_*` chains descend from `fo_syntax.rs` and every `build_*_prelude` rebuilds the chain beneath it, so no kernel could hold `FO.Provable` and `FO.Term.numeral` at once -- the second `FO.Term` fails with `DeclarationExists`. The three entry points take the already-built dependency, in the shape `declare_fo_substitution_over` already used for the same reason; each `build_*_prelude` keeps its signature and delegates. |
| 2026-09-06 | `87675da01` | `FO.Q : FO.Context` -- the seven Robinson axioms over `0, S, +, *, <` -- with `FO.natStructureQ`, `FO.Q.natModels` and `FO.Q.consistency`. `FO.natStructure` could NOT be the model and the test MEASURES that rather than asserting it: its binary family is `x + y + k` at every symbol index. Four of the seven satisfaction obligations are `Eq.refl`, because `Nat.add`/`Nat.mul` recurse on their right argument and Q4-Q7 are therefore the defining equations. |
| 2026-09-06 | `272994713` | `FO.Q.add_numeral`, `FO.Q.mul_numeral`, `FO.Term.subst_numeral`. `Nat.rec` on the SECOND argument, so each successor step is one `eqf_subst`. The two-variable axioms leave the outer numeral under `Subst.lift` as a stuck `Term.subst (Term.subst (numeral a) Subst.shift) sigma`; `subst_numeral` is what unsticks it, twice per instantiation. `mul_numeral` depends on `add_numeral` and the test reads that edge out of the kernel's own proof term. |
| 2026-09-06 | `bbce3bdfa` | `FO.Code.tri_two`, `FO.Code.pair_two`, `FO.Q.pairGraph`, `FO.Q.pairFormula`, `FO.Q.pair_represented`. The doubling identity removes `tri`'s recursion and turns the pairing's graph into ONE polynomial equation, so `pairFormula` is a genuine `FO.Formula` in three free indices. Positive half only: the uniqueness half is refused because Q has no induction, and a test asserts the ABSENCE of `FO.Q.pair_unique` so the refusal cannot go stale. |
