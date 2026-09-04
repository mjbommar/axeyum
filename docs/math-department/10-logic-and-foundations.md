# 10 — Logic and foundations

Reviewer: a proof theorist, with an interest in reverse mathematics
Verdict, 2026-09-04: **the most interested reviewer in the department, and for reasons the other eleven do not share**
Last measured: 2026-09-04 at `1856cdb3c`

> "Everyone else is reviewing your theorems. I am reviewing your kernel, and
> your kernel is the paper."

## The persona

Cares about which axioms a theorem needs, what a proof system can and cannot
derive, and whether a formal development means what it claims. Reads
`#print axioms` before reading the theorem. Regards a large library proved
from strong axioms as less interesting than a small one whose exact strength
is known. Their instinct on any formalization is to ask what the *trusted base*
is and whether anyone has checked it.

## What the library has today

**Two things: a kernel with an unusually explicit trusted base, and a small
body of genuine metatheory.**

**The kernel.** A Lean-compatible type theory with:

- inductive types with strict positivity checking, mutual and nested groups,
  and nested-inductive elimination
- universe polymorphism with a bound-parameter guard, and a constructor-field
  universe guard (ADR-1495)
- recursors, ι-reduction, K-like reduction, structure eta, projections with
  their own congruence and reduction rules
- well-founded recursion (`WellFounded.fix`, `Acc.rec`) with `fix_eq`
- Lean's four-declaration quotient package (`Quot`, `Quot.mk`, `Quot.lift`,
  `Quot.ind`) — **without `Quot.sound`**
- **no `funext`, no `propext`, no choice, no excluded middle**
- `Kernel::axiom_footprint`, read from the environment, as the only admissible
  source of an axiom claim

Each guard has its own integration suite: `strict_positivity`,
`declaration_universe_params_must_be_bound`,
`lambda_binder_domain_must_be_a_type`, `prop_large_elim_soundness` and
`prop_large_elim_derives_false`, `nested_phantom_parameter_soundness`,
`k_like_reduction`, `structure_eta`, `projection_congruence`. The kernel is
also cross-checked against official Lean's own kernel on exported
`lean4export` streams, and a **named, measured divergence** between Lean's
elaborator and Lean's kernel is recorded rather than worked around
(ADR-0517, amended 2026-09-03).

**The metatheory.**

| result | detail |
|---|---|
| **Excluded middle is not derivable in IPC** | `ipc_excluded_middle_not_provable`, with the eleven `Provable` constructors read out of the kernel environment and shown to be exactly the intuitionistic natural-deduction rule set, plus a Heyting-algebra countermodel (`ipc_heyting`, `ipc_ctx_meet`, `ipc_himp`, `ipc_le_join`, `ipc_le_meet`) |
| **EM ↔ the unrestricted least-number principle** | `Nat.em_implies_lnp` and `Nat.lnp_unrestricted_implies_em`, with the decidable and bounded forms proved outright (`Nat.lnp_decidable`, `Nat.lnp_bounded_search`, `Nat.lnp_of_pointwise_decision`) |
| **ℕ is a natural-numbers object** | `Nat.Peano.induction`, `injective`, `surjective`, `iter_unique`, `rec_unique`, `zero_ne_succ` — Dedekind categoricity with uniqueness of iteration |
| **ℤ is characterized categorically** | `Int.Characterization.categorical`, `iso`, `rec_unique` |
| **Cantor** | `Nat.cantor_no_fixed_point` |
| classical propositional logic, as consequences | Peirce's law, double-negation elimination, De Morgan in both directions, disjunctive syllogism, EM's irrefutability — each proved *from* EM as a hypothesis, never from an axiom |

Open, and honestly marked as such: Gödel's first incompleteness theorem, the
undecidability of first-order validity, and the independence of the continuum
hypothesis all sit in the ledger with `epistemic_status: open`.

## Their verdict

**The EM/LNP pair is real reverse mathematics.** Proving that the unrestricted
least-number principle over ℕ is *equivalent* to excluded middle, while the
decidable and bounded forms are outright theorems, is exactly the kind of
calibration their field exists to do. It is a small result and it is the right
kind of result, and it is stated in the strongest available form: the
principles are hypotheses discharged at use, so the footprint stays empty.

**The IPC unprovability result is more than a formality.** What makes it worth
something is the part most formalizations skip: the eleven `Provable`
constructors are read out of the kernel environment and shown to be exactly
the intuitionistic natural-deduction rules, the `Formula` type is shown to
have no `top` constructor, strict positivity is checked, and the checker
discriminates in both directions. That is a metatheorem about a formal system
with the encoding audited, rather than a statement about whatever the author
happened to write down.

**The trusted base is the headline, and it is defensible.** 2,487 proved
propositions with an empty axiom footprint, read from `Kernel::axiom_footprint`
rather than claimed in prose, and a validator that fails a proved fact with no
checked evidence. This reviewer would say — and no other reviewer in the
department would care — that this is a stronger claim than most of the
theorems it certifies.

**Their reservations.** The metatheory is small: one propositional
independence result, one reverse-math equivalence, two categoricity results.
There is no proof theory proper (no cut elimination, no normalization, no
ordinal analysis), no model theory (no structures, no satisfaction, no
compactness), no computability theory (no formal machine model, no halting
problem, no reducibility), and no set theory. The kernel's own metatheory is
unaddressed: nobody has proved this type theory consistent, or normalizing, or
sound relative to a model — which is normal for a proof assistant and is the
question their field would actually want answered.

## What they would say is missing

- **Computability.** A machine model, the halting problem, and the recursion
  theorem. The library has `Nat.cantor_no_fixed_point`, which is the
  diagonalization, and does not connect it to undecidability.
- **Gödel's incompleteness theorems.** Currently `open` in the ledger with
  nothing behind them. Needs arithmetization of syntax and a provability
  predicate — a large, well-mapped project.
- **Model theory.** Structures, satisfaction, soundness and completeness for
  first-order logic, compactness.
- **Proof theory proper.** Cut elimination for a sequent calculus, and
  normalization for the λ-calculus underneath the kernel.
- **More reverse mathematics.** The EM/LNP result is one point. The
  interesting picture is a map: which classical principles over this kernel
  are equivalent to which others (LPO, Markov's principle, the fan theorem,
  dependent choice).
- **Ordinals and set theory**, which most of the above eventually wants.

## The blocker

**Nothing external, which is unusual in this department.** Every item on the
list is ordinary work over the existing kernel, and much of it is exactly the
kind of finite, syntactic, decidable material this kernel is best at.

The one genuine constraint is that a *metatheory of this kernel* cannot be
done inside this kernel, by Gödel. Any consistency or normalization result has
to be relative — proved in a stronger system, or proved for a fragment. That
is a scoping decision, not an obstruction, and it should be written down
before anyone starts.

## Next five, in their priority order

- [ ] **1. Extend the reverse-mathematics map.** Add LPO, Markov's principle,
      and the limited principle of omniscience alongside the existing EM/LNP
      equivalence, each as a hypothesis rather than an axiom. Their view: you
      have one calibration point and the technique to make it a map, and this
      is the most distinctive mathematics in the library.
- [ ] **2. A computability layer.** A register machine or μ-recursive
      functions over ℕ, the halting problem via the existing
      `cantor_no_fixed_point` diagonalization, and undecidability of
      first-order validity — which is already `open` in the ledger.
- [ ] **3. First-order model theory: structures, satisfaction, and
      soundness**, extending the IPC work from propositional to predicate
      logic. Completeness is the harder half and needs a choice principle,
      which makes it a good test of the classical-axiom policy.
- [ ] **4. Arithmetization of syntax, toward Gödel I.** Large, well-mapped,
      and the single result whose presence would most change how the library
      is read. Their view: worth starting even if it takes a year.
- [ ] **5. Write down the kernel's own metatheoretic status.** What is assumed
      about this type theory, what has been checked (the Lean kernel
      cross-check, the guard suites, the divergence in ADR-0517), and what
      would be needed for a relative consistency result. An ADR, not code.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: kernel with strict positivity, universe guards, well-founded recursion, quotient package without `Quot.sound`, no funext/propext/choice. Metatheory: IPC EM-unprovability with audited encoding, EM ↔ unrestricted LNP, ℕ and ℤ categoricity, Cantor. 2,487 proved facts, empty footprint. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 5 landed** (roadmap W0-4): ADR-1600 records the kernel's metatheoretic status. Trusted base measured at 5,526 function-body lines across 9 files by call-graph closure from the four admission gates. Three soundness guards demonstrated firing in an isolated copy; a fourth, the nested-inductive phantom-parameter domain check, kills zero tests and is recorded as an open finding. No consistency or normalization result, and the ADR says why none can be internal. | `8b4f277d4` |

## How to re-measure

```sh
# the trusted base, read from the kernel and not from prose
cargo run --release -p axeyum-lean-kernel --example footprint_closure_audit

# the guard suites (32 kernel integration suites; confirm a NONZERO count)
scripts/check-kernel-suites.sh --list
scripts/check-kernel-suites.sh --no-lib

grep -rhoE '"Nat\.(lnp|em)[A-Za-z_]*"|ipc_[a-z_]+' crates/axeyum-lean-kernel/src/ \
  | tr -d '"' | sort -u
```

## Related

- [09-category-theory.md](09-category-theory.md) — the categoricity results,
  read as universal properties
- [11-applied-and-computational.md](11-applied-and-computational.md) — the
  proof-producing search side
- [ADR-0517](../research/09-decisions/adr-0517-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md)
  — the measured elaborator/kernel divergence
