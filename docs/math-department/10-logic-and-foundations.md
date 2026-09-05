# 10 — Logic and foundations

Reviewer: a proof theorist, with an interest in reverse mathematics
Verdict, 2026-09-04: **the most interested reviewer in the department, and for reasons the other eleven do not share**
Last measured: 2026-09-04 at `1856cdb3c`

> "Everyone else is reviewing your theorems. I am reviewing your kernel, and
> your kernel is the paper."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

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

- [x] **1. Extend the reverse-mathematics map.** *Done 2026-09-04: LPO, WLPO, Markov, LLPO.* Add LPO, Markov's principle,
      and the limited principle of omniscience alongside the existing EM/LNP
      equivalence, each as a hypothesis rather than an axiom. Their view: you
      have one calibration point and the technique to make it a map, and this
      is the most distinctive mathematics in the library.
- [x] **2. A computability layer.** *Done 2026-09-04, scoped precisely.* A register machine or μ-recursive
      functions over ℕ, the halting problem via the existing
      `cantor_no_fixed_point` diagonalization, and undecidability of
      first-order validity — which is already `open` in the ledger.
- [x] **3. First-order model theory: structures, satisfaction, and*** — *done 2026-09-05, with soundness and consistency.* **
      soundness**, extending the IPC work from propositional to predicate
      logic. Completeness is the harder half and needs a choice principle,
      which makes it a good test of the classical-axiom policy.
- [ ] **4. Arithmetization of syntax, toward Gödel I.** Large, well-mapped,
      and the single result whose presence would most change how the library
      is read. Their view: worth starting even if it takes a year.
- [x] **5. Write down the kernel's own metatheoretic status.** *Done 2026-09-04, ADR-1600.* What is assumed
      about this type theory, what has been checked (the Lean kernel
      cross-check, the guard suites, the divergence in ADR-0517), and what
      would be needed for a relative consistency result. An ADR, not code.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: kernel with strict positivity, universe guards, well-founded recursion, quotient package without `Quot.sound`, no funext/propext/choice. Metatheory: IPC EM-unprovability with audited encoding, EM ↔ unrestricted LNP, ℕ and ℤ categoricity, Cantor. 2,487 proved facts, empty footprint. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 5 landed** (roadmap W0-4): ADR-1600 records the kernel's metatheoretic status. Trusted base measured at 5,526 function-body lines across 9 files by call-graph closure from the four admission gates. Three soundness guards demonstrated firing in an isolated copy; a fourth, the nested-inductive phantom-parameter domain check, kills zero tests and is recorded as an open finding. No consistency or normalization result, and the ADR says why none can be internal. | `8b4f277d4` |
| 2026-09-04 | **Next Five item 1 landed** (roadmap W1-9): the reverse-mathematics map now carries LPO, WLPO, Markov's principle and LLPO over ℕ with six proved implications, including the converse half `WLPO ∧ MP → LPO`, all with empty footprints and every principle spelled inline so no new `Definition` was needed. Four order theorems over ℝ on an explicit `OrderDecision` hypothesis prove conclusions `creal.rs`'s own field docs record as unavailable. Every **separation** is cited rather than claimed, because a separation needs a model of the kernel and not a term in it — which is exactly what ADR-1600 said about this kernel's metatheory. | `80aa8e52c`; `omniscience` 14 passed, `creal::` 236 |
| 2026-09-04 | **Next Five item 2 landed** (roadmap W2-14): a step-function register machine over ℕ and `Nat.RM.self_halting_not_decidable` — no total `H : Nat → Bool` is correct in both directions about whether `diagStep H` halts from `1`. Footprint 0. **Scoped exactly as this reviewer would demand**: a genuine constructive refutation for the lane's own machine, explicitly *not* Turing's theorem for a fixed universal machine, since there is no program-as-data encoding, no s-m-n, no recursion theorem. The brief asked to route the contradiction through `Nat.cantor_no_fixed_point`; the lane built that route, found the two cases are Π₁- and Σ₁-shaped so the shared fixed point is decorative rather than load-bearing, and shipped a direct proof while **saying so in ADR-1611 instead of claiming reuse**. Undecidability of first-order validity correctly stays `open`. | `e15d807c8`; `nat_prelude::` 478 passed pre-merge |
| 2026-09-05 | **A kernel divergence from official Lean, found by a gate**: this kernel admits `PSigma` at `Sort (max u v)` and handles it soundly (no large elimination, `Prop`-only recursor); Lean 4.34.0-rc1 refuses that declaration outright and requires `Sort (max 1 u v)`. `real_lean_shared_prelude_crosscheck` caught it; `PSigma` now carries Lean's level, pinned by a probe that declares the bare form into a scratch kernel and counts its recursor's universe parameters. Also from the same lane: the constructor-field universe guard (ADR-1495) was never the reason dependent pairs were absent — `u ≤ max u v` discharges symbolically. | `c0054fd3b` |
| 2026-09-05 | **Item 7's public corpus was run, both halves, with the control.** The corpus is `leanprover/lean-kernel-arena`; the `189 / 121 / 62 / 6` figures this file and the requirements doc carry are stale -- it is **204 tests, 118 accept / 73 reject / 13 either** at `abc55357`. On its 186-case published tarball this kernel scores **108/113 accepts and 70/73 rejects** (69/73 on the run that found the one defect this lane closed, duplicate universe binders); the in-tree `parse-only` control (the same reader with the trusted gate's verdict discarded) scores **110/113 and 21/73**, so 21 of the reject half is earned by the reader and **49 by the trusted gate**. Eight divergences are published in a gated `docs/plan/lean-divergences.md` in lean4lean's shape. Two §4.6 "known gaps" are settled: K-like reduction is present and the `rec-k-lie` soundness cases are rejected; unit-like defeq is absent and blocks exactly two cases, not "a block" of them. **What this run does NOT close**: `level-imax-leq`, the nanoda `imax`-leq soundness bug §4.5 records as UNKNOWN for us, is rejected on an unrelated recursor K-flag mismatch, so its own property is still untested by the corpus. | ADR-1663; `python3 scripts/check-kernel-conformance.py` |
| 2026-09-05 | **Item 3 landed** (roadmap W3-6, ADR-1636): `FO.*`, 76 axiom-free declarations — de Bruijn syntax over a data signature, structures, `Prop`-valued Tarski satisfaction with the substitution lemma, a natural-deduction calculus with the eigenvariable condition, `FO.soundness`, and `FO.consistency` via the ℕ model. The `Prop`-valued design made soundness cheaper than the propositional `ipc` version. Completeness is open; the classical form is the wrong target for this kernel, so the next step is constructive Kripke completeness. | `8315ed024`; `fo_` 40 passed in the lane |

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
