# 10 — Logic and foundations

Reviewer: a proof theorist, with an interest in reverse mathematics
Verdict, re-measured 2026-09-06: **still the most interested reviewer in the department — and now also the one whose shelf moved the most in two days**
Last measured: 2026-09-06 at `1de0edfc6`

> "Everyone else is reviewing your theorems. I am reviewing your kernel, and
> your kernel is the paper."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).
>
> **Re-measured 2026-09-06 at `1de0edfc6`, and the gap grew.**
> `scripts/check-fact-characterisation.py --report` now prints
> `uncharacterised_share=0.5932` — 1,093 curated of 2,687 proved facts, so the
> ledger characterises **41%**, not 38%. The 430 was not reproduced with the
> audit's own script; two independent recounts against the 4,839-row index give
> **620** index theorems whose name appears nowhere in any fact file and
> **973** with no fact naming them as its `kernel_declaration`, out of 3,319.
> Neither number is the audit's, and both are larger than the audit's.

> **Retired 2026-09-06 (ADR-1674):** the 430 is not reproducible by its own
> method - three later readings give 599, 620, 721 and 973 on three different
> denominators. The measured, gated figure is **721 of 3,079 registered
> kernel theorem names uncovered**, ratcheted by `gen-ledger-coverage`.

## The persona

Cares about which axioms a theorem needs, what a proof system can and cannot
derive, and whether a formal development means what it claims. Reads
`#print axioms` before reading the theorem. Regards a large library proved
from strong axioms as less interesting than a small one whose exact strength
is known. Their instinct on any formalization is to ask what the *trusted base*
is and whether anyone has checked it.

## What the library has today

**Two things: a kernel with an unusually explicit trusted base, and — as of
this week — a body of metatheory that is no longer small.**

**The kernel.** A Lean-compatible type theory with:

- inductive types with strict positivity checking, mutual and nested groups,
  and nested-inductive elimination
- universe polymorphism with a bound-parameter guard, and a constructor-field
  universe guard (ADR-1495)
- recursors, ι-reduction, K-like reduction, structure eta, projections with
  their own congruence and reduction rules
- well-founded recursion (`WellFounded.fix`, `Acc.rec`) with `fix_eq`
- Lean's four-declaration quotient package (`Quot`, `Quot.mk`, `Quot.lift`,
  `Quot.ind`) — **without `Quot.sound`**. Measured nuance: `PACKAGE_LEN = 4`
  in `quotient.rs` and the package is admitted transactionally by
  `Kernel::add_quotient_package`, but **no shipped prelude admits it** — the
  only callers are that module's own tests, `kernel_differential`, and
  `axeyum-lean-import`. So the retrieval index reports `quot=0`, which is a
  fact about the preludes and not about the kernel.
- **no `funext`, no `propext`, no choice, no excluded middle.** Measured, not
  asserted: the whole-index axiom census is **30**, and every one of the 30 is
  an `AxReal.*` field of the axiomatized real prelude (`AxReal.add_assoc`,
  `AxReal.sq_nonneg`, …). `opaque=0`.
- `Kernel::axiom_footprint`, read from the environment, as the only admissible
  source of an axiom claim

Each guard has its own integration suite: `strict_positivity`,
`declaration_universe_params_must_be_bound`,
`lambda_binder_domain_must_be_a_type`, `prop_large_elim_soundness` and
`prop_large_elim_derives_false`, `nested_phantom_parameter_soundness`,
`k_like_reduction`, `structure_eta`, `projection_congruence` — all nine still
registered. **The suite count in this file was stale**: it said 32;
`scripts/check-kernel-suites.sh --list` reports **53** suites, 35 in the push
half and 18 owned by `scripts/check-lean-gate.sh`. The kernel is also
cross-checked against official Lean's own kernel on exported `lean4export`
streams, and a **named, measured divergence** between Lean's elaborator and
Lean's kernel is recorded rather than worked around (ADR-0517, amended
2026-09-03).

**The trusted core, re-measured.** `scripts/check-kernel-trusted-core.py` at
`1de0edfc6`: **5,545 trusted function lines, 256 functions, 9 files**, out of
482,185 function lines in the crate, behind **four** admission gates
(`Kernel::add_declaration`, `Kernel::add_inductive_group`,
`Kernel::restore_nested_inductive_group`, `Kernel::add_quotient_package`).
ADR-1600 measured 5,526 of 378,049 on 2026-09-04; the ratchet's ceiling is
5,900 and the run reports `ok: 5 guards, 0 failures`. The denominator grew by
104k lines and the numerator by 19.

**The metatheory.** This is the section that changed.

| result | detail | measured |
|---|---|---|
| **Excluded middle is not derivable in IPC** | `ipc_excluded_middle_not_provable`, with the **eleven** `Provable` constructors (`ax_head`, `weaken`, `imp_intro`, `imp_elim`, `and_intro`, `and_elim1`, `and_elim2`, `or_intro1`, `or_intro2`, `or_elim`, `bot_elim`) read out of the kernel environment and shown to be exactly the intuitionistic natural-deduction rule set, plus a Heyting-algebra countermodel | **22** `ipc_*` declarations in the index. **[correction]** this file previously named `ipc_heyting`, `ipc_himp`, `ipc_le_join` and `ipc_le_meet` as declarations; they are Rust module and builder names. The countermodel theorem in the environment is `ipc_heyting_join_not_ne_top`, and the non-degeneracy control `ipc_heyting_meet_not_countermodel_ne_top` is a test, not a declaration. `ipc_ctx_meet` and `ipc_soundness` are real, and were the positive control that makes the other four an absence rather than a typo. |
| **EM ↔ the unrestricted least-number principle, and a four-principle omniscience map** | `Nat.em_implies_lnp`, `Nat.lnp_unrestricted_implies_em`, the decidable and bounded forms (`Nat.lnp_decidable`, `Nat.lnp_bounded_search`, `Nat.lnp_of_pointwise_decision`), and LPO/WLPO/Markov/LLPO: `Nat.em_implies_lpo`, `Nat.lpo_implies_wlpo`, `Nat.lpo_implies_markov`, `Nat.lpo_implies_llpo`, `Nat.wlpo_and_markov_imply_lpo`, `Nat.lnp_unrestricted_implies_lpo` | **11 declarations**, each `--name`-confirmed in the index |
| **Computability** | `Nat.RM.runFuel`, `Nat.RM.Halts`, `Nat.RM.diagStep`, `Nat.RM.self_halting_not_decidable` — no total `H : Nat → Bool` is correct in both directions about whether `diagStep H` halts from `1` | **4 declarations**; exactly one name in the 4,839-row index contains "halting" |
| **First-order logic: syntax, semantics, soundness, consistency** | de Bruijn `FO.Term`/`FO.Formula` over a data signature, `FO.Structure`, `Prop`-valued Tarski satisfaction with `FO.sat_subst`, a **seventeen**-rule natural-deduction calculus with the eigenvariable condition and the Leibniz rule (`FO.Provable.eqf_subst`), `FO.soundness`, `FO.consistency` | part of the 141 below |
| **Arithmetization of syntax** | `FO.Code.pair`/`unpair` (an anti-diagonal pairing, deliberately not `Nat.pair`), `FO.Term.code_injective`, `FO.Formula.code_injective`, `FO.Term.decode_code` and `FO.Formula.decode_code` (fuel on the left), `FO.Code.substCodeAux_commutes`, `FO.Code.isFormulaCodeAux_code`, and the arithmetic half of the diagonal lemma `FO.Code.diagAux_code` | part of the 141 below |
| **Robinson's Q, and Q with order** | `FO.Q` as an `FO.Context` with `FO.Q.natModels` and hence `FO.Q.consistency`; `FO.Q.add_numeral`, `FO.Q.mul_numeral`, `FO.Q.pair_represented` (existence half); `FO.Qle` — six order axioms — with `FO.Qle.natModels` and `FO.Qle.consistency` | `fo_robinson_inventory` **132**, `fo_order_inventory` **9** → **141 `FO.*` declarations, every row `axioms=0`** |
| **ℕ is a natural-numbers object** | `Nat.Peano.induction`, `injective`, `surjective`, `iter_unique`, `iter`, `iter_zero`, `iter_succ`, `initial`, `categorical`, `succ_injective`, `zero_ne_succ` — Dedekind categoricity with uniqueness of iteration | 11 declarations. **[correction]** this file said `Nat.Peano.rec_unique`; that name does not exist. `Nat.Peano.iter_unique` does, and `Int.Characterization.rec_unique` does — the same-kind positive control for the absence. |
| **ℤ is characterized categorically** | `Int.Characterization.categorical`, `iso`, `rec_unique` | 25 declarations under `Int.Characterization` |
| **Cantor** | `Nat.cantor_no_fixed_point` | present |
| classical propositional logic, as consequences | Peirce's law, double-negation elimination, De Morgan in both directions, disjunctive syllogism, EM's irrefutability — each proved *from* EM as a hypothesis, never from an axiom | ADR-1601 |

Open, and honestly marked as such — all seven still `epistemic_status: open`
at `1de0edfc6`: `F:godel-first-incompleteness`, `F:fo-first-incompleteness`
(the hypothesis-carrying form), `F:fo-diagonal-lemma`, `F:fo-formula-decoder`
(the *self*-fuelled decoder; the fuel-additive round trip is proved and is a
different type), `F:fo-completeness-henkin`, `F:fol-validity-undecidable`, and
`F:continuum-hypothesis-independent`.

## Their verdict

**Two days ago the metatheory was four results. It is now a first-order
logic.** `FO.*` is 141 axiom-free declarations covering syntax, structures,
Tarski satisfaction, a seventeen-rule calculus, soundness, consistency, a
Gödel numbering with both injectivity halves and a proved decode round trip,
Robinson's Q with a model and a consistency proof, and Q with order. That is
not a gesture at incompleteness; it is the standard construction, in order,
with each piece admitted by the trusted gate and each one measured at
`axioms=0`. This reviewer would say the shelf went from "a small body of
genuine metatheory" to "the part of this library a logician would actually
read" inside 48 hours.

**The reverse-mathematics map is real, and it is still the most distinctive
thing here.** Eleven declarations, principles carried as hypotheses and
discharged at use, footprints empty. And the lane that built it **cited every
separation rather than claiming one**, because a separation needs a model of
the kernel and not a term in it — which is exactly what ADR-1600 says about
this kernel's metatheory. That restraint is worth more to this reviewer than
the six implications.

**The IPC unprovability result is more than a formality.** The eleven
`Provable` constructors are read out of the kernel environment and shown to be
exactly the intuitionistic natural-deduction rules, the `Formula` type is shown
to have no `top` constructor, strict positivity is checked, and the checker
discriminates in both directions. That is a metatheorem about a formal system
with the encoding audited, rather than a statement about whatever the author
happened to write down.

**The trusted base is still the headline, and it is still defensible.** 2,687
proved facts, **2,584 of them carrying an empty `axiom_footprint`**; the 103
non-empty ones are almost entirely CAS-internal residue labels
(`cas.exact-rational-polynomial-normal-form` and its kin, ADR-0601), not
kernel axioms. The kernel's own axiom census is 30 and all 30 are `AxReal.*`.
`footprint_closure_audit` reports
`theorems_with_empty_narrow_and_nonempty_widened_trusted_footprint = 0`.

**Their reservations, updated — three of the four are now narrower and one is
worse.**

- *Proof theory proper is still entirely absent*, and this is now the
  conspicuous hole. Zero declarations matching `cut_elim` in a 4,839-row
  index; the only `normaliz` hits are `Rat.normalize*`, which is arithmetic.
  No sequent calculus, no cut elimination, no normalization theorem for the
  λ-calculus underneath the kernel.
- *Model theory is half-built, not absent.* Structures, satisfaction and
  soundness landed. Completeness is `open` on purpose (the classical
  Lindenbaum route needs EM, which ADR-1601 forbids as an axiom), and
  compactness has nothing — the four `compact` names in the index are
  `Metric.Compact*`, Bishop compactness of a metric space, a different notion
  in a different field.
- *Computability is scoped honestly and is thin.* Four declarations, a
  constructive refutation for the lane's own machine, and ADR-1611 saying in
  as many words that it is **not** Turing's theorem for a universal machine.
  Zero `Turing`, zero `reducib` in the index. Undecidability of first-order
  validity correctly stays `open`.
- *Set theory and ordinals: zero.* Not one declaration in the index whose name
  contains `ordinal`, and no `Set` namespace at all.
- *The kernel's own metatheory is still unproved*, which ADR-1600 says is the
  right answer and says why. Nobody has proved this type theory consistent, or
  normalizing, or sound relative to a model. Normal for a proof assistant, and
  the question their field would actually want answered.
- **Worse than on 2026-09-04:** the ledger's coverage of the kernel. 620 of
  3,319 index theorems are never named in any fact file, and 973 have no fact
  claiming them as a kernel declaration. On the audit's smaller index the
  figure was 430. This reviewer's whole method is *read the ledger, then read
  the footprints*, and the ledger is falling further behind the kernel.

## What they would say is missing

- **The diagonal lemma at the provability level, then Gödel I.** Everything
  under it is now measured rather than guessed: `FO.Code.diagAux_code` gives
  the arithmetic identity, `FO.Provable.eqf_subst` gives the Leibniz rule,
  `FO.Qle` gives a theory with order. What is missing is representability of
  the diagonal function in `FO.Qle` — the uniqueness half — plus
  `FO.Formula.numeral` and a provability predicate. Sized in ADR-1669.
- **Completeness, constructively.** Kripke completeness, not Henkin: the
  classical statement is the wrong target for this kernel and
  `F:fo-completeness-henkin`'s own notes say so.
- **Compactness.** Nothing in the index. It is the other half of what makes a
  model theory a model theory.
- **Proof theory proper.** Cut elimination for a sequent calculus, and
  normalization for the λ-calculus underneath the kernel. This is now the only
  one of the reviewer's original five that has not been started at all.
- **A universal machine, s-m-n, and the recursion theorem**, which is what
  turns `Nat.RM` from one clever diagonal into computability theory — and what
  `F:fol-validity-undecidable` needs before it can stop being `open`.
- **More reverse mathematics.** LPO/WLPO/Markov/LLPO is a map with four
  points. The fan theorem, dependent choice, and bar induction are the obvious
  next ones.
- **Ordinals and set theory**, which most of the above eventually wants.
- **`shape_search` cannot see any of this field's newest work.** The retrieval
  index builds `logic, nat, axreal, integer, ipc, rat, characterization,
  string` plus the eight constructed groups, and **zero** `FO.*` rows appear
  in a 4,839-row dump. `footprint_closure_audit` likewise builds six groups
  and neither `ipc` nor `fo`. So the two tools this file most depends on are
  blind to 141 of its declarations, and the only way to measure them is the
  four `fo_*_inventory` examples.

## The blocker

**Nothing external, which is unusual in this department.** Every item on the
list is ordinary work over the existing kernel, and much of it is exactly the
kind of finite, syntactic, decidable material this kernel is best at. Checked
2026-09-06: no live lane worktree carries an `fo_*` commit ahead of main, so
nothing on this shelf is waiting on unlanded work either.

The one genuine constraint is that a *metatheory of this kernel* cannot be
done inside this kernel, by Gödel. Any consistency or normalization result has
to be relative — proved in a stronger system, or proved for a fragment. That
is a scoping decision, not an obstruction, and ADR-1600 wrote it down.

The one genuine *measurement* constraint is the retrieval blindness above. It
is not mathematics and this reviewer says so, but a field whose declarations
no index can find is a field whose absences cannot be checked — and this
re-measurement had to correct three name claims for exactly that reason.

## Next five, in their priority order

All five of the reviewer's original items are landed or measurably in
progress. The list is kept for the record; the reissued list follows.

- [x] **1. Extend the reverse-mathematics map.** *Done 2026-09-04: LPO, WLPO,
      Markov, LLPO. Re-confirmed 2026-09-06 — 11 declarations, each
      `--name`-matched in the index.* Their view: you have one calibration
      point and the technique to make it a map, and this is the most
      distinctive mathematics in the library.
- [x] **2. A computability layer.** *Done 2026-09-04, scoped precisely.
      Re-confirmed 2026-09-06 — 4 declarations, and
      `Nat.RM.self_halting_not_decidable` is the only name in the whole index
      containing "halting".* A register machine over ℕ and the halting
      problem; undecidability of first-order validity correctly still `open`.
- [x] **3. First-order model theory: structures, satisfaction, and
      soundness.** *Done 2026-09-05, with consistency. `fo_soundness_inventory`
      reports 77 declarations on that chain today, all `axioms=0` — 76 at
      landing, plus the Leibniz rule the next slice appended.* Completeness is
      the harder half and stays open by design.
- [~] **4. Arithmetization of syntax, toward Gödel I.** *Four slices landed in
      three days. Measured 2026-09-06: `fo_code_inventory` 61 arithmetization
      declarations, `fo_robinson_inventory` 132, `fo_order_inventory` 9 — 141
      `FO.*` in total, every one `axioms=0`. Numbering, injectivity, decoder,
      round trip, `substCode` commuting, the Leibniz rule, the arithmetic
      diagonal identity, Q with its ℕ model and consistency, numeral
      arithmetic, pairing's representability (existence half), and Q with six
      order axioms are all on main. Still open and named: the uniqueness half
      of representability, `FO.Formula.numeral`, the provability predicate,
      the diagonal lemma, Gödel I.* Their view: worth starting even if it takes
      a year — and it has moved faster than that estimate by an order of
      magnitude.
- [x] **5. Write down the kernel's own metatheoretic status.** *Done
      2026-09-04, ADR-1600. Re-measured 2026-09-06: 5,545 trusted function
      lines / 256 functions / 9 files, ceiling 5,900,
      `scripts/check-kernel-trusted-core.py` → `ok: 5 guards, 0 failures`.*

## The next five, reissued 2026-09-06

- [ ] **1. Uniqueness of representation in `FO.Qle`, then the diagonal lemma.**
      The single blocking step, and ADR-1669 has already sized it: the bound
      `m = 2·pair(a,b)` is symbolic, so the case disjunction has symbolically
      many disjuncts and eliminating it needs a uniform-family eliminator that
      none of the four slices has built. Their reason for ranking it first:
      every remaining Gödel item is behind this one and nothing else is.
- [ ] **2. The negative numeral twin and the bounded case split.**
      `a ≠ b → Qle ⊢ ¬(ā = b̄)`, sized at 400–500 lines with **no new kernel
      machinery** after ADR-1669 withdrew ADR-1651's five-helper estimate
      (`FO.Provable.weaken` lifts a `Qle` derivation into `cons φ Qle` in one
      step). The case split carries an unmeasured risk the lane flagged
      honestly: no derivation in this group has used `all_intro` at a
      non-empty context, and whether `FO.Context.shift FO.Qle` reduces back to
      `FO.Qle` must be measured with a throwaway derivation first.
- [ ] **3. Teach `shape_search` and `footprint_closure_audit` the `fo_*` and
      `ipc_*` groups.** Not this reviewer's mathematics, and they say so, but
      141 declarations invisible to the retrieval index is how false absences
      are manufactured. The group list should be derived from the build calls,
      not hand-written.
- [ ] **4. Cut elimination for a sequent calculus.** The only original ask
      with nothing under it. Zero `cut_elim` in a 4,839-row index, and the
      `FO.Provable` natural-deduction calculus is the obvious thing to state
      it against. Their view: this is the result that would make the
      metatheory a *proof* theory rather than a model theory with a numbering.
- [ ] **5. Constructive Kripke completeness.** `F:fo-completeness-henkin` is
      `open` with the right reason recorded (Lindenbaum needs EM, ADR-1601
      forbids the axiom). Kripke completeness is the form this kernel can
      actually hold, and it would close the last gap in the model-theory half
      without touching the classical-axiom policy.

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
| 2026-09-05 | **Item 4, first slice** (roadmap W3-7, ADR-1640): Gödel numbering of the first-order syntax landed this morning — an anti-diagonal pairing built under `FO.Code` (not `Nat.pair`, whose round trip is a held-out family, and whose inverse would need `sqrt`), `code_injective` for terms and formulas, a fuel-indexed decoder, and `substCode`/`isFormulaCode` as computable functions; 48 axiom-free declarations. The decode round trip and therefore the diagonal lemma did not land, but the sizing moved in the right direction twice while building the decoder. The Leibniz equality rule for `FO.Provable` remains the other prerequisite for Gödel I. | `87de47fd2`; `fo_` 68 passed in the lane |
| 2026-09-05 | **Item 4, second slice** (roadmap W3-7, ADR-1648): the decode round trip in the fuel-on-the-left form the first lane predicted, the commuting lemma for substitution codes, the Leibniz equality rule for the calculus with soundness kept green (cheaper than ADR-1636 estimated), and the arithmetic identity `diag ⌜p⌝ = ⌜p(⌜p⌝)⌝`; 13 axiom-free declarations. One prediction from the first lane, that a formula's size is bounded by its code, is false and is now pinned false. The provability-level diagonal lemma waits on representability in Q, which is a strand of work rather than a step. | `97e097346`; `fo_` 81 passed in the lane |
| 2026-09-06 | **Item 4, third slice** (roadmap W3-7, ADR-1651): Robinson's Q written down as a context with a model in ℕ, so Q is consistent by soundness; addition and multiplication of numerals provable in Q; the pairing function's graph representable in Q (existence). One real obstruction found: uniqueness of the representing value is not provable in Q without order axioms, so the next slice's theory must be Q plus order. A build-plumbing obstruction also fell: no kernel could previously hold both the calculus and the numbering. | `0450aa826`; `fo_` 99 passed in the lane |
| 2026-09-06 | **Q with order** (roadmap W3-7, ADR-1669): Robinson's Q extended by six order axioms with the naturals as a model, hence consistent; 9 axiom-free declarations. A mutation control showed the model theorem only checks that the supplied witness fits, not that the axiom is true, so one shape test is the sole guard against a self-consistent wrong axiom. The negative numeral twin, the bounded case split, uniqueness of representation and the diagonal lemma are sized in order; Gödel I stays open with representability as a hypothesis. | `1a74de1b7`; `fo_` family 108 passed in the lane |
| 2026-09-06 | **Whole file re-measured against main.** The verdict, "what the library has", "what is missing", "the blocker" and the Next Five were rewritten from measurements rather than from the 2026-09-04 reading. Numbers that moved: proved facts 2,487 → **2,687** (2,584 with an empty `axiom_footprint`; the 103 non-empty are CAS residue labels, not kernel axioms); trusted core 5,526 / 378,049 → **5,545 / 482,185**; kernel integration suites **32 → 53**; ledger characterisation 38% → **41%**, and the uncovered-theorem gap **430 → 620 or 973** depending on how "covered" is read. New: **141 `FO.*` declarations, all `axioms=0`**, from the four `fo_*_inventory` examples, which are the only tools that can see them. Three name corrections: `Nat.Peano.rec_unique` does not exist (`iter_unique` does), and `ipc_heyting` / `ipc_himp` / `ipc_le_join` / `ipc_le_meet` are Rust builders rather than declarations (`ipc_heyting_join_not_ne_top` is the real countermodel theorem). Confirmed absent with same-index positive controls: `cut_elim`, `ordinal`, `Turing`, `reducib`, and logical compactness. No live lane worktree carries `fo_*` work ahead of main. | measured at `1de0edfc6` |

## How to re-measure


**Caveat on every ABSENT claim in this file, and its expiry (2026-09-06).**
These measurements were taken with a retrieval index that built 17 of the
kernel's 31 prelude builders and indexed no `FO.*`, no `Metric.prod*` and no
list prelude, so an ABSENT verdict in those three areas was a statement about
the instrument. **That gap is now closed** (`a4848a970`, ADR-1672): coverage is
31 of 31, the group list is derived from one table, and a census test fails
when the table and the builder inventory diverge. The same gap had been
manufacturing findings downstream — `check-trust-closure.py` reported 21
facts as having absent subjects that exist and are proved; building the
missing preludes took that to 0. **Any ABSENT claim in this file that touches
first-order logic, the product metric or lists predates the fix and should be
re-measured before it is quoted.** Claims outside those three areas were
unaffected and each was paired with a positive control in the same
invocation.
**The two general kernel tools cannot see this field's newest work.**
`shape_search` builds `logic, nat, axreal, integer, ipc, rat,
characterization, string` (plus eight constructed groups under
`--include-constructed`) and `footprint_closure_audit` builds six; **neither
builds any `fo_*` group**, so an `FO.*` query against either returns
`UNANSWERABLE` or a false `ABSENT`. Use the inventories.

```sh
# 1. The FO surface -- the only tools that can see it. Each is built to FAIL
#    ON ABSENCE, so a named filter matching nothing exits non-zero.
cargo run -q --release -p axeyum-lean-kernel --example fo_order_inventory
#   -> 9 FO.Qle declarations, every row axioms=0
cargo run -q --release -p axeyum-lean-kernel --example fo_robinson_inventory
#   -> 132 FO declarations, every row axioms=0   (132 + 9 = 141 total)
cargo run -q --release -p axeyum-lean-kernel --example fo_soundness_inventory   # 77
cargo run -q --release -p axeyum-lean-kernel --example fo_code_inventory        # 61

# a single fact's own check, in the form the fact files carry
cargo run -q --release -p axeyum-lean-kernel --example fo_order_inventory \
  -- FO.Qle.consistency --exact --require-axiom-free

# 2. The trusted base, read from the kernel and not from prose
python3 scripts/check-kernel-trusted-core.py
#   -> 4 admission gates, 256 trusted functions, 5545 of 482185 lines,
#      ceiling 5900, "ok: 5 guards, 0 failures"
cargo run --release -p axeyum-lean-kernel --example footprint_closure_audit
#   -> HEADLINE: ..._nonempty_widened_trusted_footprint = 0
#      NOTE: builds logic/nat/axreal/integer/rat/string only. Not ipc, not fo.

# 3. The guard suites. 53, not the 32 this file used to claim: 35 in the push
#    half, 18 owned by scripts/check-lean-gate.sh. Confirm a NONZERO count.
scripts/check-kernel-suites.sh --list
scripts/check-kernel-suites.sh --no-lib

# 4. The reverse-mathematics map and the IPC package, by EXACT name.
#    --const asks where a constant OCCURS; --name is the existence question.
#    Dump the index once and search it offline -- each query otherwise pays a
#    ~10 s (or ~150 s with --include-constructed) environment build.
./target/release/examples/shape_search --include-constructed \
  --name-contains '' --limit 99999 > "$AXEYUM_AGENT.decls.txt"
grep -cE '^MATCH +ipc' "$AXEYUM_AGENT.decls.txt"                    # 22
grep -oE 'MATCH +Nat\.(em|lnp|lpo|wlpo|markov|llpo)[A-Za-z_]*' \
  "$AXEYUM_AGENT.decls.txt"                                         # 11
grep -oE 'MATCH +Nat\.RM\.[A-Za-z_]*' "$AXEYUM_AGENT.decls.txt"     # 4
grep -cE '^MATCH +FO\.' "$AXEYUM_AGENT.decls.txt"                   # 0 -- see above
./target/release/examples/shape_search --kind axiom --limit 100     # 30, all AxReal.*

# 5. The ledger side
python3 scripts/count-landmark-facts.py       # total=2963 proved=2687
python3 scripts/check-fact-characterisation.py --report
#   -> uncharacterised_share=0.5932
```

## Related

- [09-category-theory.md](09-category-theory.md) — the categoricity results,
  read as universal properties
- [11-applied-and-computational.md](11-applied-and-computational.md) — the
  proof-producing search side
- [ADR-0517](../research/09-decisions/adr-0517-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md)
  — the measured elaborator/kernel divergence
- [ADR-1600](../research/09-decisions/adr-1600-the-kernels-metatheoretic-status-what-is-trusted-and-what-is-not.md)
  — what is trusted and what is not
- [ADR-1601](../research/09-decisions/adr-1601-classical-logic-enters-as-a-hypothesis-not-as-an-axiom.md)
  — classical logic enters as a hypothesis
- [ADR-1636](../research/09-decisions/adr-1636-first-order-model-theory-lands-de-bruijn-and-the-eigenvariable-condition-is-a-shift.md),
  [ADR-1640](../research/09-decisions/adr-1640-godel-numbering-gets-its-own-pairing-because-nat-pair-is-a-blind-family.md),
  [ADR-1648](../research/09-decisions/adr-1648-the-round-trip-carries-its-fuel-and-leibniz-needed-no-induction.md),
  [ADR-1651](../research/09-decisions/adr-1651-robinson-q-is-a-context-and-the-two-fo-chains-must-share-one-syntax.md),
  [ADR-1669](../research/09-decisions/adr-1669-the-order-symbol-was-already-in-the-signature-so-q-plus-order-is-six-axioms-not-a-new-structure.md)
  — the five decisions behind the first-order stack
