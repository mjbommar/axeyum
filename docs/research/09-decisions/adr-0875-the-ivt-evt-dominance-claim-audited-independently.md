# ADR-0875: the IVT/EVT dominance claim, audited independently — IVT holds with named caveats, EVT's stated reason for failing is stale

Status: accepted
Date: 2026-08-30
Index-summary: First independent audit of the IVT/EVT Pareto claim. IVT
dominates on trusted base (0 vs a MEASURED `[propext, Classical.choice,
Quot.sound]`) and on computational content, with three caveats that must be
stated in the same breath: a strictly stronger hypothesis carried as DATA, an
approximate conclusion, and hypothesis-witnesses that Lean's own kernel does
not check. EVT is still not dominant as shipped, but the reason ADR-0692 and
`08-…` give — "no statement exists on which the comparison can be run" — is
now FALSE: `supOn_ub` + `supOn_approx_lub` compose into exactly the
`evt_approx_max` those documents call missing, and this lane's probe had the
kernel admit it axiom-free. EVT's real blocker is bookkeeping (no named
declaration, ZERO ledger facts for the whole supremum family), not structure.
Vacuity is now machine-checked for both, at concrete function families whose
hypotheses are kernel theorems. The four fact-level protections previously
measured at 0/20 are still 0/17.
Index-status: accepted

- **Lane:** `ivt-evt-dominance-audit` — an independent audit. The EVT half was
  last assessed by the lane that built `supOn_ub`.
- **Audits:**
  [`08-ivt-and-evt-measured-against-mathlib.md`](../../formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md),
  [ADR-0692](adr-0692-the-dominance-test-has-two-axes-not-a-vote-and-ivt-still-passes-it.md),
  and the claim in
  [`07-the-cost-model-and-pareto-position.md`](../../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md)
  §1.
- **Reclassifies nothing.** No fact, `epistemic_status`, prelude declaration,
  or gate was edited. The one new artifact is
  `crates/axeyum-lean-kernel/examples/ivt_evt_vacuity_probe.rs`, which adds
  declarations to a *local* kernel only.

## Verdict

**IVT — dominant on both axes, with three caveats, none fatal, all of which
must be stated in the same breath as the claim.**

**EVT — not dominant as the repository ships it. But `08-…`'s and ADR-0692's
stated reason is stale and should be replaced.** They say no comparable
statement exists. One does, up to a single composition, and the kernel admits
it. What EVT actually lacks is a *named declaration* and *any ledger fact at
all* for the supremum family.

Everything below is read from the kernel, from official Lean, or from Mathlib
at `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Nothing is taken from prose.

## 1. Both sides' statements, from the rendered types

Ours, from `kernel_declaration_projection` built fresh in this lane's worktree
(2,038 distinct theorems, `axiom_bearing=0`):

```text
CReal.ivt_approx : ∀ (F : CReal → CReal) (a b : CReal),
  UniformlyContinuousOn F a b → le a b → le (F a) zero → le zero (F b) →
  ∀ (n : Nat), ∃ x, le a x ∧ le x b ∧ le (abs (F x)) (ofRat (1/(n+1)))

CReal.supOn : ∀ (F : CReal → CReal) (a b : CReal),
  le a b → UniformlyContinuousOn F a b → CReal            -- a DEFINITION

CReal.supOn_ub : ∀ F a b (hab : le a b) (huc : UC F a b) (x : CReal),
  le a x → le x b → le (F x) (supOn F a b hab huc)

CReal.supOn_approx_lub : ∀ F a b (hab : le a b) (huc : UC F a b) (n : Nat),
  ∃ x, le a x ∧ le x b ∧ le (supOn F a b hab huc) (add (F x) (ofRat (1/(n+1))))
```

Mathlib's, re-read from the checkout rather than from either prior document:

```lean
-- Mathlib/Topology/Order/IntermediateValue.lean:552
theorem intermediate_value_Icc {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Icc (f a) (f b) ⊆ f '' Icc a b

-- Mathlib/Topology/Order/Compact.lean:246
theorem IsCompact.exists_isMaxOn [ClosedIciTopology α] {s : Set β}
    (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) :
    ∃ x ∈ s, IsMaxOn f s x
-- IsMaxOn f s x  ≡  ∀ y ∈ s, f y ≤ f x   (Mathlib/Order/Filter/Extr.lean:113)
```

## 2. Trusted base — Mathlib's side is now MEASURED, not inferred

`08-…` closes by recording that "Mathlib's axiom footprints were not measured,
only inferred". They are measured now, with the cached oleans at the pinned
commit and the pinned Lean 4.30.0:

```text
'intermediate_value_Icc'      depends on axioms: [propext, Classical.choice, Quot.sound]
'intermediate_value_Icc''     depends on axioms: [propext, Classical.choice, Quot.sound]
'IsCompact.exists_isMaxOn'    depends on axioms: [propext, Classical.choice, Quot.sound]
'IsCompact.exists_isMinOn'    depends on axioms: [propext, Classical.choice, Quot.sound]
'IsMaxOn'                     does not depend on any axioms      (control)
```

The `IsMaxOn` row is the control: a probe that printed three axioms for
everything would be measuring nothing. Ours read `0` from
`Kernel::axiom_footprint` for every declaration in both families. **The
trusted-base axis is settled, in our favour, for both theorems.**

## 3. Vacuity — machine-checked, and this is the finding the brief asked for

A theorem whose hypotheses nothing satisfies proves nothing, and an empty
axiom footprint cannot see that. `examples/ivt_evt_vacuity_probe` instantiates
both families at concrete function families **whose hypotheses are themselves
kernel theorems**, and admits each instantiation through
`Kernel::add_declaration`, so the instantiated statement is what the kernel
prints:

```text
ADMITTED  EvtAudit.ivt_approx_at_ivtPlateau       axioms=0
  ∀ (v : CReal) (n : Nat), ∃ x, le zero x ∧ le x one ∧
      le (abs (ivtPlateau v x)) (ofRat (1/(n+1)))

ADMITTED  EvtAudit.evt_approx_max_at_evtLinear    axioms=0
  ∀ (v : CReal) (n : Nat), ∃ x, le zero x ∧ le x one ∧
      ∀ y, le zero y → le y one → le (evtLinear v y) (add (evtLinear v x) (1/(n+1)))
```

Both hold for an **arbitrary** `v`. That matters more than it looks: these are
precisely the two families whose EXACT versions are proved to imply analytic
LLPO (`ivt_exact_root_decides_sign`, `evt_attained_max_decides_sign`). So the
approximate statements are not merely non-vacuous — they are non-trivial
exactly where the constructive difficulty lives. **Neither theorem is vacuous,
and the witness is in the tree rather than in this document.**

## 4. EVT row 1 exists in substance — the standing reason for its failure is stale

`08-…` §5 item 2 names the statement that would fill EVT's hole:

> `CReal.evt_approx_max : ∀ n, ∃ x ∈ [a,b], ∀ y ∈ [a,b], F y ≤ F x + 1/(n+1)`

`supOn_ub` bounds `F y` above by `supOn`; `supOn_approx_lub` bounds `supOn`
above by `F x + 1/(n+1)`; `le_trans` composes them. The probe builds that term
and the kernel admits it:

```text
ADMITTED  EvtAudit.evt_approx_max  axioms=0
  ∀ F a b (hab : le a b) (huc : UC F a b) (n : Nat),
    ∃ x, le a x ∧ le x b ∧ ∀ y, le a y → le y b → le (F y) (add (F x) (1/(n+1)))
```

with a negative control in the same run: the identical proof term with the
`+ 1/(n+1)` slack removed — the exact attained maximum — is REFUSED
(`TypeMismatch`). That control's scope is narrow and worth stating: it shows
the composition genuinely consumes the slack. It does **not** show the exact
form is unprovable; that is row 2's job and row 2 does it.

ADR-0692's re-derivation is therefore correct as of the day it ran and wrong
today. It checked `CReal.supOn_upper_bound` (a name that never existed) and
`CReal.evt_approx_max`, found both absent, and concluded the comparison could
not be run. The law landed as `CReal.supOn_ub`.

**This is the "verify a blocker still exists in the tree" failure in its
documentary form**: a name-shaped absence probe reported ABSENT for a law that
was present under a different spelling, and a decision was written on it.

## 5. `supOn` is indexed by the MODULUS, and nothing said that did not matter

Read from the kernel, with its own control:

```text
inductive CReal.UniformlyContinuousOn : (CReal → CReal) → CReal → CReal → Sort (1)
definition CReal.le                   : CReal → CReal → Prop        (control)
```

`Sort 1` is `Type 0`, not `Prop`. The uniform-continuity witness carries the
modulus, so it is **data** and is not proof-irrelevant, while `hab : le a b`
is a `Prop` and is. `CReal.supOn F a b hab huc` takes that witness as an
argument, so two moduli for the same `F` give two `supOn` terms the kernel
does not identify. Of the seven declarations whose type mentions `supOn`, none
relates two instances.

This is the sharpest technical objection available against the EVT half —
"your supremum is not a function of `F`" — and on Mathlib's side it cannot
even arise, because `ContinuousOn` is a `Prop`. It is answerable, from the two
characterizing laws plus `CReal.le_of_forall_le_add_small`, and the probe
answers it:

```text
ADMITTED  EvtAudit.supOn_modulus_independent  axioms=0
  ∀ F a b (hab : le a b) (u1 u2 : UC F a b),
    Equiv (supOn F a b hab u1) (supOn F a b hab u2)
```

Same standing as `evt_approx_max`: derivable today, not declared.

## 6. What the ledger actually carries — and what it does not

Read from a freshly regenerated `artifacts/safety-matrix/safety-matrix.tsv`
(S0), over the 17-fact IVT/EVT family selected by CONTENT rather than by id
substring (11 `CReal` + 6 CAS):

| protection | of 17 |
|---|---:|
| `kernel_theorem` | 11 |
| `env_footprint` | 11 |
| `coverage_bearing_checker` | 11 |
| `semantic_falsification` | 3 |
| `per_theorem_footprint` | **0** |
| `circularity` | **0** |
| `mutation_control` | **0** |
| `independent_replay` | **0** |

The 6 CAS rows score **0 on every protection** except one `semantic_falsification`
each on two of them.

**And there is no fact for any of the supremum family.** Filtering the whole
ledger to `formal.kernel_theorem` beginning `CReal.sup`, `CReal.mesh` or
`CReal.evt` returns nine rows: eight `mesh*` and
`F:creal-evt-attained-max-decides-sign`. `CReal.supOn`, `CReal.supOn_ub`,
`CReal.supOn_approx_lub`, `CReal.supSeq_converges_supOn` and every other
`supSeq` law have **no ledger fact at all**. The rungs BELOW the supremum are
recorded; the supremum itself is not.

That, and not the absence of a statement, is why EVT cannot be cited as a
dominance example today: **there is nothing in the product's own ledger to
check the claim against.**

## 7. The five risks, per theorem (ADR-0717)

An empty axiom footprint addresses part of risks 4 and 5 only. Per risk, for
the `CReal` IVT/EVT theorems:

1. **Kernel unsoundness — COVERED, and this is new since the 0/20 measurement.**
   `F:lean-kernel-accepts-the-whole-constructed-real-carrier` replays the
   carrier through official Lean 4.30.0's own `Lean.Environment.addDeclCore`.
   Re-run on this lane's HEAD (136.8 s, 4 tests, exit 0):
   `population=2062 representable=1989 lean_kernel_constants=1989`, with a
   tamper control (`tampered-proof-rejected subject=CReal.Equiv.not_zero_one`).
   Cross-checking the 73 residue names against the IVT/EVT family, **18 of 21
   are Lean-kernel-checked**. The three that are not:

   | declaration | reason |
   |---|---|
   | `CReal.ivt_exact_root_at` | blocked by `CReal.hasDerivative_add` |
   | `CReal.ivtPlateau_uniformly_continuous` | theorem type is not a `Prop` |
   | `CReal.evtLinear_uniformly_continuous` | theorem type is not a `Prop` |

   The last two are the **hypothesis-class witnesses** — the very declarations
   that make row 2 meaningful and that §3's vacuity instantiation consumes.
   They are Type-valued because `UniformlyContinuousOn` carries a modulus, so
   Lean refuses them *as `Theorem`s* by a rule of its own; that is a
   declaration-kind mismatch, not evidence of a defect. It remains true that no
   independent kernel has checked them.
2. **Statement error — PARTIAL.** `exact_statement` is 100% ledger-wide (S1,
   ADR-0763), so each fact's `formal.statement` is pinned to the rendered type.
   That binds *transcription*. It does not bind *intent*: unlike the `ml430`
   mirrors, these facts have no external statement source, so "the type is the
   proposition we meant" is checked by nothing.
3. **Vacuity — COVERED as of this audit, and by nothing before it.**
   `F:creal-evt-attained-max-decides-sign` was covered for row 2's hypothesis
   by two `creal_tests` satisfiability tests; `ivt_approx`, `ivt_exact_root`
   and the entire supremum family had no such check.
4. **Contamination — PARTIAL.** `env_footprint` yes and `axiom_footprint: []`
   on all 11, so the environment is axiom-free. `per_theorem_footprint` and
   `circularity` are **0/17**: no fact publishes its own theorem's reached
   trust or a circularity result.
5. **False evidence — PARTIAL.** `coverage_bearing_checker` is yes on 11 of 17
   and **no on all 6 CAS rows**. All 11 `CReal` rows have
   `checkers_name_producer = yes`: the checker is `theorem_dependency_inventory`,
   reading the same kernel that produced the theorem. `mutation_control` is
   **0/17**.

**What changed since 0/20:** the four fact-level protections it named —
per-theorem footprint, circularity, mutation control, independent replay — are
**still 0/17**. What did change is above the fact level: S0 now *measures* them,
S1 pins every statement, and the carrier-wide Lean replay covers 18 of the 21
declarations by NAME. It publishes declaration names and not fact ids, which is
exactly the gap the safety matrix's own "gates that publish no per-fact set"
table names — so no IVT/EVT fact can be credited from it, and the `0` is
accurate as a statement about the rows.

## 8. Decision

1. **Keep IVT's dominance claim, and require its three caveats in the same
   sentence.** The claim is: *`CReal.ivt_approx` dominates `intermediate_value_Icc`
   on trusted base (0 against a measured 3) and on computational content (a
   reducible bisection with a proved accuracy bound against a `noncomputable`
   corollary of connectedness) — while assuming strictly more (uniform
   continuity with an explicit modulus, carried as data), concluding strictly
   less (an approximate root at a fixed target, one orientation), and over a
   vastly narrower ambient structure.* Any shorter form is not the claim.
2. **Stop filing the continuity-hypothesis gap under "not comparable."** It is
   the one axis on which Mathlib's theorem is unambiguously stronger, and "our
   kernel cannot state `ContinuousOn`" is a fact about our kernel, not a reason
   to drop the axis. Report it as a *named asymmetry inside the claim*, in the
   position §4's conceded-breadth table currently gives to "generality of
   structure".
3. **Replace EVT's stated reason for ineligibility.** `08-…` §2 and §4 and
   ADR-0692's EVT section must stop saying no comparable statement exists.
   The corrected reason: *the content exists (`supOn_ub` + `supOn_approx_lub`
   compose to `evt_approx_max`, kernel-admitted, axiom-free, non-vacuous at
   `evtLinear`), but no declaration NAMES it, and the ledger carries no fact
   for `supOn` or any of its laws — so there is nothing to cite and nothing to
   check.*
4. **Do not declare `evt_approx_max` or `supOn_modulus_independent` from this
   lane.** An audit that lands the thing it was auditing is a lane grading its
   own work, which is the failure this audit exists to correct. The probe
   demonstrates derivability in a local kernel; a separate lane should land
   them in the prelude with facts.
5. **The next EVT increment is three items, in order**, and none of them is
   research: declare `CReal.evt_approx_max`; declare
   `CReal.supOn_modulus_independent`; register facts for `CReal.supOn`,
   `supOn_ub`, `supOn_approx_lub` and `evt_approx_max`. The proofs are in
   `examples/ivt_evt_vacuity_probe.rs`.

## Alternatives rejected

- **Upgrade EVT to "dominant" on the strength of the composed statement.**
  Rejected. The statement is not declared and has no fact; a dominance claim
  a referee cannot check in the ledger is the "unfalsifiable claim at full
  speed" failure this repository names as its worst outcome.
- **Downgrade IVT to "not dominant" because it assumes more and concludes
  less.** Rejected, but it is the strongest objection and it is close.
  `07-…` prices "constructive ⟹ classical plus a program" as one trade, and
  the ε-weakening plus the modulus IS that trade — the same trade in both
  theorems. Naming it (decisions 1 and 2) is the fix; withdrawing the claim
  is not.
- **Treat EVT and IVT differently on the ε-weakened conclusion.** Rejected as
  the exact inconsistency ADR-0692 was written to remove. `evt_approx_max` is
  the structural mirror of `ivt_approx`: `∃x ∈ [a,b]` with an ε-bound in both.
  Whatever verdict the weakening earns, it must earn the same one twice.
- **Amend the facts whose evidence this audit found thin.** Out of scope by
  the lane's brief, and correctly so: reported, not edited.

## Cost

Documentation plus one new example (`ivt_evt_vacuity_probe`, 5 admitted
declarations + 1 refused control + 1 representability report, 17 s). Measured
runs: `prelude_theorem_inventory` and `kernel_declaration_projection` rebuilt
fresh (49 s); `real_lean_creal_carrier_kernel_replay` re-run twice under
`AXEYUM_REQUIRE_LEAN=1` (137 s each); `lake env lean` `#print axioms` against
Mathlib at the pinned commit; `gen-safety-matrix.py` regenerated in this
lane's own worktree and **not committed** (it is another lane's artifact and
was stale on arrival for unrelated reasons).
