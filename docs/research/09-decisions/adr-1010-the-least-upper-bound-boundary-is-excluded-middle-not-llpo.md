# ADR-1010: The least-upper-bound boundary is excluded middle, not LLPO

Status: accepted
Date: 2026-08-31
Index-summary: LUB's ADR-0603 row 2 was the one family whose boundary was asserted rather than proved; `CReal.lub_decides_em` closes it, and the principle it extracts is UNRESTRICTED excluded middle rather than the analytic LLPO the IVT and EVT rows land on — because Spivak's P13 quantifies over a set given by an arbitrary predicate, not over the range of a continuous function.
Index-status: accepted

## Context

[ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md)
makes a classical theorem land as a graded family. Amendment 2 defines row 2 as
an **unprovability witness** — a kernel-checked declaration showing
`classical statement ⟹ a decision principle this kernel lacks` — and requires a
non-vacuity control. Amendment 4 forbids inferring a row 2 from prose
describing an absence.

`docs/curriculum/graded-statement-families.md` §2 measured LUB against that
standard on 2026-08-27 and found it wanting, in its own words:

> **Pure absence — no refutation exists anywhere in the repository.** … No
> function is exhibited whose classical supremum is not constructively
> computable … **the unavailability is asserted, not proved.**

That was the last such row among the four families that note surveyed, and it
was the load-bearing one: row 2 is the axis on which ADR-0603's dominance
argument rests, so a row 2 that cannot fail is exactly the
checker-that-cannot-fail defect arriving as a theorem instead of as a script.

[ADR-0716](adr-0716-row-two-of-a-decidable-subject.md) measured row 2 as
provably **empty** over ℕ, ℤ and ℚ, because the decision principle every
analysis row 2 extracts (`le_total`) is a proved, axiom-free theorem there.
That finding is about the DISCRETE carriers and does not transfer to `CReal`,
where `CReal.le_total` and `CReal.lt_total` are both absent by design
(`creal/cotransitivity.rs` states the position outright). LUB over `CReal` is
therefore a place where row 2 is real, not vacuous.

## Decision

### 1. The counterexample family is a set given by an arbitrary predicate

Spivak's P13 says every **inhabited set of reals bounded above** has a least
upper bound. It quantifies over an arbitrary set — not over the range of a
continuous function, and not over a located set. So the faithful family is

```text
CReal.lubSet : Prop → CReal → Prop
CReal.lubSet A := fun x => Or (le x zero) (And A (le x one))
```

the set `(−∞, 0] ∪ ((−∞, 1] if A)`. Classically its supremum is `1` when `A`
holds and `0` when it does not, so **the supremum's own position answers `A`**
— the same move `evtLinear`'s maximiser makes for the sign of `v`, one level
more general because the question is an arbitrary `Prop` rather than a real
comparison.

Both of LUB's hypotheses are discharged as theorems rather than asserted, which
is what makes the family machine-checked to lie inside LUB's hypothesis class:

| declaration | statement | kind | axioms |
|---|---|---|---|
| `CReal.lubSet` | `Prop → CReal → Prop` | definition | 0 |
| `CReal.lubSet_inhabited` | `∀ (A : Prop), lubSet A zero` | theorem | 0 |
| `CReal.lubSet_bounded` | `∀ (A : Prop) (x : CReal), lubSet A x → le x one` | theorem | 0 |
| `CReal.lub_decides_em` | below | theorem | 0 |

Both hypothesis lemmas are stated at an **exhibited witness** (`0`) and an
**explicit bound** (`1`) rather than as an `Exists`. That is strictly stronger
than the classical hypotheses and therefore makes the reduction harder, not
easier.

### 2. Row 2, and the principle it lands on

Read from `kernel_declaration_projection`'s `render_lean` column, not from
prose:

```text
theorem CReal.lub_decides_em :
  (x0 : Prop) → (x1 : CReal) →
  (x2 : (x2 : CReal) → CReal.lubSet x0 x2 → CReal.le x2 x1) →
  (x3 : (x3 : CReal) → CReal.lt x3 x1 →
        Exists.{1} CReal (fun x5 => And (CReal.lubSet x0 x5) (CReal.lt x3 x5))) →
  Or x0 (Not x0)
```

One `CReal.lt_cotrans` call on the fixed strict pair `zero < one` at `z := s`
returns `Or (lt zero s) (lt s one)` unconditionally; the first branch reads `A`
off the approximation witness at `t := 0`, and the second refutes `A` because
`A` would put `1` in the set and contradict `s < 1`.

**The conclusion is unrestricted excluded middle.** This kernel does not
contain it: it has `Decidable.em`, which takes a `Decidable` instance, and the
four conditional bridges `em_of_dne` / `dne_of_em` / `em_of_peirce` /
`peirce_of_em`, which take unrestricted `em` as a **hypothesis** and never
assert it (ADR-0716 §2 measures that absence with controls).

So this row 2 is **strictly stronger** than the two that already existed.
`CReal.evt_attained_max_decides_sign` and `CReal.ivt_exact_root_decides_sign`
both land on `∀ v, Or (le v zero) (le zero v)` — analytic LLPO, which is
*consistent* with Bishop's constructive mathematics. Excluded middle for an
arbitrary proposition is not, and it is not a statement about the order on
`CReal` at all: it decides propositions about `Nat`, about `String`, about
anything the kernel can express.

### 3. Bishop's definition of supremum is what is assumed, and that choice is
### the load-bearing one

The row-2 hypothesis pair is an upper bound plus the **approximation
property**, not the classical "`s ≤ b` for every upper bound `b`". Two reasons,
and the first is decisive:

- The classical leastness clause yields only `¬¬A` here — if `A` failed, `0`
  would be an upper bound, so `s ≤ 0` — and `¬¬A → A` is *itself* the decision
  principle at issue. A reduction through it would be circular.
- The approximation property is the clause a **constructive** supremum is
  defined by, and it is exactly the clause `CReal.supOn_approx_lub`
  (`creal/sup_laws.rs`) proves for the located case. So this row 2 refutes
  precisely the generalisation row 1 stops short of.

The `∀ t < s` form is implied by Bishop's `ε`-form (take `ε := s − t`), so
assuming it assumes no more than "S has a supremum in Bishop's sense".

### 4. Non-vacuity is discharged, at a decidable proposition

A refutation shaped as an implication whose hypotheses have no models is
unfalsifiable. `creal/lub_boundary_tests.rs` discharges **both** hypotheses at
`A := True`, where the set is `(−∞, 1]` and its supremum genuinely is `1`:

- upper bound: `CReal.lubSet_bounded` at `A := True`, verbatim, no transport;
- approximation: witness `x := 1`, since `1 ∈ lubSet True` by the right
  disjunct and the hypothesis `t < 1` **is** the required `t < x`.

`Kernel::infer` accepts the fully discharged instance, and the conclusion is
pinned verbatim against an independently built `Or True (Not True)`.

Exhibiting a discharge at a *decidable* `A` does not weaken the boundary — at
such an `A` the conclusion is available anyway, which is precisely why no
analogous discharge exists for an arbitrary `Prop`.

The negative control changes ONE small term (`Or.inl` for `Or.inr`, putting an
`And True (le 1 1)` proof into a `le 1 0` slot) and carries its own positive
control in the same test. It is deliberately a **head-constant** mismatch
rather than transposed real arguments: a failing `def_eq` has no early exit,
and swapping two `CReal`s would set the checker unfolding `CReal.le`'s sequence
definition without bound — the pathology recorded in `CLAUDE.md`'s
negative-control entry.

### 5. What this does NOT claim

- It does **not** prove `∀ A : Prop, Or A (Not A)` false. Excluded middle is
  consistent with this kernel's type theory, so the conclusion is *unprovable
  here*, not refutable. "Refuted" means what it means for the IVT and EVT rows:
  the classical conclusion is proved at least as strong as a decision principle
  this kernel demonstrably does not have. It is falsifiable — land an
  unrestricted `em` and this stops being a refutation and becomes a route to
  LUB.
- It does **not** contradict LUB's row 1. `CReal.supOn` / `CReal.supOn_ub` /
  `CReal.supOn_approx_lub` construct the supremum of a **uniformly continuous
  function on a compact interval**, where the modulus supplies the locatedness;
  `creal/completeness.rs` constructs the limit of a **regular sequence**, which
  carries its own rate. `lubSet A` is neither, and it is exactly as un-located
  as `A` is undecided.
- It says nothing about LUB row 3 (`extremum::polynomial_extremum`, the
  polynomial-range special case, CAS-internal) or row 4 (there is no
  axiomatized carrier with a completeness axiom to import against — `AxReal`
  declares none).

## Consequences

- LUB's family is now 1 (Bishop completeness + `supOn`), 2 (this), 3 (narrow,
  CAS-internal), 4 (no target). `docs/curriculum/graded-statement-families.md`
  §2 is corrected accordingly; MVT's row 2 remains an *inherited* assertion and
  is the next one worth closing.
- ADR-0603's row-2 taxonomy gains a distinction it did not previously need:
  **which** decision principle a row 2 lands on is part of the result, and
  the principles are not interchangeable. LLPO is consistent with BISH;
  unrestricted `em` is not; `le_total` over a discrete carrier is a landed
  theorem and carries no information at all (ADR-0716 §1). A family whose row 2
  reaches `em` is a stronger boundary claim than one that reaches LLPO, and
  saying only "row 2 exists" flattens that.
- The mechanism generalises to any classical statement quantifying over a set
  given by an arbitrary predicate rather than over a construction — which is
  most of the classical order-completeness apparatus. Nothing here needed a new
  primitive: `lt_cotrans`, `zero_lt_one`, `lt_irrefl` and the two `lt_of_*`
  compositions were all already present, and the whole family cost four
  declarations.

## Cost

Four declarations, all first-attempt kernel accepts, all axiom-free. Measured
effect on `creal_prelude_builds` (debug, this lane's worktree, by toggling the
build step): **120.6 s** with the step stubbed out against **130.5 s / 134.0 s**
across two runs with it live — about +11 s, 9%. Not a multiple, and well below
the regression class `CLAUDE.md` records (18.7 s → 92.6 s from one declaration).

## References

- `crates/axeyum-lean-kernel/src/creal/lub_boundary.rs` — the four declarations
- `crates/axeyum-lean-kernel/src/creal/lub_boundary_tests.rs` — non-vacuity,
  negative control, statement pin, footprint
- `artifacts/facts/F-creal-lub-decides-em.json`
- [ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md),
  [ADR-0716](adr-0716-row-two-of-a-decidable-subject.md)
- `docs/curriculum/graded-statement-families.md` §2
