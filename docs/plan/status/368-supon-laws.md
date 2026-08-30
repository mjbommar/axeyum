# Lane 368 — the `CReal.supOn` characterization laws

<!-- plan-section: lane-status -->

**Status: LANDED (partial, and the partiality is precise). 2026-08-30.**

Eight declarations in a new `crates/axeyum-lean-kernel/src/creal/sup_laws.rs`,
all admitted through `Kernel::add_declaration` with an empty axiom footprint,
every one a first-attempt kernel accept. Decision recorded in
[ADR-0710](../../research/09-decisions/adr-0710-supon-is-a-supremum-from-below-and-on-a-dense-family-from-above.md).

## What landed

**The approximate least-upper-bound law is complete.**

```
CReal.supOn_approx_lub : ∀ F a b (hab : le a b) (u : UniformlyContinuousOn F a b) (e : Nat),
  ∃ x, le a x ∧ (le x b ∧ le (supOn F a b hab u) (add (F x) (ofRat (Rat.natDivSucc 1 e))))
```

It must stay approximate: `CReal.evt_attained_max_decides_sign` refutes the
attaining form, which is EVT's row 2. No `argmax`-shaped declaration was added
and none may be.

Supporting it: `CReal.maxRange_attained_approx` (a finite maximum is
approximately attained at one of its samples, by `lt_cotrans`) and
`CReal.supSeq_le_shift`.

**The upper-bound law landed at every sampled point, not at an arbitrary one.**

```
CReal.supSeq_le_supOn             : le (supSeq F a b u k) (supOn F a b hab u)
CReal.supOn_ub_at_supSeq_point    : i ≤ meshLevelCount (supLevel F a b u k)
                                    → le (F (sample i)) (supOn F a b hab u)
CReal.meshMax_le_supOn_add        : le (meshMax F a b (supLevel F a b u k + dd))
                                       (add (supOn F a b hab u)
                                            (ofRat (natDivSucc 1 (meshLevelCount k))))
CReal.supOn_ub_at_fine_mesh_point : i ≤ meshLevelCount (supLevel F a b u k + dd)
                                    → le (F (sample i))
                                         (add (supOn F a b hab u)
                                              (ofRat (natDivSucc 1 (meshLevelCount k))))
```

The last is the strongest: the refinement depth `dd` is free, so the sampled
points can be made as fine as wanted while `k` controls the error
independently.

**The tool the remaining step needs**, `CReal.stepFamily_locate`, is landed —
cell location stated over the ORDER alone, with no mesh algebra in the
induction.

## What does NOT hold

`∀ x, le a x → le x b → le (F x) (supOn F a b hab u)` at an arbitrary `x`.
One declaration; ADR-0710's "What remains, precisely" gives the four-step
route, the level construction, and the reason the locate epsilon cannot be
absorbed by the schedule alone.

## Verdict on the two-axis dominance test

Detail moved to [`../notes/368-supon-laws.md`](../notes/368-supon-laws.md).

