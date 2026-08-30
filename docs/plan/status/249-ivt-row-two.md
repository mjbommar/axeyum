# 249 — IVT's ADR-0603 row 2, as a kernel theorem

<!-- plan-section: lane-status -->

Status: **DONE.** Seven declarations landed in a new
`crates/axeyum-lean-kernel/src/creal/ivt_boundary.rs`, all accepted by
`Kernel::add_declaration` on the **first** attempt, all axiom footprint 0. One
curated fact registered. Nothing in `creal/ivt.rs` was touched.

## Step 0 — the gap was real

`grep -n 'name_str(creal, "ivt' crates/axeyum-lean-kernel/src/creal.rs` returned
the fifteen existing `ivt_*` names and **no** row-2 declaration; the only
`decides`-shaped name anywhere in the crate was
`evt_attained_max_decides_sign`. The brief's reading was correct and the note
that produced it (`docs/research/11-design-review/2026-08-29-ivt-has-no-row-2-theorem-evt-does.md`)
was not stale.

## What was proved

```text
CReal.ivt_exact_root_decides_sign :
  ∀ v c, le zero c → le c one →
    Equiv (min c (max (add c (neg one)) v)) zero →
    Or (le v zero) (le zero v)
```

Verbatim from `kernel_declaration_projection`:

```text
((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.le CReal.zero x1) ->
  ((x3 : CReal.le x1 CReal.one) -> ((x4 : CReal.Equiv (CReal.min x1
  (CReal.max (CReal.add x1 (CReal.neg CReal.one)) x0)) CReal.zero) ->
  Or (CReal.le x0 CReal.zero) (CReal.le CReal.zero x0))))))
```

The full statement family, seven declarations, `creal` prelude, footprint 0
each:

Detail moved to [`../notes/249-ivt-row-two.md`](../notes/249-ivt-row-two.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | ivt-row-two | `CReal.ivt_exact_root_decides_sign` — **ADR-0603 row 2 for IVT**, previously prose in `ivt.rs`'s module doc. An exact root of the plateau family `x ↦ min x (max (x−1) v)` on `[0,1]` yields `Or (le v zero) (le zero v)`; axiom-free, accepted on the first `add_declaration` |
| 2026-08-29 | ivt-row-two | `CReal.ivtPlateau` + `ivtPlateau_nonpos_at_zero` / `_nonneg_at_one` / `_uniformly_continuous` — all three of classical IVT's hypotheses PROVED, so the counterexample family is machine-checked to lie inside its hypothesis class rather than asserted to |
| 2026-08-29 | ivt-row-two | `CReal.uniformly_continuous_max` / `_min` — the lattice's first entries in the closure table `uniformly_continuous_add`/`_neg`/`_sub`/`_mul` fill for the ring. General, modulus `mF n + mG n`, no index shift. `_min` is not `_max`'s dual and the writeup says why |
| 2026-08-29 | ivt-row-two | `F:creal-ivt-exact-root-decides-sign` registered, curated, four discriminating checkers; `validate-facts.py` 1926 facts / 0 errors |
