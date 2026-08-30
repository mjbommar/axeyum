# Lane: uniform-deriv — the uniform limit of derivatives

<!-- plan-section: lane-status -->

**Status: LANDED — `CReal.hasDerivative_uniform_limit` is admitted,
axiom-free, and the query that measured its absence now returns it.**
2026-08-27.

The target, verbatim from the source (`creal/uniform_convergence.rs`):

    CReal.hasDerivative_uniform_limit :
      ∀ (F F' : Nat → CReal → CReal) (G G' : CReal → CReal) (a b : CReal),
        (∀ n : Nat, HasDerivativeOn (F n) (F' n) a b) →
        UniformConvergesOn F G a b →
        UniformConvergesOn F' G' a b →
        HasDerivativeOn G G' a b

Through `Kernel::add_declaration` (the only trust anchor), on the first
attempt, with `axiom_footprint` **0** in all three preludes that build it
(`creal`, `complex`, `cpoint`).

**Re-verified before building, and again after.** Against a freshly built
`shape_search`, `--concl CReal.HasDerivativeOn --hyp CReal.UniformConvergesOn`
was **ABSENT (exit 1)** at `declarations=1890` and is now **FOUND 1** at
`declarations=1893` — exactly the three theorems below, no others. The
sixteen pre-existing `HasDerivativeOn` conclusions are unchanged and were all
pointwise combinators; this is the first that takes a limit hypothesis.

**Three declarations, not one, and the middle one is the finding.**

1. `CReal.lipschitz_of_deriv_bound` — `abs_diff_le_of_deriv_bound` with its
   endpoints **UNORDERED**:

       ∀ F F' a b, HasDerivativeOn F F' a b → ∀ M, le zero M →
       (∀ z, le a z → le z b → le (abs (F' z)) M) → ∀ x y,
       le a x → le x b → le a y → le y b →
       le (abs (add (F y) (neg (F x)))) (mul M (abs (add y (neg x))))

Detail moved to [`../notes/162-uniform-deriv.md`](../notes/162-uniform-deriv.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | uniform-deriv | `CReal.hasDerivative_uniform_limit` -- the uniform limit of derivatives; first `HasDerivativeOn` conclusion in the tree from a limit hypothesis; axiom-free, first-attempt kernel accept |
| 2026-08-27 | uniform-deriv | `CReal.lipschitz_of_deriv_bound` -- the mean value inequality for an UNORDERED pair, via `min x y` and no case split; the keystone lane 159's plan did not anticipate |
| 2026-08-27 | uniform-deriv | `CReal.abs_diff_sub_le_of_deriv_bound` -- the tail estimate `\|(F y - F x) - (G y - G x)\| <= sup\|F' - G'\|*\|y - x\|` |
| 2026-08-27 | uniform-deriv | measured: `--concl CReal.HasDerivativeOn --hyp CReal.UniformConvergesOn` ABSENT at `declarations=1890`, FOUND 1 at 1893 |
| 2026-08-27 | uniform-deriv | 14 `creal/derivative.rs` helpers promoted to `pub(super)` and imported rather than copied |
