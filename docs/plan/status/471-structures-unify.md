# Lane: structures-unify — wiring `CReal.commRingS`, a `Complex` instance, and unifying the two Alg spines

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, structures-unify, 2026-09-03).** In progress:
wiring `CReal.commRingS` into `build_creal_prelude`'s generated
`STEP_DISPATCH`; `Complex.commRingS`; deriving `Alg.ringMulZero`/`neg_neg`/
`sub_self` from `AlgS`; `AlgS.mul_neg_one`/`add_left_cancel`. Updated as work
lands.

<!-- plan-section: landed-changes -->

| 2026-09-03 | structures-unify | `CReal.commRingS` wired into `build_creal_prelude`'s `STEP_DISPATCH` (`algebra_instance::declare_comm_ring_s`, right after `product::declare_product`); `steps_generated.rs` regenerated, `--check --strict --self-check` exit 0 |
