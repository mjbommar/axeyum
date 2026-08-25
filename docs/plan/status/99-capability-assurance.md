# Lane: capability-assurance — the strand's own metric was unmeasurable

<!-- plan-section: lane-status -->

**Open queue, in the order I intend to clear it** (`WIP`,
capability-assurance, 2026-08-20). Items that clear themselves are struck rather
than carried — a queue listing resolved work is the same defect as stale prose.

1. ~~`hooks/pre-push` runs `cargo test -p axeyum-lean-kernel` WHOLESALE~~ —
   **cleared 2026-08-20.** The Lean-prelude suites moved to `just check`, which
   already owned them and which gates a different property; the hook went
   **630 s → 130 s**. It also gained `cargo check --all-targets` (not
   `--workspace`, which does not compile the bench examples and let me break
   `main`) and a route-agreement step.
2. **One guard in `check-lra-hypothesis-binding.py:1244` measurably SURVIVES**
   (`bind_structural`'s opaque-sort check). Needs a control in
   `102-attestation-gap`'s test module; the mutation harness reports it rather
   than the harness having been wrong.
Items 3-4 (the 404 GB target-dir relocation, scheduled because it forces one
cold rebuild; and registering a heavy-cargo suite with the mutation harness)
are in [the lane note](../notes/99-capability-assurance.md).

Cleared by their owners since this list was written: `103-creal-lean-divergence.md`
is under the ceiling (2,958 B), and `PLAN.md` now records the 11 -> 10 ledger
guard-count correction rather than publishing the wrong number.

Detail and older landed rows moved to [`../notes/99-capability-assurance.md`](../notes/99-capability-assurance.md).

<!-- plan-section: landed-changes -->

| 2026-08-20 | `01d54044a` | **Certified 278/324 (85.8%)**, from 267/327 (81.7%) this morning. Timeouts 10 -> 4, `proof_errors` 10 -> 4. Four of the recovered rows were emitters that had returned the CORRECT answer and were billed 31.9s of shared prelude construction inside a 15s cap; `prelude_warm_ms` is now a visible artifact field instead of one instance's bad luck. |
| 2026-08-20 | `5a25f247a` | **Four DAG walks were exponential today, all the same bug written four times** — `contains_quantifier`, `lower_derived_bv`, `collect_enumerable_symbols_rec` (1.28e10 calls in 90s), `collect_nested_registrations`. `Float-no-simp3-main` >300s -> 19.4ms, `fp_fromsbv` 45s -> 3.8ms. The `certify.rs` memo deliberately does NOT collapse occurrences for the quantified-bit budget: that is a tree-sum, and collapsing it would undercount an exponentially shared quantifier nest and let a query past a budget check it cannot satisfy. |
