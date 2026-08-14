# Lane: infeasibility — certified infeasibility with a minimal explanation (OR/planning)

<!-- plan-section: lane-status -->

**Irreducibility is now measured, not asserted — three OR instances, three
irreducible cores, one of them kernel-checked (`WIP`, infeasibility,
2026-08-14).** The chain (deletion-minimized `get-unsat-core` -> Farkas
certificate -> Lean reconstruction) all existed and had never been pointed at a
real operations-research instance, and nothing anywhere re-solved a leave-one-out
subset — so "minimized core" was a hope, since `unsat_core` conservatively keeps
a row whose removal leaves the remainder `unknown`. Landed: three committed
instances under `artifacts/instances/infeasibility/` (nurse roster 5/102 = 4.9%,
hazmat load plan 14/90 = 15.6%, project schedule 5/60 = 8.3%), a measuring
example that re-solves every leave-one-out subset AND replays each returned model
through the IR evaluator, a z3 cross-check script that agrees on every core and
every leave-one-out, and four facts (0 validator errors). Each core's `unsat`
turned out to carry a **re-derived** arithmetic certificate
(`UnsatArithAletheProof` / `UnsatFarkas`, `check_outcome = verified`, trust step
`farkas` certified this run), not a bare verdict. The schedule core reconstructs
into the Lean kernel from its all-multipliers-1 Farkas certificate — the largest
LRA reconstruction in the tree (every existing exercise uses 2 or 3 constraints).
Two traps recorded in the diary: `prove_unsat_to_lean_module` routes this query
to `ProofFragment::LraDpll`, whose module is a **structural shim** that
kernel-checks and contains no arithmetic at all (`reconstruct_lra_proof` must be
called directly); and the proof term is **5.1 MB** for a five-row explanation,
because the arith prelude has no numerals.

Next, in priority order: (1) numerals in the arith prelude — 5.1 MB for five
rows is what stops a kernel-checked explanation being shippable; (2) a
hypothesis-footprint audit for the LRA route, binding each `lra.hyp._N` back to
its originating assertion (the propositional route has
`declared_assumption_clauses`; the arithmetic one has nothing, so the example can
only count the axioms, not check them); (3) facade dispatch order, so an SMT-LIB
QF_LRA `unsat` can reach `ProofFragment::Lra` instead of the shim — nothing in
the repository currently asserts `ProofFragment::Lra`; (4) an integer route: both
LIA cores have re-checked Alethe refutations and no kernel path; (5) a filtering
IIS algorithm, since the deletion loop costs O(n) full solves and is hopeless
past a few hundred rows.

Full reasoning, including what a commercial IIS gives that this does not:
[`docs/mathematics-2026-08/diary-infeasibility.md`](../../mathematics-2026-08/diary-infeasibility.md).

<!-- plan-section: landed-changes -->

| 2026-08-14 | `PENDING` | Certified infeasibility for operations research: three committed OR instances with measured-irreducible cores (4.9% / 15.6% / 8.3%), leave-one-out re-solves with evaluator model replay, z3 cross-check, and a kernel-checked Farkas refutation of the schedule's critical chain. Four facts. |
