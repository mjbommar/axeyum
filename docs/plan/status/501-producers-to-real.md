# Lane: producers-to-real — `ring`/`decide` over `Alg.CommRing`/`AlgS.CommRing`

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, producers-to-real, 2026-09-04).** W1-5: extend
`ring` (and `decide` if meaningful) to the setoid carriers, repeating
`linarith::generic`'s move (ADR-1585/ADR-1592) for a second producer.

`ring::generic` (`crates/axeyum-lean-kernel/src/ring/generic.rs`, new file)
is built EXTENDING `linarith::generic`'s exact `Backend` shape: a
`Backend::{KernelEq, Setoid}` enum threaded through six wrapper methods
(`refl`/`symm`/`trans`/`congr_add`/`congr_mul`/`congr_neg`) and one parser
(`as_eq`), reaching `Alg.CommRing` (`Int.commRing`/`Rat.commRing`) and
`AlgS.CommRing` (`CReal.commRingS`, `Complex.commRingS` reachable the same
way). The fragment is `ring::rat`'s exact shape (sorted sum of sorted
monomials, coefficients capped at magnitude 1) generalized off selectors
instead of a fixed `RatPrelude`. Three facts not primitive on `Alg.CommRing`/
`AlgS.CommRing` (`mul_zero`, `mul_neg_one`, `neg_neg`) are reused from
already-generic `Ring`-level theorems (`Alg.ringMulZero`/`Alg.mul_neg_one`/
`Alg.neg_neg`, `AlgS.mul_zero`/`AlgS.mul_neg_one`/`AlgS.neg_neg`) rather than
re-derived; `mul_neg`/`neg_mul` (neg distributing into one side of a
product) are derived LOCALLY per `Problem` from `mul_neg_one`+`mul_assoc`+
`congr_mul` — no new global declaration. `neg` does NOT distribute over
`add` generically (named scope restriction, see the module's own doc
comment) — a `neg (add u v)` source subterm is a sound but un-simplified
atom.

Status of the remaining deliverables (goals at `CReal.commRingS`,
corrupted-certificate battery, `decide` investigation, retirement count,
ADR-1599, gates) — being executed this session; see landed-changes below
for what has actually run.

<!-- plan-section: landed-changes -->

| 2026-09-04 | producers-to-real | status stub |
