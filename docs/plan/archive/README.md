# Archived lane status — the 2026-08-13 → 15 campaign

`PLAN.md` is an **active work queue**, not a journal. These 43 lane status
files are the record of lanes that have landed their work or were cut off; they
are kept verbatim, and they are no longer emitted into `PLAN.md`.

## Why they moved

The per-lane split (`69d32216b`) fixed the shared-append-point clobbering that
cost this repository content four times in one day. It also took `PLAN.md` from
under its 52 KB authority ceiling to **233,888 bytes in two days** — 43 lanes
each writing a diary-style block — so `just check` could not pass at all. The
ceiling and the per-lane design could not both stand: `docs/plan/global/` alone
is 43,348 bytes of the budget, so even a 500-byte cap per lane would not have
fit. Archiving finished and cut-off lanes returns the sources to 46,820 bytes
and returns `PLAN.md` to being a queue.

Nothing is lost. Each file is intact below, in git history, and — for 26 of the
43 — duplicated in a fuller committed diary, which is the better record anyway.

## The lanes, and what each said was next

Restore a lane by `git mv`-ing its file back into `docs/plan/status/` when work
on it resumes, and re-running `python3 scripts/gen-plan.py`.

| lane | status | record | next, as the lane left it |
|---|---|---|---|
| `history` | `WIP` | [status](00-history.md) | — |
| `agent-k-hypothesis-minimisation` | `WIP` | [status](05-agent-k-hypothesis-minimisation.md) | — |
| `agent-h-clausal-reconstruction` | `DONE` | [status](10-agent-h-clausal-reconstruction.md) | kernel arena checkpointing, spooling admitted theorems before truncation so proof size becomes disk-bounded rather than RAM-bounded. |
| `agent-i-cas-bridge` | `DONE` | [status](20-agent-i-cas-bridge.md) | exact-rational LP over candidate residues instead of unit-coefficient subset search; see `agent-i-cas-bridge/FEEDBACK.md` F8. |
| `telescoping` | `WIP` | [status](25-telescoping.md) · [diary](../../mathematics-2026-08/diary-telescoping.md) | — |
| `telescoping-scale` | `WIP` | [status](26-telescoping-scale.md) · [diary](../../mathematics-2026-08/diary-telescoping-scale.md) | — |
| `geometry` | `WIP` | [status](27-geometry.md) · [diary](../../mathematics-2026-08/diary-geometry.md) | (1) A degree-reverse-lexicographic order in `groebner.rs` — the single change most likely to move the frontier, and it helps every consumer of Gröbner bases in the crate. (2) Split… |
| `mvpoly-bignum` | `WIP` | [status](28-mvpoly-bignum.md) · [diary](../../mathematics-2026-08/diary-mvpoly-bignum.md) | (a) switch `geometry_limits()` to `grevlex`, regenerate the six certificates, **check whether any certificate now uses a smaller condition set** (that is a change to what the fact… |
| `geometry-frontier` | `WIP` | [status](29-geometry-frontier.md) · [diary](../../mathematics-2026-08/diary-geometry-frontier.md) | (1) Buchberger's criteria in `groebner_cert.rs` — product first (four lines, 28–46% of pairs *by measurement*), then chain; worth it for the whole crate, and it will **not** by its… |
| `lean-kernel` | `WIP` | [status](30-lean-kernel.md) | — |
| `euler-linearity` | `WIP` | [status](31-euler-linearity.md) · [diary](../../mathematics-2026-08/diary-euler-linearity.md) | (1) **Decide about Pappus** — isolate a single condition with a rational configuration (or find a smaller condition set), or relax the ratchet to a named justified exception and wr… |
| `pappus-minimality` | `WIP` | [status](32-pappus-minimality.md) · [diary](../../mathematics-2026-08/diary-pappus-minimality.md) | (1) **Simson** — decide the field first, then the algebra; a rational configuration is an hour's work (`A=(5,0)`, `B=(0,5)`, `C=(−3,4)`, `P=(4,−3)` on `x²+y²=25`, concyclicity as t… |
| `simson` | `WIP` | [status](33-simson.md) · [diary](../../mathematics-2026-08/diary-simson.md) | (1) **The `fact.schema.json` minimality field**, now on its fourth instance and with a new axis — the regime is no longer the whole story, because a minimal set is minimal *over a… |
| `int-keystone` | `WIP` | [status](35-int-keystone.md) · [diary](../../mathematics-2026-08/diary-int-keystone.md) | — |
| `int-remainder` | `WIP` | [status](36-int-remainder.md) · [diary](../../mathematics-2026-08/diary-int-remainder.md) | — |
| `real-keystone` | `WIP` | [status](37-real-keystone.md) · [diary](../../mathematics-2026-08/diary-real-keystone.md) | ℚ is the right carrier for LRA — real and rational satisfiability coincide for linear systems with rational coefficients — and it *is* quotient-free constructible (`Int` numerator,… |
| `ordered-ring-reconstruct` | `DONE` | [status](38-ordered-ring-reconstruct.md) · [diary](../../mathematics-2026-08/diary-ordered-ring-reconstruct.md) | (1) Fix the facade dispatch so an SMT-LIB QF_LRA `unsat` reaches `ProofFragment::Lra` instead of the contentless `LraDpll` shim — generalizing the shim would produce an axiom-free… |
| `lra-dispatch` | `DONE` | [status](39-lra-dispatch.md) · [diary](../../refactor-2026-08/diary-lra-dispatch.md) | (1) The 28 non-arithmetic structural routes are marked, not fixed — marking turns a silent misreport into a visible gap. (2) Multi-clause `DisjunctiveLra`: a two-clause Boolean `QF… |
| `proved-mathematics` | `WIP` | [status](40-proved-mathematics.md) | — |
| `quant-duality` | `WIP` | [status](45-quant-duality.md) · [diary](../../mathematics-2026-08/diary-quant-duality.md) | — |
| `proof-construction` | `WIP` | [status](50-proof-construction.md) | — |
| `fp-kernels` | `WIP` | [status](55-fp-kernels.md) · [diary](../../mathematics-2026-08/diary-fp-kernels.md) | — |
| `infeasibility` | `WIP` | [status](56-infeasibility.md) · [diary](../../mathematics-2026-08/diary-infeasibility.md) | — |
| `db-design` | `WIP` | [status](57-db-design.md) · [diary](../../mathematics-2026-08/diary-db-design.md) | — |
| `publishable-result` | `WIP` | [status](60-publishable-result.md) | — |
| `documentation` | `WIP` | [status](70-documentation.md) | — |
| `gates` | `WIP` | [status](80-gates.md) | — |
| `lean-gate-honesty` | `WIP` | [status](81-lean-gate-honesty.md) · [diary](../../refactor-2026-08/diary-lean-gate-honesty.md) | — |
| `quant-bv-shares` | `WIP` | [status](82-quant-bv-shares.md) · [diary](../../refactor-2026-08/diary-quant-bv-shares.md) | — |
| `quant-pins` | `WIP` | [status](83-quant-pins.md) | `Int.euclidean_decomposition` is the last integer axiom, and `int-remainder` names it as its next target. When it is discharged these three modules move again — but now they will m… |
| `formalized-collect` | `WIP` | [status](85-formalized-collect.md) · [diary](../../formalized-math-2026-08/diary-formalized-collect.md) | — |
| `import-brecon` | `WIP` | [status](86-import-brecon.md) · [diary](../../formalized-math-2026-08/diary-import-brecon.md) | — |
| `whnf-cache-key` | `WIP` | [status](87-whnf-cache-key.md) · [diary](../../formalized-math-2026-08/diary-whnf-cache-key.md) | — |
| `import-scale` | `WIP` | [status](88-import-scale.md) · [diary](../../formalized-math-2026-08/diary-import-scale.md) | — |
| `import-strings` | `WIP` | [status](89-import-strings.md) · [diary](../../formalized-math-2026-08/diary-import-strings.md) | `Nat.bitwise._unary` is the top root in both (236/500 and 186/400 streams); its stream admits 301 of 302 records and refuses only the declaration, with `TypeMismatch`. It is the **… |
| `coordinator-scratch` | `WIP` | [status](90-coordinator-scratch.md) | — |
| `examples-sweep` | `DONE` | [status](90-examples-sweep.md) · [diary](../../refactor-2026-08/diary-examples-sweep.md) | — |
| `import-wfrec` | `WIP` | [status](91-import-wfrec.md) · [diary](../../formalized-math-2026-08/diary-import-wfrec.md) | `Nat.Linear.Poly.denote_reverse` / `…ExprCnstr.denote_toNormPoly` is now the top root in **both** corpora. Its pair is `Prod.rec.{1,0,0}` (6 args) against `(Nat.brecOn.go.{1} motiv… |
| `kernel-reuse` | `WIP` | [status](92-kernel-reuse.md) | **Exit codes on the inventory examples**, per the coordinator's audit. A named theorem that matches nothing now exits non-zero (`nat_theorem_inventory`, `int_theorem_inventory`); `… |
| `lean-ledger` | `WIP` | [status](93-lean-ledger.md) | The 30 `real` rows are now 94% of the trusted surface and the obvious target; ADR-0456 already names the trigger for building ℚ. Nothing else in the ledger is blocked. |
| `numerics` | `WIP` | [status](94-numerics.md) | — |
| `import-projrec` | `WIP` | [status](95-import-projrec.md) | — |
| `solver-decomp` | `WIP` | [status](96-solver-decomp.md) | — |

