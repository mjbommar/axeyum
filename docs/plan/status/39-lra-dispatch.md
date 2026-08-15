# Lane: lra-dispatch — the front door reaches the real reconstructor

<!-- plan-section: lane-status -->

**Lane state (`DONE`, lra-dispatch, 2026-08-15).** Two lanes had measured that
`prove_unsat_to_lean_module` routed a pure-`Real` conjunctive `QF_LRA` `unsat`
through `ProofFragment::LraDpll`, whose Lean module is a 21-line structural shim
(`axiom P`, `axiom Not P`, apply) that kernel-checks, is `sorry`-free, and
contains no arithmetic — and that `ProofFragment::Lra`, the genuine Farkas
reconstructor, had **no test anywhere asserting a query reaches it**. Both are
now fixed, and the second half — a contentless module passing as a proof — was
the larger of the two, because **29** routes share that emitter.
(ADR-0458,
[`diary-lra-dispatch.md`](../../refactor-2026-08/diary-lra-dispatch.md))

**Dispatch.** `scan_arithmetic_proof_fragment` tries a new
`lra_farkas_reconstruction_certifies` arm *before* the lazy-SMT arm. Its
predicate is two gates: a self-checked `lra_farkas_certificate`, then the
**reconstruction itself building and the kernel inferring it to `False`**. The
second gate means the reordering can only move a query from "shim" to
"arithmetic", never to "declined" — a certificate shape the reconstructor does
not cover keeps falling through to `LraDpll`. `lra_term_infers_false` is now
shared by the classifier and `gate_and_render_lra_module`, so the check that
routes a query is the check that later accepts it.

**Measured:** `x < 0 ∧ 0 ≤ x` and `x+y ≤ 0 ∧ 1 ≤ x ∧ 1 ≤ y` reach
`ProofFragment::Lra` through both `scan_proof_fragment` and the front door, and
the emitted module carries `Real.add_le_add`, `Real.lt_irrefl`, one
`lra.hyp._N` per asserted row and one `lra.x._N` per variable. Seven new lib
tests; three existing `LraDpll` assertions flipped to `Lra`. The two cvc5
`QF_LRA` audit rows stay on `LraDpll` (genuinely Boolean-structured), so
`check-lean-gate.sh` is unchanged at 113.

**The shim: kept, marked, and excluded from the honest entry point.** Removing it
was not defensible — it is load-bearing for 29 routes and for those the Rust
certificate genuinely is the evidence. Four changes instead: every attestation
module opens with `-- axeyum-lean-module-content: structural-attestation` and a
warning naming its refuter; `LeanModuleContent` + `ProofFragment::lean_module_content()`
type it in an exhaustive match; `gate_module_content` cross-checks the table
against the rendered artifact on **every** call and refuses a mismatch
(`ReconstructError::ModuleContentMismatch`); and `prove_unsat_to_lean_theory_module`
returns a typed `ReconstructError::NoTheoryContent` decline instead of a module
with nothing in it. `axeyum_property::LeanModule` gained `content()` /
`theory_source()` and `LeanSummary` a `content` field.

**Honest residual:** `prove_unsat_to_lean_module` keeps `(ProofFragment, String)`
— 199 in-workspace call sites — so a caller who ignores the marker, the doc, the
classifier and the strict door still gets a shim. It is no longer possible to do
so without the fact being in hand in three places; it is not type-impossible.

**QF_LIA, scoped not built — and the recorded boundary was in the wrong place.**
Both integer infeasibility instances' **LP relaxations are infeasible**, and z3
4.13.3 returns the identical core from the relaxation (roster 5 rows, load plan
14 rows). Neither refutation needs integrality: each is a rational Farkas
combination, valid in any ordered commutative ring with 1 — the same 22-law
interface `generalize_over_ordered_ring` abstracts over, with ℤ as ADR-0456's
model. What blocks the route is a **sort gate**, not a theory gap:
`lra.rs::is_real` accepts only `Sort::Real` and the `Op::Real*` opcodes. The
slice is therefore "collect `Op::Int*` into the same `LinR` rows, reconstruct
over the ring interface, instantiate at `Int`" — plus a soundness-negative pass
so an LP-feasible integer-infeasible system keeps declining to
`Diophantine`/`IntInequality`.

**On the real instance.** `infeasibility_farkas_lean --require-kernel` on
`schedule-deadline.smt2` (60 rows, 5-row measured-irreducible core) now prints
`facade fragment Lra` / `carries ordered-field content` / `strict facade ACCEPTED
as Lra`, where the `infeasibility` lane had to print `LraDpll` / `STRUCTURAL
SHIM`. That example's own shim detector turned out to be **broken** — it matched
`axiom hyp` where the reconstructor mints `axeyum.reconstruct.lra.hyp._N`, so it
returned "no arithmetic" for a genuine module and had been right only for as long
as the answer was "shim". The second instrument caught it on the first run; it is
now classified on the declared name and type.

**`main` is red on three golden module pins, not this lane's.** The
`--no-fail-fast` sweep is **280 suites / 3,822 passing / 3 failed**:
`quant_affine_growth_lean` (79,801 -> **174,524** bytes),
`quant_eq_partition_lean` (51,989 -> **112,303**), `quant_residue_lean`
(33,339 -> **83,060**). All three reproduce **byte-for-byte in a
`git archive HEAD` snapshot with this lane's files restored from `HEAD`**, all
three assert on direct `int_reconstruct` calls this lane never touches, and all
three roughly double — one upstream change, likely `d326c74af` (WHNF cache key /
K-like reduction). Separately, `F:schedule-critical-chain-infeasible` records 30
axioms (21 prelude) where the example now measures **26 (17 prelude)**; its
`checker_command` still passes because it pins the *hypothesis* count, so the
stale number is in `notes`/`axiom_footprint`. All belong to other lanes.

**Next, for whoever picks this up.** (1) The 28 non-arithmetic structural routes
are marked, not fixed — marking turns a silent misreport into a visible gap.
(2) Multi-clause `DisjunctiveLra`: a two-clause Boolean `QF_LRA` row is outside
both the conjunctive Farkas path and today's one-clause disjunctive path.
(3) The trial reconstruction was not measured on the 60-row `schedule-deadline`
core (a 5 MB term); if it costs, return the built context from the classifier
rather than weakening the predicate. (4) The hypothesis-footprint gap both prior
lanes named is now reachable from the front door, which raises its priority.

<!-- plan-section: landed-changes -->

| 2026-08-15 | `lra-dispatch` | Conjunctive `QF_LRA` reaches `ProofFragment::Lra` at the Lean facade instead of the contentless `LraDpll` shim, with the first tests asserting a query reaches the real reconstructor; structural-attestation modules now self-label, are typed by `LeanModuleContent`, are cross-checked against the fragment table on every call, and are declined by `prove_unsat_to_lean_theory_module`. |
