# Lane: ordered-ring-reconstruct — refutations that assume nothing

<!-- plan-section: lane-status -->

**Lane state (`DONE`, ordered-ring-reconstruct, 2026-08-15).** ADR-0456 measured
that the `Real` package is an **ordered commutative ring with 1** and named the
route that eliminates its 30 axioms without constructing a carrier: parameterise
the consumer, not build a model. That route is now built and measured
(ADR-0457, [`diary-ordered-ring-reconstruct.md`](../../mathematics-2026-08/diary-ordered-ring-reconstruct.md)).

`generalize_over_ordered_ring`
(`crates/axeyum-solver/src/reconstruct/arithmetic/ordered_ring.rs`) λ-abstracts
the 30 `Real` declarations, the per-variable constants and the per-constraint
hypothesis axioms out of a finished, kernel-gated proof term, in dependency
order, with every binder type computed from the environment. The kernel then
infers the statement:

```
∀ (R : Sort 1) (add mul : R → R → R) (neg : R → R) (zero one : R)
  (le lt : R → R → Prop), <the 22 laws> →
  ∀ (x0 : R), le (add x0 zero) zero → le (add (neg x0) (add one zero)) zero → False
```

**Measured `axiom_footprint`: empty**, on all five fixtures (three Farkas shapes,
a strict cycle, a sum-of-squares). The un-generalized theorem's footprint is
printed beside it on the same run — 18, 22, 24, 7, 10 — so the zero
discriminates. **Real Lean 4.30.0 agrees**: the committed fixture
`arithmetic-ordered-ring-farkas.lean` declares no `axiom` at all and Lean answers
`'axeyum_ordered_ring_refutation' does not depend on any axioms`.
`check-lean-gate.sh` goes **112 → 113** real-Lean checks (floor 105 unchanged).

**Nothing is lost.** Instantiating at `Real` — applying the theorem to the 30
constants and the refutation's own variable/hypothesis axioms — is a term the
kernel accepts against `False`, recovering the original statement with its
original trusted base; under the tight telescope the recovered footprint is
identical name for name. Recorded as `F:ordered-ring-farkas-refutation`, route
`kernel-lean`, `axiom_footprint: []` (`validate-facts.py`: kernel-lean 31 → 32,
axiom-free 30 → 31).

**`real: axiom=30` is untouched, deliberately** — reducing the trusted base was
never the goal. What changed is that no reconstructed refutation *depends* on it;
the 30 are now used only to instantiate. Of the 30, 21 are reached by at least
one fixture; the nine never reached are `le_trans`,
`mul_le_mul_of_nonneg_left`, `add_lt_add_of_le_of_lt`, `mul_comm`, `mul_assoc`,
`mul_one`, `mul_zero`, `left_distrib`, `mul_nonneg`.

**Next, for whoever picks this up.** (1) Fix the facade dispatch so an SMT-LIB
QF_LRA `unsat` reaches `ProofFragment::Lra` instead of the contentless `LraDpll`
shim — generalizing the shim would produce an axiom-free theorem that says
nothing, so the entry point is still the direct reconstructor. (2) Try the 5 MB
schedule-deadline core through the generalization and find out what it costs;
this lane did not, and does not imply it works. (3) The hypothesis-footprint gap
is still open: the binders are visible in the statement now, but nothing checks
that they are the rows they claim to be.

<!-- plan-section: landed-changes -->

| 2026-08-15 | `ordered-ring-reconstruct` | Farkas/SOS refutations generalize over the ordered-ring interface: empty `axiom_footprint`, confirmed by real Lean's `#print axioms`, with the `Real`-specific statement recovered by instantiation (ADR-0457, `F:ordered-ring-farkas-refutation`). |
