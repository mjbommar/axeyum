# Lane: attestation — can the content-free routes transcribe, and do they now

<!-- plan-section: lane-status -->

**Yes, for 95 of the 124 — it was how the emitter was written, and both the
emitter and a checker that can fail have landed** (`WIP`, attestation,
2026-08-18).

Lane `agent-binding-coverage` measured that 124 of the corpus's 270 rendered
Lean modules transcribe nothing: their entire vocabulary is
`α atom._N func._N Eq.{1} Not And`, a fresh vocabulary with no declared
relationship to any query symbol. It was right not to "cover" them. The
question this lane took is the next one: **is that abstraction necessary, or is
it how the emitter was written?** Measured per route, it is both, and the split
is sharp.

| n | route | why the module said nothing | now |
| --- | --- | --- | --- |
| 89 | `ArrayAxiom` | the emitter collapsed each whole term into ONE opaque constant | **structural**, checked |
| 6 | `QfAbv`, `QfUf` | nothing — they were structural all along, and were misfiled | **structural**, checked |
| 13 | `ArrayAxiom`, `TermIdentity` | both sides genuinely are bare query leaves | attested |
| 9 | `Sos` | the real reconstructor declined and a `prop._0` wrapper fired | attested |
| 4 | `FiniteArrayExtensionality` | the same nothing, under a conjunction | attested |
| 2 | `ArrayAxiom` | the rendered term is the output of a **rewrite** | attested |
| 1 | `ArrayAxiom` | *self-refuting* — its `False` needed no hypothesis | **declines** |

**`ArrayAxiomRefutationCertificate` carried the query's own `TermId`s the whole
time.** `array_axiom_term_expr` turned each whole term into one opaque constant
keyed by its arena index, so `select(store(a, i, v), j)` reached Lean as
`atom._0` — and, measured and now a test, read-over-write and select-over-ite
rendered the *same module, byte for byte*. So did every other instance the route
certified. Size was never the reason: over the whole corpus the combined
`lhs`/`rhs` tree is 10 nodes at the median and 156 at the maximum. The route now
renders the query's syntax into the EUF carrier — one constant per distinct
leaf, one `α → … → α` function per distinct operator — keyed so one query symbol
is one constant wherever it occurs. The proof term is unchanged; only the
statement stops being empty.

**A third verdict, `structural`, and it can fail.** Binding an array hypothesis
to an `(assert …)` line would be a check with no true instance: for 89 of the
105 queries the route certifies, no assertion says `¬(lhs = rhs)` at all — the
hypothesis is the *conclusion of a congruence derivation*. What does hold, and
is now required, is one step weaker and still sharp: **every term the module
equates is a subterm of the `.smt2` file, under one injective correspondence
between the module's opaque names and the file's own symbols, literals and
operators.** `structural=95 structural_nodes=2982 structural_caught=359`. Every
structural module is corrupted four ways on every run — swap two arguments, drop
one, retarget a leaf, collapse two constants — and 359 of 372 corruptions stop
being subterms of their own query. The 13 accepts are the same legitimate class
the arithmetic binder already has.

**The guard that keeps the classes honest is the anti-absorption one**: an
instance pinned `attested` now FAILS if the structural binder can relate it to
the query. Without it, a renderer that started transcribing would leave every
pinned attestation green while `transcribes NOTHING` quietly stopped being
true — which is exactly what had already happened to the 6 `QfAbv`/`QfUf`
instances, structural all along and classified content-free by a check that read
vocabulary rather than shape.

**The self-refuting module was a real defect, not a curiosity.**
`neg-no-self-negating-proposition.smt2` is `(not (not (= p (not p))))` — no
array anywhere. It reached `ProofFragment::ArrayAxiom` because the
read-congruence probe collects `p ≡ ¬p` and `conflicting_bool_negation_`
`equalities` scanned the class for a term equivalent to `inner`, found `inner`
itself, and reported the pair `(p, p)`. The conflict is *Boolean*, and
`¬(lhs = rhs)` is not something that query asserts, so no honest pair exists
here at all: the fix is a decline. `array_axiom_refutation` now refuses a
degenerate certificate outright, which also keeps it out of
`Evidence::UnsatArrayAxiom`. Re-running the search — what
`check_array_axiom_evidence` does — could never have caught this, because it
produces the same degenerate answer again. The query is still `unsat`, now via
`TermLevelEnum` with `certified=1`.

**The 28 that remain are measured, not assumed** — each was run through the
binder and refused. Two of them are the general problem in miniature and worth
naming: `redand-eliminate.smt2` asserts `(bvredand x)` while the certificate is
about `bvcomp x (bvnot #b000000)`, and `ext10.btor.smt2` asserts
`(ite (= a0 a0) …)` while the arena folds `(= a0 a0)` to `true` at
construction. **The rendered term is the output of a rewrite, not of the source
text.** To bind those one must certify the *rewrite* as well as the
transcription, which is a different object: a rewrite-step certificate.

**Next, in measured order.** (1) `Sos`, 9 instances: the route already HAS a
real reconstructor (`reconstruct_sos_proof` → `gate_and_render_lra_module`,
which renders `Real.*`), and the `prop._0` wrapper is its
`UnsupportedTerm` fallback. It is reached by exactly one file in the corpus. So
this is not a necessary abstraction either — it is the missing degree-2 ring
normalizer, and it lands on `ordered_ring.rs`, which `agent-r3-telescope` owns.
(2) The 13 bare-leaf instances: binding them needs the *disequality* anchored to
an assertion, not just the terms. (3) The 2 rewrite-output instances, which need
the rewrite certified.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `3076b6ae0` | the one Lean module `rfl` refuted on its own: root-caused to a degenerate `(t, t)` witness, the route now declines, and a self-refuting attestation FAILS the run instead of being counted |
| 2026-08-18 | `8e4894de4` | `ArrayAxiom` renders the query's own terms; a third `structural` verdict binds 95 modules to their query's subterms, 359 of 372 corruptions caught, and the attested class drops 124 → 28 with an anti-absorption guard |
