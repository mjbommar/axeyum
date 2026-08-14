# Lane diary: certified infeasibility with a minimal explanation

**Lane `infeasibility`, 2026-08-14.** Operations research: scheduling,
rostering, load planning. The question this lane exists for is not "find me a
plan" — it is *"there is no plan, and **why**."*

Commercial MILP solvers sell IIS (irreducible infeasible subsystem) computation
for exactly this. What they hand back is a list of row names and a number you
must trust. The offer here is the list, the ratio, **the measurement that the
list is irreducible**, and — for the linear-real instance — a proof term an
independent kernel type-checks.

---

## 1. What was already in the tree, and what was not

Three pieces existed and had never been pointed at an OR instance:

- `get-unsat-core` at the SMT-LIB front door (`crates/axeyum-solver/src/smtlib.rs`),
  documented as deletion-minimized;
- Farkas certificates out of `lra.rs` (`FarkasCertificate`, with a from-scratch
  `verify()`), consumed by the Alethe `la_generic` route and by interpolation;
- `reconstruct_lra_proof` (`crates/axeyum-solver/src/reconstruct/arithmetic.rs`),
  which turns a Farkas certificate into a Lean kernel term.

What did **not** exist: any instance to point them at, and any check that the
"minimized" core is actually minimal.

That second gap is the substance of this lane. `axeyum_solver::unsat_core` is
deletion-based, and deletion-based minimization yields an irreducible core *only
if every trial decides definitively*. Its loop conservatively **keeps** a row
whose removal leaves the remainder `unknown` — the right call for soundness, and
it means the returned subset is a core whose minimality is a **hope**, not a
result. Nothing anywhere re-solved a leave-one-out subset. In scheduling the
minimality is the entire product: "these 5 of your 102 rows contradict" is an
explanation; "these 102 rows contradict" is the input restated.

So the rule for this lane was: **irreducibility is measured or it is not
claimed.**

## 2. The instances

`scripts/gen-infeasibility-instances.py` emits three committed artifacts under
`artifacts/instances/infeasibility/`. They are committed rather than generated
by a test, so the evidence is replayable; the generator is committed too, because
a 102-assertion roster written by hand is unreviewable — nobody could confirm
that the *only* contradiction is the advertised one.

Every instance is built to one rule: **the contradiction must be buried.** The
instance minus its explanation has to be genuinely satisfiable, and the
explanation has to be a small fraction of the rows. That property is checked, not
assumed (`instance minus core` must decide `sat`, with the model replayed).

| instance | model | rows | core | ratio |
|---|---|---:|---:|---:|
| `roster-icu-night.smt2` | ICU night roster, 6 nurses x 7 nights, QF_LIA | 102 | 5 | **4.9%** |
| `loadplan-hazmat.smt2` | outbound load plan, 12 pallets x 5 trucks, QF_LIA | 90 | 14 | **15.6%** |
| `schedule-deadline.smt2` | project schedule, 20 tasks, continuous time, QF_LRA | 60 | 5 | **8.3%** |

**Roster.** Thursday night needs one ICU-certified nurse. Alice is on approved
leave, Cara is in mandatory recertification, and Bob is pinned to the Wednesday
handover — so the consecutive-night rest rule takes him off Thursday too. Five
rows, none of which mentions the other four. Note what the infeasibility is
*not*: certified capacity is 9 night-shifts against a requirement of 7, so there
is no staff-hours shortage to find by counting.

**Load plan.** Three class-3 dangerous-goods pallets, two ADR-certified trucks,
and a segregation rule capping each truck at one class-3 pallet. Total payload is
3500 kg against 6000 kg of capacity — the five weight rows appear in no core,
which is why they are there.

**Schedule.** The long-lead casting for `t03` lands day 6; from there the chain
`t03 -> t06 -> t09 -> t12` is 5 + 6 + 3 days of work followed by `t12`'s own 4.
Delivery cannot be before day 24 against a 20-day promise.

## 3. The measurement

`crates/axeyum-solver/examples/infeasibility_iis.rs` runs five checks per
instance and exits non-zero on any of them:

1. the whole model decides `unsat`;
2. the front door's `(get-unsat-core)` names are all real `:named` rows, and
   agree with the term-level `unsat_core` (one check of the plumbing between
   them, not two independent derivations — they share the deletion loop);
3. the core **alone** re-decides `unsat`;
4. for every member `m`, `core \ {m}` decides **`sat`** — and the returned model
   is **replayed** against the very terms it claims to satisfy, by
   `check_model` (the IR ground evaluator, which shares no code with the decision
   procedure). `unknown` here is a **failure**, not a pass;
5. the instance **minus** the core decides `sat`, likewise replayed.

`--expect-rows` / `--expect-core` pin the numbers. This matters: a checker that
prints whatever it found pins nothing. Passing `--expect-core 4` to the roster
exits 1, so the fact ledger's `checker_command` is a ratchet.

**Result: all three cores are measured-irreducible, all leave-one-out subsets
`sat` with replayed models, all three "instance minus core" satisfiable.** Wall
times 0.11s / 0.21s / 0.94s.

`scripts/check-infeasibility-iis-z3.py` re-derives the same five things with z3
4.13.3 alone, sharing no code with us. **z3 returns the identical core on all
three instances** and agrees on every leave-one-out verdict. It is deliberately
*not* a `checker_command`: a gate needing `z3` on PATH would either fail on a
machine without it or — much worse — be written to exit 0 having done nothing,
which is the inert-gate pattern this repository has shipped several times.

### What the cores rest on, measured rather than named

`produce_evidence` on each core, with `check_outcome` re-run:

| instance | evidence variant | re-check | trust step |
|---|---|---|---|
| roster | `UnsatArithAletheProof` | `verified` | `farkas` — **certified this run** |
| load plan | `UnsatArithAletheProof` | `verified` | `farkas` — **certified this run** |
| schedule | `UnsatFarkas` | `verified` | `farkas` — **certified this run** |

So every core's `unsat` carries an arithmetic refutation that was *re-derived*
this run, not trusted from the emitter. This was better than expected and is why
the facts' `axiom_footprint` names a checker rather than a bare decision
procedure.

## 4. The two core shapes, and why the worse one is in the ledger

`F:roster-icu-night-iis` (4.9%) and `F:loadplan-hazmat-iis` (15.6%) are the two
things an IIS can be:

- a **local collision** of a handful of otherwise-unrelated rows — the
  compression is large, and reading the five rows tells an operator what to do;
- a **global counting argument** in which every participant is necessary. The
  pigeonhole core is irreducible *and* large: drop one exclusion and the pallet
  escapes to an uncertified truck; drop one segregation row and two class-3
  pallets share a truck. All fourteen are load-bearing.

The 15.6% instance is kept precisely because it is worse. Reporting only the
roster would be selecting on the outcome.

It also exposes the honest limit of the whole genre: **an IIS says which rows
collide, not why.** "Three pallets into two trucks" is the reader's inference.
The certificate contains no such sentence.

## 5. How far the Farkas-to-Lean route reached — and the trap on the way

`crates/axeyum-solver/examples/infeasibility_farkas_lean.rs`, on the schedule
core.

**Farkas.** Five atoms, **every multiplier 1** — the textbook negative-cycle
refutation, 6 + 5 + 6 + 3 = 20 against a ceiling of 16, excess 4.
`FarkasCertificate::verify()` re-derives it from scratch in exact rationals and
shares no code with the Fourier–Motzkin elimination that found it. Verified.

**The trap.** The obvious entry point, `prove_unsat_to_lean_module`, routes a
pure-Real conjunctive `unsat` through `ProofFragment::LraDpll`, whose Lean module
is a 21-line **structural shim**:

```lean
axiom axeyum.reconstruct.prop._0 : Prop
axiom axeyum.reconstruct.hyp._1 : axeyum.reconstruct.prop._0
axiom axeyum.reconstruct.hyp._2 : Not axeyum.reconstruct.prop._0
theorem axeyum_refutation : False :=
  axeyum.reconstruct.hyp._2 axeyum.reconstruct.hyp._1
```

It kernel-checks. It is `sorry`-free. It contains **no arithmetic at all** — the
refutation is *asserted* in `hyp._2`, and the module is byte-identical for some
thirty other routes. Reporting this as "the Farkas proof reached the kernel"
would have been false, and it is exactly the shape of claim that passes a casual
review. The example prints and labels both results for this reason. Note that
`scan_arithmetic_proof_fragment` reaches `LraDpll` *before* `ProofFragment::Lra`,
so the genuine Farkas arm is shadowed at the facade for precisely the queries it
was built for. Measured: `ProofFragment::Lra` occurs in the whole tree at exactly
two places, `reconstruct.rs:1611` (where it is produced as the fallthrough) and
`reconstruct.rs:2201` (where it is consumed) — no test anywhere asserts a query
reaches it.

**The real thing.** `reconstruct_lra_proof` called directly **reaches**: the term
`infer`s and its inferred type is `def_eq` to `False`. The module declares 30
axioms — 21 ordered-field prelude, 4 variable axioms (one abstract `Real` per
start time), and **5 hypothesis axioms, one per core row**. The example asserts
that last equality and exits 1 otherwise, which is the closest thing available to
a footprint audit on this route (see the honest gap below).

This is the largest linear-arithmetic reconstruction in the tree. Measured: all
fourteen existing call sites of `reconstruct_lra_proof` outside this example are
in `crates/axeyum-solver/src/reconstruct/tests.rs`, and every one passes an
assertion slice of length 1 (a negative test), 2, or 3. Five constraints over
four variables with non-unit integer constants went through
`try_general_farkas` unchanged.

**Where it stops, precisely.**

1. **The two integer instances have no Farkas route at all.**
   `lra_farkas_certificate` decides linear *real* arithmetic and declines a
   roster or a load plan — "assertion is not a conjunctive linear real
   constraint". That is a fragment boundary, not a missing case. Their cores are
   still measured-irreducible; they just have no path to a kernel. For QF_LIA the
   only genuine integer reconstructors are gcd-infeasible equality systems and
   *single-variable* intervals; anything else lands on the same structural shim.
2. **Nothing dispatches an SMT-LIB file to the genuine reconstructor.** It has to
   be called directly, which is what this example does.
3. **There is no hypothesis-footprint audit for the arithmetic route.** The
   propositional route has `declared_assumption_clauses`; the LRA hypothesis
   axioms are minted as canonical `le L zero` props with generated names and no
   link back to `(>= s_t06 (+ s_t03 5.0))`. Counting them is not checking them.
   The chain *instance rows -> certificate* is audited by `verify()`; the chain
   *certificate -> Lean hypothesis axioms* is not.
4. **Axiom-free is not on offer and cannot be.** `arith_prelude.rs` declares
   `Real` and every field law through `declare_axiom` — no theorems, no
   inductives. `axiom_footprint: []` here would have been a lie the validator
   would have accepted, since it only rejects `[]` *off* the `kernel-lean` route.
   The fact lists all 30 names.
5. **Size.** The proof term is **5,099,060 bytes** for a five-row explanation.
   The prelude has no numerals, so the constant `20` reconstructs as a 20-fold
   `Real.add Real.one` chain, and every cancellation is an explicit `Eq`-rewrite.
   A 5 MB certificate for a five-row contradiction is checkable but not
   shippable; numerals in the prelude are the obvious next lever.

No `lean` binary is on this box, so "kernel-checked" here means *our* kernel's
`infer` + `def_eq False`, not Lean's.

## 6. Why the ledger route is `search-certificate`

The three IIS facts assert a **conjunction of two halves with different trust
bases**: the core's `unsat` carries a re-checked Alethe/Farkas certificate
(clausal-grade), while irreducibility rests on |C| models replayed by the IR
evaluator (witness-grade). `proof_route` takes one value, and the enum's
`search-certificate` — "a combinatorial search whose result carries a replayable
witness or cover" — is exactly this composite. Labelling the composite
`smt-clausal` would advertise a certificate for the half that has witnesses;
promoting `F:schedule-deadline-iis` to `kernel-lean` on the strength of its unsat
half would be exactly the route conflation the field exists to prevent.

The kernel result is therefore a **separate fact** with a narrower statement:
`F:schedule-critical-chain-infeasible`, route `kernel-lean`, footprint of 30
named axioms. `F:schedule-deadline-iis` depends on it.

A note on `formal.language` there: it is `smtlib2`, not `lean4`. The rendered
`theorem infeasible : False` carries no content without its hypothesis axioms —
it is a refutation *of them* — so quoting it as the formal statement would be
uninformative at best.

## 7. What a commercial IIS gives that this does not, and vice versa

**Theirs, not ours.**

- **Scale.** Gurobi/CPLEX compute an IIS on models with hundreds of thousands of
  rows. This lane's deletion loop costs O(n) full solves — 102 solves for the
  roster. It is fine at 100 rows and hopeless at 100,000. Commercial IIS uses
  filtering (elastic/deletion hybrids, additive-deletion) that we have not built.
- **Bound granularity.** They distinguish a *row* from a *variable bound* and
  report `x <= 3` as an IIS member. Here everything is an assertion; a bound is
  only separable if it was written as its own `:named` row (which is why these
  instances do).
- **Mixed-integer reach.** They handle genuine MILP with continuous relaxations,
  cuts, and presolve. Our integer instances are pure-integer and small.
- **Ecosystem.** Row-name round-tripping to LP/MPS files, modelling-language
  integration, IIS-guided repair suggestions.

**Ours, not theirs.**

- **Irreducibility is measured here, not asserted.** The commercial number is
  documented as irreducible; you are not handed the leave-one-out re-solves. We
  run every one and fail if any comes back `unknown`.
- **Each `sat` is a replayed witness**, checked by an evaluator independent of
  the solver. The satisfiable half of "irreducible" does not rest on the solver
  at all — it rests on |C| concrete rosters an evaluator confirms.
- **The `unsat` half carries a re-derived certificate** (Alethe `lia_generic` /
  Farkas), not a solver verdict.
- **For the LRA instance there is a proof term an independent kernel
  type-checks.** No commercial IIS ships that. This is the "check it without
  trusting my solver" claim, and it is real for one of the three instances.
- **Cross-oracle agreement** with z3 on the core *and* on every leave-one-out.

Honest summary of the trade: a commercial IIS is vastly more capable and asks for
trust; this is far smaller and asks for none.

## 8. Next

1. **Numerals in the arith prelude.** 5 MB for five rows is the binding
   constraint on shipping a kernel-checked explanation.
2. **A hypothesis-footprint audit for the LRA route** — bind each `lra.hyp._N`
   back to the originating assertion, closing gap (3) above.
3. **Dispatch order at the facade**, so an SMT-LIB QF_LRA `unsat` can reach
   `ProofFragment::Lra` instead of the `LraDpll` shim.
4. **A filtering IIS algorithm** so the row count can grow past a few hundred.
5. **An integer route.** The two LIA cores have re-checked Alethe refutations but
   no kernel path; that is where the next real capability is.
