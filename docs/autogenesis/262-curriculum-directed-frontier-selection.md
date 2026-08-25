# 262 — Choosing autogenesis targets from the curriculum DAG

Date: 2026-08-24

## Result

Target selection in this programme is currently by **proof-graph locality**: a
fact is a candidate when every `depends_on` is settled. Measured today, that
selection principle yields

```
scripts/fact-frontier.py --json
  ready total: 141   admissible: 0   selected: None
  outcome: refused-no-admissible-candidate
```

— **141 dependency-ready facts, zero dispatchable**, every one rejected
`no-registered-operation`. The registry covers 30 facts, all of them already
settled: **30-of-30 on proved work, 0-of-138 on anything open.**

Locality also has a recorded failure mode. Doc
[`228`](228-capsule-lane-retrospective.md): *"Nine of the ten most recent
operations are Fibonacci/gcd. Picking the adjacent theorem is how a lane ends up
with nine capsules and zero generality."*

`docs/curriculum/curriculum.toml` is a **non-local** selection principle that
already exists: 23 nodes, 37 prerequisite edges, four layers, derived backward
from three destinations, gated for acyclicity by `axeyum-scenarios::mathtour`
and for exercise coverage by `scripts/check-curriculum-coverage.py`. It says
what a destination *requires*, independent of what happens to sit next to what
in an imported corpus.

This document is the crosswalk between the two, and it is mostly a record of
how far apart they are.

## The measurement

Nursery families mapped onto curriculum nodes. The mapping is **arguable and
deliberately stated in the open** — it is a judgement, not a derivation, and
disagreeing with a row is the point of writing it down.

| Curriculum node | Layer | Status | Nursery rows |
|---|---:|---|---:|
| `modular-arithmetic` | 2 | covered | 40 |
| `counting` | 2 | covered | 35 |
| `divisibility-and-euclid` | 2 | covered | 30 |
| `number-theory` | 3 | covered | 21 |
| `naturals` | 1 | covered | 18 |

**Five of 23 nodes carry all the pressure**, and every one is in the ℕ/ℤ
arithmetic corner.

### Gap 1 — nursery rows with no curriculum home: 72 of 216 (33%)

| Orphan family | Rows |
|---|---:|
| `natural-logarithm` | 21 |
| `natural-bitwise` | 19 |
| `natural-fibonacci` | 16 |
| `integer-fibonacci` | 16 |

A third of the evaluation population is aimed at subjects the curriculum does
not name. Two readings, and they are not equivalent:

- the curriculum is **missing nodes** — logarithms, binary representation and
  linear recurrences are real topics, and this repository has landed
  `Nat.testBit`/`Nat.size`/`sum_testBit_eq`, `Nat.fib`/`fib_add`/`fib_cassini`
  and `Nat.catalan` in the last day; or
- those rows are **not worth pursuing**, and the nursery inherited Mathlib's
  shape rather than a chosen one.

**Neither reading is free.** Adding a node obliges an exercise family and a
negative control (`check-curriculum-coverage.py` reports
`covered=19|running=19|with_negative_control=19`). Declining the rows shrinks a
preregistered blind population, which is an amendment, not an edit —
`ADR-0542` and the held-out isolation gate exist for exactly that.

### Gap 2 — curriculum nodes with zero nursery pressure: 18 of 23

```
L0  propositional-logic  predicate-logic  proof-methods  induction
    sets  relations-and-functions  cardinality
L1  integers  rationals  reals  complex
L2  groups  rings  fields  polynomials  sequences-and-limits
L3  linear-algebra  calculus
```

**Both remaining destinations are here.** `linear-algebra` is marked `covered`
with `computable` decidability and has **zero** rows in the evaluation
population; `calculus` is `lean-horizon` and likewise zero. The curriculum names
them as the point of the whole tour and autogenesis has no path to either.

This is the sharper of the two gaps, because it is not a labelling question. A
producer cannot be evaluated against a population that contains nothing from the
subject it is meant to advance.

## How to use this to choose

The two selection principles answer different questions and should be composed,
not swapped:

| Question | Answered by |
|---|---|
| *Which subject should the next capability serve?* | the curriculum DAG — a node on a path to a destination |
| *Which specific row inside that subject?* | `fact-frontier.py` — dependency-ready, partition-legal |
| *Is the capability general?* | `gen-production-provenance-ledger.py` — `facts_via_multi_target` |

Concretely, the decision procedure this document proposes:

1. **Pick a curriculum node on an unfinished path to a destination.** Prefer one
   whose `decidability` is `computable` or `decidable`; `bounded` nodes cap what
   a self-checking exercise can establish, and `DEPTH.md` explains why.
2. **Read its nursery pressure from the table above.** Zero pressure means the
   next action is population work, not producer work — and that is a finding,
   not a blocker.
3. **Ask what the next three targets in that node share.** Doc 228, item 2:
   if the answer is "nothing — each needs its own route," that belongs in a
   decline record rather than in three more capsules.
4. **Register the operation against all of them.** `applicability.fact_ids`
   takes a list and nothing ever required length one.
5. **Check the generality counter moved.** If `facts_via_multi_target` is
   unchanged, the work did not produce; that is the one number doc 228
   installed and the one it says to watch.

## Amendment, 2026-08-24 — `covered` never meant kernel-proved

**A lane refuted the reading this document was first written under, and the
correction sharpens it.**

The original framing measured *kernel theorems per curriculum node* and read a
zero as "covered on paper only". That is wrong. `covered` is re-derived by
`scripts/check-curriculum-coverage.py` from a realized **`axeyum-scenarios`
family** — `polynomials` names `Family::Polynomial`, fixed-degree BitVec
exhaustive and witness self-checks over the **solver**. It has always meant
"this node has a self-checking exercise family", and never "this node has kernel
theorems".

So the 18 zero-pressure nodes are **not unbacked**. They are

    backed on the SOLVER route (scenarios, decide-and-check)
    empty  on the KERNEL route (proved theorems)

which is the ADR-0033 double-duty split doing exactly what it was designed to
do: the same artifact teaches a concept *and* tests a theory. But **testing a
theory and proving a theorem are different evidence routes**, and the
autogenesis loop is a kernel-proving loop. So it is the kernel-side zero, not
the coverage flag, that binds this programme.

Restated, the two gaps are:

| | measured |
|---|---|
| Gap 1 | 72 of 216 nursery rows (33%) name subjects no curriculum node names |
| Gap 2 | 18 of 23 nodes are solver-backed and kernel-empty, **both destinations among them** |

The decision procedure below is unchanged; step 2 should read *nursery pressure
and kernel theorems* rather than "coverage".

**This amendment exists because the document was wrong in a way its own tables
could not show.** The counts were right; what they meant was not — the same
error doc `233` recorded about itself and kept rather than deleted, for the same
reason.

## Second amendment, 2026-08-25 — the kernel-empty half of Gap 2 moved

The first amendment said 18 of 23 nodes were "solver-backed and kernel-empty."
Five of those nodes are no longer kernel-empty. Measured from the `nat` prelude's
`theorem_names` list — **not** by grepping source, which returns zero against
real declarations because names are interned `NameId`s:

| Curriculum node | Kernel theorems before | After | What landed |
|---|---:|---:|---|
| `sets` | 0 | 28 | union/inter/compl/diff, the counting laws, 13 pointwise Boolean-lattice laws, and `Subset` as a **partial order** joined to the lattice |
| `groups` | 0 | 4 | `IsGroupOn` (bundled predicate — this kernel has no typeclasses), uniqueness of identity and inverses, left cancellation, and **ℤ/n under addition** as a worked instance |
| `relations-and-functions` | 0 | 5 | `ReflexiveOn`/`SymmetricOn`/`TransitiveOn`/`EquivalenceOn`, `eq_equivalence_on`, `modEq_equivalence_on` |
| `cardinality` | 0 | 1 | the two-bound `pigeonhole` — genuinely not the same statement as `finite.rs`'s one-bound self-map lemma |
| `polynomials` | 0 | 4 | `Rat.pow`, `polyEval` and its laws; then the ℚ diagonal/rectangle toolkit |

`sequences-and-limits` gained `converges_squeeze` and the `sumRange` sample-rate
law. **Both destinations are still kernel-thin**: `linear-algebra` has the
`dotN` inner product and Cauchy–Schwarz, `calculus` has the derivative and
eleven theorems, and neither has nursery pressure. Gap 2's sharper half — a
producer cannot be evaluated against a population containing nothing from its
subject — is unchanged.

**Two findings from working the nodes are worth more than the counts.**

*A missing type is the binding constraint, not missing effort.* There is no
`List`, no `Finset`, and no product type, so a permutation cannot be encoded as
a group element, `polyEval_mul` cannot be stated without vanishing hypotheses,
and Lagrange's identity at general `n` is unstatable. Every one of those was
discovered by a lane trying to prove the theorem, not by planning.

*A brief can ask for a false theorem.* `polyEval (conv a b) (m+n-1) x =
polyEval a m x * polyEval b n x` is false for arbitrary coefficient functions —
`conv` sums the full antidiagonal, including points outside the `m x n`
rectangle. A lane refuted it with a kernel-confirmed counterexample rather than
failing to prove it, which is the outcome this document should want from a
target it names: **a node's frontier is characterised as much by what is false
there as by what is proved.**

## Third amendment, 2026-08-25 — the refusal in the Result section is no longer true

This document opens by quoting

```
ready total: 141   admissible: 0   selected: None
outcome: refused-no-admissible-candidate
```

as its central finding. That measurement has changed, and the sentence it was
evidence for — *"the registry covers 30 facts, all of them already settled"* —
was the actionable half all along:

```
ledger: 435 facts   entries: 196 (open=191)
selection.outcome: "selected"
selection.admissible_fact_ids:
  F:ml430-nat-modeq-refl-d870c8f5
  F:ml430-nat-modeq-symm-0a3d4d18
  F:ml430-nat-modeq-trans-ef9d1c46
```

One registered operation did it — `authoritative-mathlib-nat-modeq-family-v1`,
naming **three open, dependency-ready facts**. What makes it a producer rather
than a longer dispatch table is a real shared-shape analysis:
`producers::modeq_family` never mentions `Int`, `Nat`, `ModEq` or `%`. It peels
Pi binders into hypotheses and closes an `Eq`/`Iff`-headed goal by
refl/symm/trans reconstructed from `Eq.rec`, and both `Int.ModEq` and
`Nat.ModEq` unfold transparently to `a % n = b % n`. Equally important, the
registration says which siblings it does **not** cover — `add-left`, `neg`,
`dvd-iff`, `of-mul-*` need congruence reasoning the producer lacks — because a
list that overclaims is the dispatch-table defect with extra entries.

**This does not mean the loop closes.** Selection is the first arrow, not the
last: the operation says a fact is *dispatchable*, and the registration moved no
`epistemic_status` — `open` stayed at 191, and `ledger_writes` is 0. Whether the
producer's output is admissible as `proved` is a separate question and is being
asked separately.

**What the counts in this document should be read as, going forward.** The
ready-total is a property of the LEDGER and grows as facts are registered
(141 → 196 as the ledger went 362 → 435). The admissible count is a property of
the REGISTRY. They move for unrelated reasons, and conflating them is what made
"141 ready, 0 admissible" read as a frontier problem when it was a registry
problem.

## Fourth amendment, 2026-08-25 — the producer wall is WHNF opacity, not a missing capability

The loop is now code-complete: `fact-frontier.py` selects,
`execute-autogenesis-operation.py` re-derives and emits a receipt that survives
a re-signed cross-target forgery, `prepare-autogenesis-fact-transaction.py`
produces a checkable transaction. So the bottleneck moved, and it is worth
naming precisely, because two successive measurements framed it differently and
the second one is right.

**The autonomy metric, measured:** 291 established facts, **8 via an operation
covering more than one fact**, 21 via single-target capsules, 262
hand-constructed or imported. Two authoritative multi-target producers exist.
The machinery is not the constraint; producer *reach* is.

**First framing (correct but incomplete).** A lane walked all 10 open train
`natural-factorial` rows and all 9 `natural-fibonacci` rows against
`bounded_induction.rs` and found none reachable, attributing most of it to a
missing **order-side residual generalization** — `close_order_terminal` has no
analogue of the Eq-side `try_absorbing_argument`, so any inequality whose gap is
a symbolic quantity is out of reach. It noted the doc records that mechanism was
*built and deliberately reverted* in `002e7956d` for capacity reasons.

**Second framing (verified, and deeper).** A lane then read that commit, found
the reverted work drove `attempt`'s greedy induction choice into a self-similar
chain that exhausted the shared `MAX_RESIDUAL_LEMMAS` budget for **zero admits**
— and then went past the commit message to probe the actual goals with
`BIS_DEBUG=1` against the real frozen exports:

- `AxNat.factorial (AxNat.succ n)` WHNF-reduces to a `brecOn.go`/`below`
  projection ending in `(...).1 (AxNat.succ n)`. The multiplication
  `(succ n) · n!` **never becomes a separable top-level application** for
  symbolic `n`.
- `AxNat.fib (n+1)` WHNF-reduces to `(Nat.iterate f (n+1) (0,1)).1`. The
  additive recurrence is not definitionally reachable; `fib_add_two` is a
  separately proved lemma.

A residual/absorbing mechanism works on the WHNF-reduced application spine. **If
WHNF exposes no separable structure, no scoping of that mechanism can close
these goals** — building it would reproduce the measured capacity cost with none
of the hoped-for upside. That is a stronger result than "the capability is
missing": the capability would not have helped.

**So the next capability is a different one**, and there are two candidates
worth stating: composing an already-checked auxiliary lemma
(`Nat.fib_add_two`, `Nat.factorial_succ`) as a hypothesis the producer can
rewrite through, rather than re-deriving it structurally; or an introspection
strategy other than plain WHNF-then-app-spine that can see through
`brecOn`/`Nat.iterate` compilation for a generic argument. Neither is a narrow
addition to an existing function.

**The methodological point, which is the reusable part.** The first lane's
diagnosis came from reading the producer and the doc; the second's came from
running the producer against the real goal and looking at what WHNF actually
produced. Both were careful. Only the second could have found that the named
missing capability was not the binding constraint — and it found it by
*probing the artifact rather than the description of the artifact*, which is
this repository's standing rule about tools arriving one level up.

## Fifth amendment, 2026-08-25 — the composition mechanism for the fourth amendment's premise already exists, and it hits the same wall

The fourth amendment named two candidate capabilities and left both
unassessed for buildability. This amendment settles the first — "composing an
already-checked auxiliary lemma (`Nat.fib_add_two`, `Nat.factorial_succ`) as a
hypothesis" — by measurement rather than design, and the answer is narrower
than either "buildable" or "missing."

**The premises exist, in two forms.** `prelude_theorem_inventory
--include-constructed --release` lists both, axiom-free, in this kernel's own
hand-built `nat_prelude`:

```
Nat.factorial_succ   ((x0 : AxNat) -> Eq AxNat (AxNat.factorial (AxNat.succ x0)) (AxNat.mul (AxNat.factorial x0) (AxNat.succ x0)))
Nat.fib_add_two      ((x0 : AxNat) -> Eq AxNat (AxNat.fib (AxNat.succ (AxNat.succ x0))) (AxNat.add (AxNat.fib (AxNat.succ x0)) (AxNat.fib x0)))
```

`Nat.fib_add_two` is additionally an already-**proved ledger fact**
(`F:ml430-nat-fib-add-two-b86e0c82`, route `bounded-iterate-recurrence-v3`,
`crates/axeyum-lean-import/examples/nat_fib_iterate_recurrence.rs` — an
independent re-derivation through `Nat.iterate` unfolding, not composition).
`Nat.factorial_succ` is not itself a tracked nursery fact.

**Neither is available to the producer as it stands, because the producer's
kernel imports only definitions.** `import_statement_ndjson` builds an
isolated per-goal kernel from a proof-free adapter (`proof_declarations_allowed:
false`), and its dependency closure is the STATEMENT's definitional closure
only. Measured directly (not by grepping ndjson text) on the real, existing
`descfactorial-one.ndjson` export: `{"Constructor": 10, "Definition": 31,
"Inductive": 9, "Recursor": 9}` — **zero Theorem, zero Axiom, zero Opaque**
among its 59 admitted declarations. No existing export for any open
`natural-factorial`/`natural-fibonacci` fact carries a citable premise theorem,
by construction of the adapter contract, not by omission.

**A general mechanism for bridging that gap already exists and is already
decided: ADR-0523, accepted 2026-08-20.** Cross-kernel theorem composition
(`axeyum_lean_import::compose_checked_theorem_slice`) takes a source kernel, a
target kernel, and named theorem roots, reuses shared-name declarations by
kernel-type-shape compatibility, imports missing closure members only when
they are themselves checked theorems, and publishes only after the TARGET
kernel's own `Kernel::add_declaration` independently rechecks the rebuilt
proof — i.e. re-derives, never just cites. It is already used in production,
~20 times, composing real Mathlib theorem names (`Nat.add_comm`,
`Nat.gcd_dvd_left`, …) alongside `nat_prelude`-sourced lemmas, for facts
including `F:ml430-int-fib-add-two-739358dd` and `Nat.gcd_fib_add_self`. **So
the architectural question this document's fourth amendment posed — is a
premise a new manifest kind, an extra field, or a different mechanism
entirely — is already answered by precedent, and no new ADR is needed for the
mechanism itself.**

**Measured directly against two of the real open facts, that mechanism
reaches the same wall `bounded_induction.rs` does, for two distinct
reasons.** Built two new proof-free adapters
(`scripts/lean/autogenesis_statement_adapter_nat_factorial_pos_v1.lean`,
`…_nat_fib_le_fib_succ_v1.lean`), compiled and exported them against the
pinned Mathlib v4.30.0 checkout on s5 exactly as the existing manifests'
`reproduction` field prescribes, and ran `compose_checked_theorem_slice`
against the resulting real, freshly-exported isolated kernels (ndjson mirrored
to `/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-premise-composition-probe-v1/`,
`sha256:f0624c7f…` and `sha256:d1af65c0…`):

- **`F:ml430-nat-factorial-pos-f1dd2405`** (`∀ n, 0 < n.factorial`) composed
  against `Nat.factorial_succ`: `bounded_induction_operation` alone declines
  first (`"terminal goal is not definitionally equal and no applicable
  induction-hypothesis rewrite closed the gap"`, confirming the goal is
  genuinely open to the existing producer). `compose_checked_theorem_slice`
  gets much further — it resolves the closure and reuses the shared `Nat`
  family by type-shape — then fails at the target kernel's own recheck:

  ```
  DeclarationValueMismatch {
    declared: "(x0 : AxNat) -> Eq AxNat (AxNat.factorial (AxNat.succ x0)) (AxNat.mul (AxNat.factorial x0) (AxNat.succ x0))",
    inferred: "(x0 : AxNat) -> Eq AxNat (AxNat.mul (AxNat.factorial x0) (AxNat.succ x0)) (AxNat.mul (AxNat.factorial x0) (AxNat.succ x0))"
  }
  ```

  `nat_prelude`'s own `Nat.factorial_succ` proof is `rfl`-shaped (its own
  `factorial` is a plain recursor, one iota step). Retargeted at Mathlib's
  `Nat.factorial` — compiled through `brecOn`/`below`/`PProd` course-of-values
  recursion, reconstructed faithfully by this kernel's importer — the LHS
  `AxNat.factorial (AxNat.succ x0)` does not WHNF-reduce to the RHS in THIS
  kernel, so the declared type and the rebuilt proof's inferred type diverge
  at exactly the point the fourth amendment's `BIS_DEBUG` probe stalled. This
  is the **same wall**, confirmed through a **second, independent code path**
  that does not go through `bounded_induction.rs`'s search at all — it is a
  property of what this kernel's `def_eq` can and cannot see through `Nat.factorial`'s Mathlib-compiled form, not an artifact of one producer's
  scoping.
- **`F:ml430-nat-fib-le-fib-succ-d1ef4a3d`** (`∀ n, Nat.fib n ≤ Nat.fib (n+1)`)
  composed against `Nat.fib_add_two`: a **different** failure. `nat_prelude`'s
  own `Nat.fib` is built over an internal `AxNat.fibAux` accumulator, which
  has no Mathlib-imported counterpart to reuse — Mathlib's `Nat.fib` compiles
  through `Nat.iterate`, not an accumulator recursor of this shape — so the
  rebuilt proof's inferred type is stated over `AxNat.fibAux` where the
  declared type is stated over the target's own `AxNat.fib`, and admission is
  rejected the same way. This is a **representational mismatch between two
  independently-authored constructions of the same function**, distinct from
  the factorial probe's WHNF-opacity wall, but with the identical practical
  consequence: `nat_prelude`'s own proof of the recurrence does not transfer.

**What this narrows the finding to.** The fourth amendment framed the choice
as "compose a premise" vs. "a smarter introspection strategy," as if the first
were the cheaper option once found feasible. It is not cheaper: composing a
`nat_prelude`-sourced premise requires that premise's OWN proof to survive
re-derivation against Mathlib's independently-compiled representation of the
same function, and for both `factorial` and `fib` it does not, for two
different structural reasons. The one case where composition-style reasoning
already closed a real fact (`fib_add_two` itself, via
`bounded-iterate-recurrence-v3`) did NOT compose an existing premise at all —
it independently re-derived the recurrence by reasoning through `Nat.iterate`
directly, i.e. exactly the fourth amendment's SECOND candidate ("an
introspection strategy other than plain WHNF-then-app-spine"), not the first.
That is now measured evidence, not conjecture, that the second candidate is
the one with a working precedent and the first does not have one yet for
either target family.

This does not close the question for every open fact in these two families —
`Nat.factorial_succ`'s own `brecOn` shape and `Nat.fib`'s `Nat.iterate` shape
are two specific compiled forms among others Mathlib may use elsewhere — but
it means the next concrete step for `natural-factorial`/`natural-fibonacci`
is not "wire composition into `bounded_induction.rs`"; it is either (a) a
kernel-level fix to how this kernel's `whnf`/`def_eq` handles
`brecOn`/`below`-compiled course-of-values recursion (out of scope for this
document — `crates/axeyum-lean-kernel/` is not this lane's to touch), or (b)
more `Nat.iterate`/well-founded-shaped producers in the style of
`bounded-iterate-recurrence-v3`, generalized past its current single-target
registration (`authoritative-mathlib-nat-fib-add-two-receipt-v1` covers
exactly one fact) into something that earns a nonzero
`facts_via_multi_target` count the way `authoritative-mathlib-nat-modeq-family-v1`
already did for a different shape.

## Boundary

This document **selects nothing and authorizes nothing.** It adds no operation
applicability, no fact status, no admission authority, and no partition change.
It does not measure expected proof yield, cost, or downstream mathematical
value, and it does not assert that any curriculum node is reachable.

The family→node mapping is a **stated judgement**, not a derivation. It is not
gated, and it should not be gated until someone is prepared to defend each row;
a crosswalk that cannot be argued with is the checker-that-cannot-fail defect in
a different costume.

The counts are reproducible from `docs/curriculum/curriculum.toml` and
`artifacts/autogenesis/nursery-v1.json` at this commit. If either moves, the
tables here go stale and say nothing about it — which is why they carry no gate
and must be re-measured before being quoted.

## What this does not resolve

The frontier is empty for a reason this document does not touch: **no registered
operation covers any open fact.** Choosing a better subject does not create a
producer. The loop demonstrably closes end to end — two facts proved by a
model-chosen plan and checked by an independent second kernel — and wrote
nothing, because a transaction requires a registered operation and none covers
the `Nat.ModEq` family. That registration is a human decision and remains the
binding constraint.

What the curriculum DAG changes is **which** registration to make next, and
whether it is chosen from the neighbourhood or from a path to somewhere.
