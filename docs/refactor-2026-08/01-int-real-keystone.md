# 01 — ℤ and ℝ are one hole through every layer

> **STATUS 2026-08-18 (later) — R3 landed, and the distance to `real: 0` is
> longer than ADR-0468's end-state paragraph reads.** That paragraph says the 30
> retire by deletion because "once R3 lands, no consumer references the `Real`
> package, and `build_arith_prelude` can be retired." Measured after R3 landed:
> **18 files still reference `build_arith_prelude`/`ArithPrelude`**, and the
> load-bearing one is `LraReconstructCtx`, whose own doc comment says *"the
> trusted base is `build_arith_prelude`'s axioms"*. Every LRA refutation is still
> stated over the axiomatized `Real`.
>
> R3 is necessary and it is not sufficient. What it removed is the OBSTACLE: the
> proof term no longer mentions `Eq`, `Eq.refl` or `Eq.rec` (gated by
> `residual_eq_constants`), so nothing in it is beyond what a *defined* relation
> can interpret, and the 39-binder form provably specializes back to today's
> statement. What it did not do is change the carrier.
>
> So the real chain to `real: axiom=0` is: **the 15 remaining `CReal` laws → R4
> instantiation → then deletion.** Eight of those need `mul` and seven need `lt`,
> and both were costed as new mathematics rather than transcription. Anyone
> planning against "R3 lands, then delete" should plan against that instead.

> **STATUS 2026-08-18 — ℝ is CONSTRUCTED, and `real: 30` has still not moved.**
> Both halves of that sentence are load-bearing. `crates/axeyum-lean-kernel/src/creal.rs`
> is a Bishop setoid of regular ℚ-sequences over the constructed ℚ: **31
> declarations, trusted surface 0**, `Equiv` reflexive/symmetric/transitive, and
> **7 of the 22 ordered-ring laws** — the additive group in `Equiv` form
> (`add_comm`, `add_neg`, `add_zero`, `add_assoc`) and three order laws verbatim
> (`le_refl`, `le_trans`, `add_le_add`).
>
> The 30 axioms do **not** retire by exhibiting this model. They retire by
> *deletion*, when no consumer references the `Real` package — ADR-0468 phase R3,
> which binds equality as a telescope parameter (`RING_BINDER_NAMES` 30 → 39) so
> a generalized refutation can be instantiated at a carrier whose equality is
> `CReal.Equiv` rather than `Eq`. Until that lands, "ℝ is constructed" and
> "`real: axiom=30`" are both true at once, and reading the first as the second
> is the error this note exists to prevent.
>
> Three costings were corrected by building rather than estimating. The
> Archimedean property of ℚ came in at about a third of its ~750-line estimate.
> `add_zero`/`add_assoc` were costed behind a missing `natDivSucc`-antitone
> lemma that turned out **not to be needed** — read at a common denominator the
> bound is `3/(2n+2) ≤ 4/(2n+2)`. And this document's own claim that "the 13
> order laws restate verbatim" was optimistic: only **3 of 13** were reachable
> without `mul` or `lt`.
>
> What remains is honestly harder than transcription. Eight laws need `mul`,
> whose bound Mathlib derives from `CauSeq`'s *existential* modulus — a fixed
> modulus does not supply it, so that is invention rather than porting. Seven
> need `lt`, and the naive `∃ n, y_n − x_n > 2/(n+1)` does not give `lt_trans`:
> two regularity round trips consume the margin exactly. `lt := Not (le y x)` is
> a dead end, because `le_of_lt` is then not constructive and there is no
> `le_total` over ℝ to recover it from.
>
> The vacuity risk here is severe and axiom footprints cannot see it: every law
> is a statement about inhabitants of `CReal`, so an uninhabited carrier or a
> total `Equiv` would make all of them hold, footprint-free, of nothing.
> `creal_setoid_witness` therefore reports `carrier inhabited`, `Equiv
> discriminates` and `le discriminates`, and its exit status depends on all
> three — verified by mutation, not asserted.

> **STATUS 2026-08-17 — the trusted surface is now `real` ALONE.** Measured by
> `cargo run -q -p axeyum-lean-kernel --example nat_axiom_inventory`, with
> `scripts/gen-lean-axiom-ledger.py --check` green:
>
> ```text
> logic:   axiom=0  opaque=0  quotient=0
> nat:     axiom=0  opaque=0  quotient=0
> integer: axiom=0  opaque=0  quotient=0
> string:  axiom=0  opaque=0  quotient=0   <- was 1
> real:    axiom=30 opaque=0  quotient=0   <- the whole remaining hole
> ```
>
> `string` closed the same day: `append` was an axiom for scope, not necessity —
> `Str` is a recursive inductive whose recursor supports exactly the structural
> definition `Nat.add` uses, so it became a definition with a proved monoid. So
> **every trusted declaration this project has is now in this file's subject**,
> which is what makes the ℝ route above the last foundational item rather than
> one of several.
>
> Two things this does NOT mean, recorded because the number invites them.
> Zero axioms is not zero trust: the kernel that admits these declarations is
> `5,148` function-body lines (derived, gated, `scripts/check-kernel-trusted-core.py`),
> and an adversarial differential against official Lean found a real soundness
> defect in it the first time it ran — a lambda binder domain checked only for
> `def_eq` rather than for being a type, so an ill-typed domain that
> beta-reduced away was never checked (`8428331c8`). And the definitions must
> still say what they claim: `Nat`/`Int` are now pinned by characterization
> theorems (Peano categoricity for ℕ; discreteness, generation and no-junk for
> ℤ), but the SMT-LIB → rendered-statement transcription is still unchecked and
> is the weakest link in the chain
> ([13-residual-trust-surface.md](../prover-track/research/13-residual-trust-surface.md)).


> **STATUS 2026-08-17 — the ℝ half has a route, and it is free.**
> [ADR-0468](../research/09-decisions/adr-0468-real-is-constructed-as-a-setoid-over-the-rationals.md)
> decides **a Bishop setoid of regular ℚ-sequences**: a one-constructor carrier
> with no quotient, and equality carried by a *defined* `CReal.Equiv` rather
> than by `Eq`. ADR-0456's two rejections below are both correct — a Cauchy
> quotient needs the `Quot.sound` this kernel does not have, Dedekind cuts need
> `propext` + `funext` — but the conclusion "therefore ℝ is deferred" does not
> follow, because **equality does not have to be `Eq`**. That third option was
> missing from the accounting.
>
> Measured, not argued: `creal_shape_probe` admits the carrier, its recursor,
> the representative projection (large elimination) and the setoid relation over
> the *constructed* `Rat` with a **trusted surface of 0**, against a `funext`
> negative control in a second kernel that comes back non-empty — so the zero
> discriminates. The price is counted too: **9 of the 30 `Real` declarations
> mention `Eq`**, so 13 of the 22 laws are discharged verbatim and 9 only in
> `Equiv` form. The order fragment a Farkas refutation actually invokes is
> untouched.
>
> One claim below is now superseded rather than merely dated: "a Cauchy-sequence
> ℝ is *inexpressible*" is true of a Cauchy ℝ **with `Eq`**, and false of one
> with a defined equivalence. And the ℚ trigger fired early — `rat_prelude.rs`
> landed ℚ as an ordered field on 2026-08-17, so R1 is unblocked.

> **STATUS 2026-08-16 — the integer half is DONE. `int_prelude` has 0 axioms.**
> `Int.euclidean_decomposition` — the last assumption, and the only member that
> was not a ring or order law — is now a theorem with an empty axiom footprint.
> `nat_axiom_inventory --require-axiom-free integer` exits 0; the inventory reads
> **54 derived (54 with an EMPTY axiom footprint), 0 still asserted**.
>
> It did not need `Int.div`/`Int.mod`. The statement is existential, so it is
> discharged by supplying witnesses: `Int.lt_dest` turns `0 < k` into a positive
> `ofNat`, `Int.rec` splits on the dividend, and each branch reads its witnesses
> off `Nat.div_mod_exists`. The negative branch is uniform —
> `q = negSucc a, r = ofNat (K − succ b)` — with the `succ b = K` case collapsing
> to `r = 0` through truncated subtraction rather than a separate case. The
> `ofNat` transfer steps are definitional, so the only propositional content is
> the ℕ equation.
>
> Downstream: the two reconstruction modules in `axeyum-solver` grew (174,524 →
> 206,580 and 83,060 → 124,121 bytes) because the export now carries a proof
> where it carried an assumption. Re-pinned; `check-lean-gate.sh` accepts them
> at 126 real-Lean checks.
>
> **STATUS 2026-08-15 — the integer half is done except for division.** ℤ is
> CONSTRUCTED over the proved ℕ development rather than asserted, and its axiom
> count has gone **34 → 6 → 1**. `int_theorem_inventory` reports **50 derived
> theorems, all 50 with an empty `axiom_footprint`**. Every ring and order law
> is now a theorem: `no_int_between` (discreteness, previously this route's
> central *assumption*), both associativities, distributivity, and both additive
> order laws.
>
> The design decision worth carrying forward: a **normalized-pair** construction
> was chosen over a setoid quotient, because `Quot.sound` is admitted as
> `Declaration::Quotient`, a *trusted* kind the inventory counts. A quotient
> would have put it in every integer footprint forever and made
> `axiom_footprint: []` unreachable for any integer fact. Most ring laws do not
> distinguish the two routes; exactly one forces the quotient (`add_neg`).
>
> The four laws that stalled were **one** obstruction, not four: `Int.subNatNat`
> is a `Nat.rec` on `n − m` and is stuck on variables, so every mixed-sign
> branch of `Int.add` is stuck. A shift lemma, two characterisations and an
> elimination principle unblock all of them
> ([`diary-int-remainder.md`](../mathematics-2026-08/diary-int-remainder.md)).
>
> **The export has now been read by a real Lean binary** —
> `scripts/check-lean-gate.sh` at Lean 4.30.0, `12 suites, 49 tests, 112
> real-Lean checks (floor 105)`. The previous lane flagged that as not done.
>
> One integer axiom remains, `euclidean_decomposition`, and it is a different
> kind of problem: it asserts the *existence* of a quotient and remainder, so it
> needs `Int.div`/`Int.mod` defined and specified rather than another rewriting
> lemma.

> **STATUS 2026-08-15 (later) — the ℝ half was the wrong question, twice, and
> both corrections are measured.** The `Real` prelude's 30 declarations are not
> an axiomatization of ℝ: there is **no inverse, no division, no completeness,
> no Archimedean and no density axiom** — not even totality — so the package is
> an **ordered commutative ring with 1**, every law of which is true of ℤ. And
> this kernel's quotient package is four declarations with **no `Quot.sound`**,
> so a Cauchy-sequence ℝ is not expensive here, it is *inexpressible*; the
> "a quotient would put `Quot.sound` in every footprint" reasoning recorded above
> and in three source comments describes Lean's package, not ours.
>
> So ℝ was not constructed and its 30 axioms are untouched. What landed is the
> **model**: `build_int_model_of_arith` admits, for each of the 22 `Real` laws, a
> kernel-checked theorem whose type is that axiom's type with the eight
> carrier/operation constants substituted — computed from the environment, never
> typed — proved by the corresponding `Int` theorem. **22/22 witnesses have an
> empty `axiom_footprint`, and 22/22 are syntactically the `Int` law.**
> `Int.sq_nonneg` (the one law with no ℤ counterpart) is proved; `Int` goes
> **50 → 51 derived, all 51 axiom-free**.
>
> That is *relative consistency*, not a discharge — it eliminates the
> possibility that the 30 axioms are contradictory (which would make every LRA
> and SOS certificate vacuous with no gate noticing), and it does not make a
> `Real` theorem out of an `Int` one. **ℚ is the right next carrier and is
> quotient-free constructible, but nothing in the package needs it yet**; the
> trigger is a proposed `inv`/`div`/supremum/Archimedean axiom, and a test fires
> on that day. The route that actually *eliminates* the 30 is parameterising the
> solver's reconstruction over the ordered-ring interface, not constructing a
> carrier. See
> [ADR-0456](../research/09-decisions/adr-0456-real-is-an-ordered-ring-modelled-by-int.md)
> and [`diary-real-keystone.md`](../mathematics-2026-08/diary-real-keystone.md).

**The finding.** Five agents working in five different crates on five different
tasks each hit the same wall on 2026-08-14, and each reported it as a local gap.
It is not five gaps. Integers and reals are absent, assumed, or unprovable at
every layer of the stack simultaneously.

## The measurement

| layer | crate | state |
|---|---|---|
| evidence | `axeyum-scenarios` | `lib.rs:559-563` — `unreachable!("scenarios do not declare integer symbols for enumeration")`, and the same for `Sort::Real`. **No negative control about ℤ or ℝ is expressible.** |
| library | `axeyum-lean-kernel` | `nat_prelude` **119 proved / 0 trusted**; `int_prelude` **50 proved / 1 axiom** (was 20 / 6 when this was written, and 0 / 34 before that); `arith_prelude` **0 proved / 30 axioms** — unmoved |
| solver | `axeyum-solver` | the `∀`-route's `k=3` blocker is *integer* bound strictness: `P≥1, P·s ≥ P+1 ⊢ s ≥ 2` is `unknown`, while `⊢ s > 1` and `s > 1 ⊢ s ≥ 2` are **0 ms each** |
| CAS bridge | `axeyum-cas` | the ideal-membership certificate is a statement about **ℝ**; the mathematics it was built for is true over **ℤ** for reasons involving integrality |
| curriculum | `docs/curriculum` | `integers` and `rationals` are both `decidability = "computable", status = "covered"`; `reals` is `"bounded", "covered"` — while the library assumes them and the evidence layer cannot enumerate them |

That last row is the day's characteristic defect reaching the core of the
mathematics: `covered` is a **stored status, not a re-derived one**, asserted
over the number systems the entire ladder rests on. The corpus audit found
`reals` is the one `covered` node whose claim our fragment cannot support, and
`divisibility-and-euclid` claimed `computable`/`covered` with **zero**
negative-control evidence until it was closed by hand.

## Why this is the keystone rather than one item among five

The north star is a ladder: finite domain → arithmetic → theory combination →
quantifiers → proof production. The bottom rung (SAT/QF_BV) is strong: DRAT
certificates, an independent backward checker, covers with mechanically
discharged obligations. The top rung is real: Lean's own kernel accepts an
axeyum development from an empty environment.

**The rung between them is missing.** Arithmetic over ℤ and ℝ is where every
serious mathematical statement lives, and it is exactly where the stack has
assumptions instead of proofs and `unreachable!()` instead of evidence.

This also explains a pattern that looked like coincidence. The campaign produced
**18 new off-diagonal Schur values and 2 new Rado numbers** — all finite,
bounded, colouring problems over `BitVec`-shaped domains — and **zero theorems**.
That is not a coincidence of target selection. It is the shape of what the stack
can currently carry evidence about.

## The work

Five items, one per layer, deliberately treated as **one coordinated push**
rather than four independent tickets. Fixing them separately reproduces the
disease: four crates each solving their local instance, none composing.

### K1 — Construct `Int` from proved `Nat`, discharge its assumptions

> **Owned by another lane.** `int_prelude.rs` cannot be built without
> `nat_prelude.rs`, which a second session rewrites every few minutes — 49
> touches in 24 hours. That lane is already building toward ℤ (extended
> Euclidean, Bézout certificates, gcd's universal property), so contesting the
> file would slow the keystone rather than advance it. See
> [`00-parallel-work.md`](00-parallel-work.md). **K2–K5 are free and are what
> ℤ will need the moment it lands.**

The precondition landed while this was being written. In 60 commits the Lean
lane took `nat_prelude` from 3,856 to 9,969 lines and from 57 to **106 proved
theorems with zero axioms**, and — decisively — moved past arithmetic into the
machinery ℤ-as-a-quotient needs:

```
add native accessibility foundation   ·  add generic well-founded fixpoint
prove well-founded fixpoint equation  ·  prove Nat strict order well-founded
add executable Nat division state     ·  certify executable Nat division
add checked executable Nat gcd        ·  prove Nat gcd universal property
bridge divisibility through executable remainder
```

**Metric:** assumptions remaining per prelude, per release. A number a referee
can check and a competitor cannot fake. Measured 2026-08-15 by
`nat_axiom_inventory`: `logic` 0, `nat` 0, `int` **1**, `arith` **30**,
`string` 1. (The `int 3, arith 3, string 1` this line used to carry was a
different quantity read off a different tool, and was wrong for both.)

### K2 — An UNSAT evidence route for `Int`/`Real` in `axeyum-scenarios`

`check_unsat` proves UNSAT **by enumeration over the sort's bit width**, which is
why `Sort::Int` and `Sort::Real` are `unreachable!()`. Enumeration cannot be the
answer for unbounded sorts, so this needs a second evidence kind — bounded-domain
instantiation, or a symbolic identity discharged by the existing routes.

Until it exists, **half the stack cannot produce a self-checking negative
control about the sorts our mathematics lives in.** 15 of the 86 refutable
misconceptions in the corpus audit are naturally QF_LRA and were declined for
exactly this reason.

### K3 — Integer bound strictness normalisation in the solver

`x ≥ k ↔ x > k−1` over `Sort::Int`, retried on `unknown`. Measured as the
difference between `unknown` at 20 s and **0 ms** on both bounding steps of the
`k=3` critical leaf.

Note the mechanism, because it changes what kind of fix this is:
`nra.rs:107` `const MAX_CROSS_PRODUCTS: usize = 2`, enforced at `:334`. The
query declines in **40 ms at 1 s, 10 s, 60 s and 300 s alike** and stays
`unknown` through the 1800 s rung. **Budget is irrelevant by construction** —
this is a deterministic admission cap, not a search that ran out of time.

### K4 — Integrality certificates in the CAS

A modulus plus finite enumeration in ℤ/mℤ is as re-checkable as a polynomial
identity, and it is the ℤ half of the bridge that was built for ℝ. Named
instances already in the register and provably outside the current route:
`x·y = 1 ∧ x + y = 3`, and `x² + y² = 3`.

### K5 — Re-derive the curriculum's `covered` flags from evidence

`integers`, `rationals` and `reals` should each name the `axeyum-scenarios`
family that exercises them, or lose the label. The curriculum is the routing
table for the whole vision; a routing table whose entries are asserted rather
than checked routes work to places that cannot receive it.

## How we will know it worked

Not by a benchmark. By this: **a statement with symbolic integer parameters,
discharged with a re-checkable certificate.** The campaign's `∀`-route already
proved the `k=2` Rado case for symbolic `a` **and** `b` over unbounded ℤ — a
theorem about an infinite family. `k=3` stalled, and the stall is now known to
be K3 plus a product-abstraction pass, not a missing nonlinear engine.

One such theorem is worth more than the nineteenth table entry, and it is the
thing this stack is uniquely shaped to produce.
