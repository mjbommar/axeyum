# 01 — ℤ and ℝ are one hole through every layer

> **STATUS 2026-08-15 — the integer half is largely done.** ℤ is now CONSTRUCTED
> over the proved ℕ development rather than asserted: 34 axioms became 6, and 20
> `Int.*` theorems each carry an empty `axiom_footprint`. `Int.no_int_between`
> — discreteness, previously this route's central *assumption* — is derived and
> rests on nothing.
>
> The design decision worth carrying forward: a **normalized-pair** construction
> was chosen over a setoid quotient, because `Quot.sound` is admitted as
> `Declaration::Quotient`, a *trusted* kind the inventory counts. A quotient
> would have put it in every integer footprint forever and made
> `axiom_footprint: []` unreachable for any integer fact. Most ring laws do not
> distinguish the two routes; exactly one forces the quotient (`add_neg`).
>
> Six axioms remain, and four are blocked on one missing piece — `subNatNat`'s
> borrow lemma. ℝ is untouched at 30 axioms and is now the whole of this item.
> Details: [`../mathematics-2026-08/diary-int-keystone.md`](../mathematics-2026-08/diary-int-keystone.md).

**The finding.** Five agents working in five different crates on five different
tasks each hit the same wall on 2026-08-14, and each reported it as a local gap.
It is not five gaps. Integers and reals are absent, assumed, or unprovable at
every layer of the stack simultaneously.

## The measurement

| layer | crate | state |
|---|---|---|
| evidence | `axeyum-scenarios` | `lib.rs:559-563` — `unreachable!("scenarios do not declare integer symbols for enumeration")`, and the same for `Sort::Real`. **No negative control about ℤ or ℝ is expressible.** |
| library | `axeyum-lean-kernel` | `nat_prelude` **119 proved / 0 trusted**; `int_prelude` **20 proved / 6 axioms**; `arith_prelude` **0 proved / 30 axioms** |
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
can check and a competitor cannot fake. Today: `int` 3, `arith` 3, `string` 1.

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
