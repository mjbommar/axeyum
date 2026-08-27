# Retrieval, not proof difficulty, is the measured bottleneck

Status: **open deficiency**, Opus lane dispatched 2026-08-27.

## The observation

Repeatedly this session, a lane declared itself blocked on a lemma that already
existed, proved, in the tree. The count reported by lanes reached **thirteen**
by the end of the day. That number is a lane-reported tally and has **not** been
independently audited — auditing it is part of the dispatched work, not a
conclusion this file asserts.

The most expensive single instance, because it stalled a whole rung of `supOn`:

    CReal.congr_of_uniformly_continuous :
      ∀ (F : CReal → CReal) (a b : CReal),
        UniformlyContinuousOn F a b →
        ∀ x y : CReal, le a x → le x b → le a y → le y b →
          Equiv x y → Equiv (F x) (F y)

A lane needed exactly this, searched `creal/uniform_continuity.rs` — the module
where it *belongs* — found nothing, and reported the obstacle as its stopping
point. The lemma lives in `creal/integral.rs`, because
`riemann_sum_split_exact_of_uc` consumed it first.

**The search was competent and the answer was correct.** Nothing about the query
was wrong. The lemma is simply not filed where its subject matter says it should
be, and a by-name search cannot find a thing whose name you do not know.

## The three hiding places, all measured

1. **General infrastructure filed under its first consumer's module.**
   `CReal.bucketIndex` (with four clamp lemmas) lives in `uniform_continuity.rs`
   because a covering argument needed it first; it is now consumed by three
   other modules. `congr_of_uniformly_continuous` is the same shape.
2. **A reusable step built INLINE inside a larger declaration, never named.**
   `nat_prelude/powsq.rs`'s `declare_pow_half_split` performs a complete `Nat`
   even/odd split purely as scaffolding. **An inline step has no name to find**,
   so no name-based index can ever surface it.
3. **A lemma whose stated hypothesis is WEAKER than everyone assumes.**
   `CReal.sumRange_cauchy_of_dominated` never required `f` nonnegative, so it
   already covers signed series. Two lanes discovered this independently, both
   against briefs asserting the opposite.

## Why the existing tools cannot fix this

`prelude_theorem_inventory` lists **theorems only**, so every `Definition` —
`Nat.add`, `CReal.integral`, `Rat.polyEval` — returns **zero rows**. Worse, a
prefix grep for `Rat.polyEval` returns 16 hits, every one a *lemma about* it and
none the definition. So the careless query confirms presence and the careful
anchored query reports absence, and **both are wrong about the definition**.

And none of these tools answer the question a blocked lane actually has, which
is never *"is this name taken?"* but:

> **Does something of this SHAPE exist — anywhere, under any name?**

## Why this is the right thing to fix now

`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md` names
three gates on marginal cost per theorem: **contracts, retrieval, sharding**.
Retrieval is one of them, and it is the one with a running measurement.

The cost is not the rebuild. It is that each blocked lane first *sizes its task
as new*, and several came close to building a duplicate. A duplicate is worse
than a delay: **it leaves two proofs of one fact that must stay in sync, and the
kernel happily verifies both.** That has already happened once, with six private
helpers copied verbatim rather than reported.

Prose has not fixed it. CLAUDE.md has carried "search for the STEP, not the
NAME" for some time, and every brief this session repeated it, and the thirteenth
instance still happened — to a careful lane, following the instruction.

## What is dispatched

A shape-indexed retrieval tool over `kernel.environment()` — matching on the
structure of a declaration's type (conclusion head symbol, hypothesis shapes)
rather than on its name — covering **every** declaration kind, not just
`Theorem`, so it answers the definition question the theorem inventory
structurally cannot.

Two things it must do that no current tool does:
- **Fail on absence**, so a fact-ledger `checker_command` can depend on it.
- **Pair every negative with a positive control of the SAME declaration kind.**
  A theorem is not a control for a definition; `Nat.add` returning zero rows is
  the fastest way to learn you are asking the wrong tool.

Hiding place 2 (inline, unnamed steps) is likely **out of reach** for any index
over declared names, since there is no declaration to index. Say so explicitly
rather than implying coverage that does not exist.
