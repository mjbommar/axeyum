# The `add_declaration` typecheck cliff on `declare_medians_concurrent`

Status: **diagnosed, not fixed**. Trusted-kernel change deferred pending an
adversarial def-eq fixture (see "Why no fix here" below).

## Summary

`declare_medians_concurrent` (`crates/axeyum-lean-kernel/src/creal_point.rs`,
on the sibling worktree `agent-ac848b6ea4152d280`, uncommitted) builds a proof
term in ~18 ms and then `Kernel::add_declaration` does not finish typechecking
it within 430+ seconds (three orders of magnitude slower, and climbing, not
plateauing). This is not a size problem: a synthetic control with the *same*
bookkeeping shape (a 15-leaf `right_chain` reordered via
`reorder_chain_proof`, using *more* swaps than the real proof) checks in
30 ms. The actual cause is that `declare_medians_concurrent`'s use of real
`CReal`-valued leaves (built from point coordinates via `mul`/`neg`/`cross`,
and combined via `midpoint_self`/order-adjacent lemmas) causes the
typechecker to repeatedly open motive binders for `Eq.rec`/`Int.rec`
recursor applications reached by δ-unfolding `Rat`/`Int` arithmetic — and
`LocalContext::push`/`pop` unconditionally wipe **all** of the context's
memo tables on every such open, regardless of how deep in an unrelated
computation it happens. Measured over one run before it was killed (still
running, still climbing): **10.06 million** cache-wiping binder-opens,
**1.229 billion** `infer_core` calls, and an overall infer-cache hit rate of
only ~59% for a proof term whose own construction touches a few thousand
nodes at most.

## Reproduction

Branch under investigation: `agent-ac848b6ea4152d280` worktree,
`crates/axeyum-lean-kernel/src/creal_point.rs` (uncommitted, ~2957 lines,
purely additive over this worktree's committed 1498-line version — it adds
`CPoint.collinear`/`CPoint.medians_concurrent` and everything
`declare_medians_concurrent` needs). Per-step `eprintln!` timing already
present in that file confirms:

```
median_hyp_expand A/B/C          ~0.65-4.0 ms each
concat_proof(a,b) / (ab,c)       ~20-280 µs
reorder_chain_proof              ~0.7-4.5 ms   (the 43-swap sort)
group1..6 + peel1..5             ~25-370 µs each
final assembly                   ~18-95 µs
------------------------------------------------
all term construction            ~18 ms  (debug), lower in release
add_declaration(medians_concurrent)   >180 s (debug), >430 s (release), never printed
```

Confirmed independently in this worktree (which does **not** have
`medians_concurrent` committed): copied the file in, built and ran
`cpoint_prelude_builds` in both debug and `--release`. Debug: still running
past 180 s (twice). Release: still running and still climbing past 430 s
wall clock (killed, not a plateau — see counters below). All diagnostic
edits made for this investigation were reverted before finishing; `git
status`/`git diff` in this worktree are clean.

## Scaling curve: the reorder/chain bookkeeping is NOT the cause

To isolate whether `reorder_chain_proof`'s 43-swap selection sort over the
15 leaves is inherently superlinear, a synthetic control was built directly
in `creal_point.rs` (`mod cliff_repro`, removed after measurement): the same
`right_chain` + `reorder_chain_proof` shape, but over `n` **opaque atomic
fvar leaves** (no `CReal` arithmetic underneath — no `mul`/`neg`/`cross`,
no `midpoint_self`, no order/`PosBound` lemmas), reordered by a **full
reversal** (`n(n-1)/2` swaps — 105 at `n=15`, more than the real proof's 43).
Built a minimal `CPointPrelude` wrapper around a freshly-built
`CRealPrelude` for this (avoiding `build_cpoint_prelude`, whose own last
step *is* `declare_medians_concurrent` — calling it would just re-trigger
the cliff before the synthetic measurement ever ran).

| n (leaves) | swaps (full reversal) | build      | check      | check/build |
|-----------:|-----------------------:|-----------:|-----------:|------------:|
| 3          | 3                       | 2.51 ms    | 0.56 ms    | 0.2         |
| 5          | 10                      | 5.29 ms    | 1.56 ms    | 0.3         |
| 7          | 21                      | 6.54 ms    | 4.86 ms    | 0.7         |
| 9          | 36                      | 9.13 ms    | 7.15 ms    | 0.8         |
| 11         | 55                      | 12.34 ms   | 12.34 ms   | 1.0         |
| 13         | 78                      | 19.54 ms   | 21.32 ms   | 1.1         |
| 15         | 105                     | 25.55 ms   | 30.03 ms   | 1.2         |

Linear, bounded, no cliff — with *more* swaps than the real 43. This rules
out the splice/reorder/peel bookkeeping pattern itself as the culprit. The
difference must be in what `declare_medians_concurrent`'s leaves *are*
(genuine `CReal` expressions built from point coordinates, combined via
`midpoint_self`/order-adjacent lemmas), not the shape of the proof that
combines them.

## Instrumentation and findings

Added (then reverted) atomic call counters in
`crates/axeyum-lean-kernel/src/tc.rs` for: `infer_core`, `whnf`, `whnf_core`,
`whnf_no_unfolding`, `def_eq_core` (+ cache-hit / `def_eq_quick`-true
counts), `lazy_delta_step`, `delta`, and `LocalContext::push`/`pop`
(tc.rs:569 / tc.rs:586). Also attributed every `push` to its call site —
the four places `ctx.push(LocalDecl { .. })` occurs in the whole file:
`def_eq_binder` (tc.rs:1452, Pi/Pi or Lam/Lam congruence),
`check_core`'s Lam-vs-Pi fast path (tc.rs:2793), `infer_lambda` (tc.rs:3124),
`infer_pi` (tc.rs:3161).

Running the real `declare_medians_concurrent` (via `cpoint_prelude_builds`,
release build) with these counters live, before being killed at ~430 s wall
clock (**still climbing, not plateauing**):

```
infer_core        ≈ 1,229,000,001 calls   (open_hit ≈ 191.05M, closed_hit ≈ 531.38M → ~58.8% hit rate)
def_eq_core       ≈   775,527,241 calls   (cache_hit ≈ 1.24M, def_eq_quick-true ≈ 765.30M)
whnf_core         ≈   804,582,479 calls
whnf_no_unfolding ≈    72,614,877 calls
lazy_delta_step   ≈     4,348,040 calls
delta (real δ-unfold) ≈ 3,630,499 calls
LocalContext push ≈    10,062,206   pop ≈ 10,062,038   (balanced — no leak)

push attribution:  check_core (Lam-vs-Pi) = 10,031,236  (99.7%)
                   infer_pi               =     25,724
                   def_eq_binder          =      3,417
                   infer_lambda           =      1,627   <- STABLE; the proof's
                                                             own 6 outer lambdas
                                                             are NOT the source
```

`infer_lambda`'s count stops growing early and stays flat for the rest of
the run — direct evidence that the outer `∀ A B C P, collinear .. -> collinear
.. -> collinear ..` telescope (6 nested `Lam`/`Pi`, opened once each) is not
where the time goes. **99.7% of all binder-opens come from one call site:**
`check_core`'s bidirectional Lam-vs-Pi fast path
(`crates/axeyum-lean-kernel/src/tc.rs:2793`), invoked from `infer_app`
whenever an *argument* being checked is syntactically a `Lam` against a
`Pi`-shaped expected domain.

Sampling the actual `(argument, domain)` pairs hitting that branch — gated
to only sample once `infer_core` had already passed 100 million calls (well
past every other, fast, `declare_*` step, so unambiguously *inside*
`declare_medians_concurrent`'s own check) — shows they are recursor
**motive/case arguments**, not anything geometry-specific:

```
head=Eq.rec   arg=(fun _:Nat => (fun _:(P (BVar 0)) => ...))   domain=(Pi _:Nat, (Pi _:(P (BVar 0)), Sort))
head=Int.rec  arg=(fun _:Int => Rat)                            domain=(Pi _:Int, Sort)
head=Int.rec  arg=(fun _:Nat => (...))                          domain=(Pi _:Nat, ((fun _:Int => Rat) (Int.ofNat (BVar 0))))
```

i.e. `Nat`-indexed equality transport (`Eq.rec`) and `Int`→`Rat` case-split
coercion (`Int.rec`) — standard-library machinery reached by δ-unfolding the
`Rat`/`Int` arithmetic that `CReal.add`/`mul`/`Equiv`, `PosBound`, and the
order/GCD reasoning transitively behind `inv2`/`midpoint_self` route
through. (An earlier, ungated sample of the *first* 10 occurrences in the
whole run showed `And.rec`/`Or.rec`/`False.rec` motives instead — that
first burst is from building `CRealPrelude`/`RatPrelude`/`IntPrelude`
themselves at the very start of `build_cpoint_prelude`, which is fast and
bounded; it is a separate, much smaller population from the one sustaining
the cliff.)

## Mechanism

`LocalContext::push`/`pop` (`tc.rs:569`/`tc.rs:586`) each unconditionally
call `.clear()` on **all four** of the context's memo tables —
`infer_cache`, `def_eq_cache`, `whnf_cache.1`, `whnf_core_cache.1` — every
single time either is invoked, with no notion of scope narrower than "the
entire declaration stack." This is deliberate and, on its own, correct: an
open expression's cached type/whnf/def-eq result is only valid under the
exact local declaration stack it was computed against, and the doc
comments on `LocalContext` are explicit about this (`tc.rs:520-537`).

The problem is where this fires. `check_core`'s Lam-vs-Pi fast path opens
one binder **per level of every `Lam`-typed argument it checks**
(`tc.rs:2793`), and it is invoked from `infer_app` for *every* application
node in the term being typechecked — including ones arbitrarily deep inside
`declare_medians_concurrent`'s recursive descent, with no relationship to
that theorem's own outer lambdas. Every time this fast path fires on an
`Eq.rec`/`Int.rec` motive reached while checking one of the theorem's 15
leaves (or one of the 43 swap-steps, or one of the 6 cancellation groups),
it **discards every memoized `infer_core`/`def_eq_core`/`whnf_core` result
the surrounding, much larger computation had already built**, forcing that
surrounding computation to re-derive it once control returns. Because
re-deriving it requires touching the *same* `Rat`/`Int` arithmetic (the
same underlying rational bounds recur across the 15 structurally-distinct
leaves), the wipes compound: each of the 10.06 million wipes is followed by
comparable-sized re-derivation, consistent with the observed
1.229 billion ÷ 10.06 million ≈ **122 "extra" `infer_core` calls redone per
wipe** — a plausible size for the `Rat`/`Int` sub-computation reachable from
one leaf's order/`PosBound`-adjacent context.

This is the closed/open cache split's documented failure mode, one layer
up from where it was last fixed: the split (tc.rs:520-537, "33.0 s without
this memo, 13.0 s with it") already protects *closed* subterms from
per-context wipes by routing them to a kernel-global cache. But the leaves
in `declare_medians_concurrent`'s proof are **open** (built from the
theorem's own universally-quantified point/hypothesis fvars), so every
comparison involving them routes through the *context-scoped* cache — the
one `push`/`pop` still wipes unconditionally, on every nested binder-open
anywhere in the descent, not just at the theorem's own boundary.

### Why smaller theorems in the same file don't show this

Every other theorem in `creal_point.rs` (`declare_varignon`,
`declare_add_right_cancel`, `declare_midpoint_vector_swap`, …) also touches
this same `And`/`Or`/`Eq`/`Int`-rec machinery — the very first ~500K
`infer_core` calls of the *whole* prelude build already show ~13K
Lam-vs-Pi events, well before `declare_medians_concurrent` starts, and
attributable to `CRealPrelude`/`RatPrelude`/`IntPrelude`'s own internal
order/case-split lemmas. But those theorems' own build-and-check times
(0.3–7.3 ms, measured both in debug and release) show the wipe-and-redo
cost stays a small constant there: their proofs are small (a handful of
lemma applications, no 15-way leaf splice). `declare_medians_concurrent` is
the first proof in this codebase whose *size* (15 structurally-distinct
`CReal` leaves, each combined via `midpoint_self`/order-adjacent lemmas,
spliced through a 43-swap reorder and 6 cancellation groups) is large
enough that the same per-wipe redo cost, compounding once per Eq.rec/Int.rec
comparison, crosses from "a few extra ms" to "still running past 430 s."

## What was changed

**Nothing remains changed.** For this investigation:
- Copied `creal_point.rs` from the sibling worktree
  `agent-ac848b6ea4152d280` (uncommitted there; not edited there) into this
  worktree to get a runnable `declare_medians_concurrent`.
- Added a synthetic `mod cliff_repro` scaling-curve test to `creal_point.rs`.
- Added atomic diagnostic counters and a shallow structural sampler to
  `crates/axeyum-lean-kernel/src/tc.rs` (`cliff_diag` module, counter bumps
  at the call sites listed above, a `shallow_dump` helper, and a
  `LAM_SAMPLE_COUNT`-gated `eprintln!` in `infer_app`).

All of the above were reverted (`git checkout --
crates/axeyum-lean-kernel/src/creal_point.rs
crates/axeyum-lean-kernel/src/tc.rs`) before finishing this session; `git
status`/`git diff` in this worktree are clean. No adversarial def-eq
fixture is included because no cache-keying change was made.

## Why no fix here

A fix has an obvious shape — narrow what a `push`/`pop` invalidates so an
unrelated, deeply-nested binder-open (like a recursor motive check reached
mid-δ-unfold) doesn't discard the memoization of an ancestor computation it
has no relationship to — but this is exactly the class of change this
kernel's own history warns is easy to get wrong in a way that is not a
slowdown but a **soundness hole**: CLAUDE.md records a prior δ-chain memo
that "routes each link into the split cache by *that* link's own key" and a
`whnf_core` tripwire once "gated on the *entry*, and the links it guards are
not the entry." A memo keyed on anything less than everything the
comparison actually depends on (in particular: the local declaration stack
in scope, not just the `ExprId` pair) can make the kernel accept two terms
that are not actually def-eq under the context that matters.

Any real fix here needs, at minimum: a precise statement of what the
narrower cache key is and a proof it is still sound under `push`/`pop`
interleaving, plus an adversarial fixture — two terms that must **not** be
def-eq, constructed so that a too-coarse "keep entries that don't mention
the popped fvar" (or similar) rule would wrongly keep a stale entry across
the pop and accept them anyway. Constructing that fixture and the fix
together is follow-up work, not attempted in this session.

## Follow-up

- Build the adversarial def-eq fixture above and a scoped-invalidation
  design (e.g. a checkpoint/rollback discipline on the four memo tables
  keyed to the exact declaration-stack depth, rather than a global
  `.clear()`), then re-run this same `declare_medians_concurrent` repro to
  confirm the fix actually removes the cliff before landing it.
- Re-run this measurement once `declare_medians_concurrent` is committed
  to get an exact wall-clock/exit number (this session never observed
  completion) and confirm the full kernel suite
  (`cargo test -p axeyum-lean-kernel --lib`) stays green with the fix in
  place.
