# ADR-0462: ζ for a local `let` belongs inside `whnf_core`, not at the def-eq entry points

Index-summary: a let-local exposed during lazy delta was never unfolded; moving ζ into `whnf_no_unfolding` matches Lean's `whnf_fvar` and clears the top declined root in both scale censuses
Status: accepted
Date: 2026-08-15

## Context

Lean's kernel reduces a **let-bound free variable** to its recorded value inside
`whnf_core` itself. Pinned `references/lean4` at `d024af0`:

```cpp
// src/kernel/type_checker.cpp:401  whnf_core
case expr_kind::FVar:
    if (is_let_fvar(m_lctx, e)) break;   // fall through to the work below
    else return e;
...
case expr_kind::FVar:
    return whnf_fvar(e, cheap_rec, cheap_proj);

// src/kernel/type_checker.cpp:346
expr type_checker::whnf_fvar(expr const & e, bool cheap_rec, bool cheap_proj) {
    if (optional<local_decl> decl = m_lctx.find_local_decl(e))
        if (optional<expr> const & v = decl->get_value())
            return whnf_core(*v, cheap_rec, cheap_proj);   /* zeta-reduction */
    return e;
}
```

The *placement* is the content of the rule. `whnf_core` is called from
`lazy_delta_reduction_step` after **every** δ unfolding
(`whnf_core(*unfold_definition(t_n), false, true)`, lines 901–932), and
recursively on the head of every application spine. So a local `let` that only
becomes the head of a term *during* the delta loop is still reduced.

This port had ζ for locals in a separate pass, `whnf_local_value`, consulted at
exactly two places — the top of `def_eq_core_uncached` and the `whnf_in` entry
point — and it only unfolded the head of a spine. Nothing inside
`lazy_delta_step` ever consulted it.

**Measured consequence, on the declaration this was found on.**
`Nat.bitwise._unary` is the top declined root in both scale censuses (236 of 500
sampled `Init`+`Std` streams, 186 of 400 Mathlib ones); its own stream admitted
301 of 302 records and refused only the declaration, with `TypeMismatch`. Lean
writes `Nat.bitwise` with `let n' := n / 2` and `let m' := m / 2`; the generated
well-founded-recursion helper states its decreasing obligation in terms of the
let-locals, and discharges it against `n / 2` directly. The refused pair was

```text
lhs  PSigma.casesOn.{1,1,1} Nat (fun _ => Nat) (fun _ => Nat)
       (PSigma.mk (n / 2) (m / 2)) (fun n m => n)
rhs  PSigma.casesOn.{1,1,1} Nat (fun _ => Nat) (fun _ => Nat)
       (PSigma.mk n'      m'    ) (fun n m => n)      -- n' := n / 2,  m' := m / 2
```

with the **same head, the same arity, and all five arguments pairwise
definitionally equal** — and the pair still refused. `PSigma.casesOn` carries
`ReducibilityHint::Abbrev`, so the `try_eq_const_app` short-circuit (which is
gated on `Regular`/`Regular`, exactly as Lean's is on
`d_t->get_hints().is_regular()`) does not fire; both sides δ-unfold, ι fires on
each, and the loop continues with `n / 2` against the bare let-local `n'`. From
there `get_applied_def` reports `(Some, None)`, so the *left* side is unfolded
forever while the right side is never ζ-reduced. Full weak-head normal forms of
the two sides are the **same interned expression** (`ExprId(62170)` in the run
that found this), and `def_eq` returned `false` on them.

## Decision

**Do ζ for local `let`s inside `whnf_no_unfolding` — this port's `whnf_core` —
and delete the separate `whnf_local_value` pass.**

```rust
ExprNode::FVar(fvar) => match ctx.value_of(fvar) {
    Some(value) => {
        self.reduction_ctx_reads += 1;
        cursor = self.foldl_apps(value, args.iter().copied());
    }
    None => return cursor,
},
```

`whnf_in` becomes `whnf_core` and is removed; the two `whnf_local_value` calls
in `def_eq_core_uncached` are removed. Nothing else moves: the rule is the same
rule, in the position Lean puts it.

Three properties this decision rests on, each checked rather than argued:

* **It is a widening, and a sound one.** ζ identifies a local with the value the
  local context recorded for it. Only `Kernel::infer_let` creates such a local,
  and it does so after checking that value against the local's declared type,
  so the identification is the ζ rule of the theory and adds no new
  identification beyond it. `LocalContext::push_let` goes through `push`, which
  clears the context-scoped `infer`/`def_eq`/`whnf` caches, so no answer
  computed before a `let` entered scope survives into it.
* **The kernel-global WHNF cache stays sound.** That cache has no local-context
  component in its key and is restricted to *closed* expressions; a closed term
  cannot reach the new arm at all, since no reduction step can introduce an
  `FVar` into a closed term. The existing `reduction_ctx_reads` tripwire is
  bumped in the new arm on a **hit**, so if that argument is ever wrong the
  assertion in `whnf_no_unfolding` fires rather than the cache going quietly
  wrong.

  A **miss** is deliberately *not* counted, and the first version of this arm
  got that wrong: it counted every `FVar` head and the tripwire then fired on
  two of the first 250 Mathlib streams. The mechanism is one the tripwire's own
  doc comment does not cover. Reducing a closed expression can call *inference*
  — K-like reduction infers its major (`k_like_major`, the single door from
  reduction into inference) — and that inference opens **its own** binders;
  reducing under them meets ordinary valueless locals. Their lookups return the
  term unchanged, which is exactly what an empty context would return, so they
  are not a dependence on the context and counting them is a false positive.
  A hit is the context changing the reduct, which is precisely what the cache
  key must not hide.
* **It changes which position the rule fires in, not whether it exists.**
  Removing the new arm and re-running the suite fails **exactly two** of the
  four tests in `local_let_zeta_reduction.rs`: the delta-exposed case and the
  chained case. The head-position case and the ordinary-local refusal still
  pass, because the old two-call-site pass covered the first and neither pass
  ever covered a valueless local. That is the measurement the diagnosis is
  built on, not a claim about what the code looks like.

## Consequences

* `Nat.bitwise._unary` imports clean: **302 of 302 declaration records, 367
  declarations, zero declines**, from the same retained stream that refused it.
* A paired A/B census — both binaries run concurrently on the same retained
  streams, same bounds, compared per stream — shows the effect is far wider than
  the one declaration. Mathlib, 76 paired streams: CLEAN 24 → 39, DECLINED
  48 → 31, total declines 51,040 → 15,735, **distinct decline roots 167 → 64**.
  The 129 roots that disappear are the Mathlib instance hierarchy the previous
  lane had named as the long tail — `Pi.preorder`, `Prop.partialOrder`,
  `DistribLattice.ofInfSupLe._proof_4`, `Function.Injective.*`, `Nat.inst*` —
  none of them individually diagnosed. Twenty-six roots are new, because
  declarations that used to be `UnknownConst` cascades behind a refused ancestor
  are now reached and refuse on their own account.
* The previous lane's "same family" claim splits. The
  `Std.DTreeMap.Internal.*.eq_def` roots really were this rule and are gone;
  `Nat.Linear.*` is not, still declines, and is now the **top** root in both
  corpora. Its pair is `Prod.rec` against a projection of a *stuck*
  `Nat.brecOn.go` application — and Lean's `lazy_delta_reduction_step` has a
  `try_unfold_proj_app` branch for exactly that case which this port does not.
* The cost is wall clock: a stream that used to give up at a def-eq failure now
  keeps reducing. Four Mathlib streams moved into the 120 s RESOURCE bucket.
  This is Lean's cost too — Lean performs the same ζ in the same place.
* Definitional equality now accepts strictly more pairs than before. Every
  positive in `local_let_zeta_reduction.rs` is paired with a control in the same
  test that must still be refused, and
  `real_lean_local_let_zeta_crosscheck.rs` hands the same four declarations to
  official Lean 4.30.0 and requires its verdicts to match ours — including
  reading `#print` back to confirm the `letE` survived elaboration, so a
  toolchain that zeta-expands early fails the suite instead of making it
  vacuous. Real-Lean floor 109 → 111.
* `whnf_local_value` and `whnf_in` no longer exist. Removing them changed no
  test outcome (500 passing before and after in a clean snapshot), which is what
  says the new arm subsumes them rather than merely coexisting with them.

## Alternatives considered

* **Call `whnf_local_value` inside `lazy_delta_step` as well.** This would fix
  the measured case, but it keeps ζ as a bolt-on whose coverage is a list of
  call sites — the exact property that made the gap invisible for as long as it
  existed. Lean does not have that list, and neither should this.
* **Zeta-expand `Let` nodes at import time.** Cheap and wrong in the direction
  that matters: it discards the sharing a `let` exists to express, and a Lean
  term with a `let` under a recursive call can blow up exponentially when
  expanded. It would also make our accepted terms differ from the terms Lean
  checked, which is the one property the whole import route is for.
