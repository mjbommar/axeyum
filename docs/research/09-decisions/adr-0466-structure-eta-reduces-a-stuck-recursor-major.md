# ADR-0466: structure eta must reduce a **stuck recursor major premise**, not only appear at def-eq

Index-summary: a recursor on a structure *variable* was permanently stuck because this port lacked Lean's `to_cnstr_when_structure`; adding it clears the top declined root in both scale censuses, and it also settles that the rule the previous lane named — `try_unfold_proj_app` — is structurally inert here
Status: accepted
Date: 2026-08-15

## Context

The previous lane ([ADR-0462](adr-0462-local-let-zeta-belongs-inside-whnf-core.md))
moved ζ into `whnf_core` and handed over **`Nat.Linear.Poly.denote_reverse`** as
the new top declined root in both scale censuses (153 of 500 sampled
`Init`+`Std` streams, and the top Mathlib root too). It had probed the pair —

```text
depth=1  lhs_head = Prod.rec.{1,0,0}                                            (6 args)
         rhs_head = (Nat.brecOn.go.{1} motive (Nat.Linear.Var.denote v …) Nat.mul._f).1  (1 arg)
         STOP: ARITY differs
```

— and named a candidate rule this port lacks: `lazy_delta_reduction_step`'s
`try_unfold_proj_app` branch (`src/kernel/type_checker.cpp:868`, pinned
`references/lean4` at `d024af0`), which unfolds a *projection application* on
one side instead of δ-unfolding an expensive well-founded-recursion term on the
other.

**That was the wrong rule, and it is measurably inert here.** Two findings, in
order.

### 1. The blocker is `to_cnstr_when_structure`

Reproducing the pair on the retained root stream shows that the left side is
`Nat.Linear.Poly.denote v [p]` reduced as far as this kernel can take it: a
`Prod.rec` whose **major premise is the bare free variable `p : Nat × Var`**.
`Nat.Linear.Poly.denote` is `List.rec` over `List (Nat × Var)` and its minor
destructures the head element, so checking the lemma requires ι on a `Prod.rec`
against a variable. This port's `reduce_rec` had, in exactly the position Lean
puts it, `to_cnstr_when_K` and the Nat/String literal hooks — and **not**
`to_cnstr_when_structure`:

```cpp
/* If `e` is not a constructor application and its type `C ...` is a
   non-recursive structure, return `C.mk e.1 ... e.n`. */
template<typename WHNF, typename INFER>
inline expr to_cnstr_when_structure(environment const & env, name const & induct_name,
                                    expr const & e, WHNF const & whnf, INFER const & infer_type) {
    if (!is_non_rec_structure(env, induct_name) || is_constructor_app(env, e))
        return e;
    expr e_type = whnf(infer_type(e));
    if (!is_constant(get_app_fn(e_type), induct_name))
        return e;
    if (whnf(infer_type(e_type)) == mk_Prop())
        return e;
    return expand_eta_struct(env, e_type, e);
}
```
(`src/kernel/inductive.h:63`, called from `inductive_reduce_rec` at line 96,
between the K hook and the literal hooks.)

So the rule was already *in* this kernel — as
[`Kernel::try_eta_structure`](../../../crates/axeyum-lean-kernel/src/tc.rs), the
def-eq eta rule, guarded by the same `is_non_rec_structure` predicate — but
**only where def-eq could use it**, never where reduction could. Measured on the
commit before this change: `def_eq(s, Solo.mk)` for an opaque `s : Solo` already
returned `true`, while `Solo.rec … s` refused to reduce. The gap was between two
copies of one rule, not a missing rule.

### 2. `try_unfold_proj_app` cannot fire in this port at all

Lean's branch is defined as *"`whnf_core(e)` changes `e`"*, and it is worth
having because Lean's delta loop reduces with `cheap_proj = true` — a projection
whose structure is reduced **without** δ — so a projection application really can
still be reducible when it reaches `lazy_delta_reduction_step`, and
`try_unfold_proj_app` deliberately re-reduces it with `cheap_proj = false`.

This port has no `cheap_proj` mode: `reduce_projection` always reduces the
projected structure with full δ. Every side entering `lazy_delta_step` has
therefore already been through `whnf_no_unfolding` and is a fixed point of it, so
`try_unfold_proj_app` is a function that can only return `None`.

Measured rather than argued. An instrumented build that adds the branch exactly
as Lean writes it, counting entries and hits, over four retained root streams and
four `Init`+`Std` corpus streams:

| stream | branch reached | branch fired |
|---|---:|---:|
| `Nat.Linear.Poly.denote_reverse` | 69 | **0** |
| `Nat.bitwise._unary` | 74 | **0** |
| `Fin.shiftRight_val` | 121 | **0** |
| `List.attach_cons` | 13 | **0** |
| `initstd-500-streams/{1,7,42,123}` | 135 / 5,778 / 36 / 74 | **0 / 0 / 0 / 0** |

6,300 opportunities, zero effect. Porting `try_unfold_proj_app` on its own would
have been a rule that exists and never fires — the failure mode `import-strings`
found in the string def-eq hook ([ADR-0461](adr-0461-lean-string-literal-def-eq-hook-is-unreachable.md)).
It is a *performance* branch, and it is contingent on a `cheap_proj` mode this
port does not have; both belong to a separate decision.

## Decision

**Port `to_cnstr_when_structure` into `Kernel::reduce_rec`, in the position Lean
calls it from: after the K hook and the literal hooks, before rule selection.**

```rust
let major = self.k_like_major(&rec_rules, major, ctx).unwrap_or(major);
let major = self
    .structure_eta_major(&rec_rules, major, ctx)
    .unwrap_or(major);
```

`structure_eta_major` replaces a major that is not a constructor application by
`mk params… e.0 … e.n-1`, taking the parameters off the major's inferred type and
the universe levels off that type's head — Lean's `expand_eta_struct` verbatim.
This is a **port**, not a new rule: the guard is Lean's `is_non_rec_structure`
plus its `Prop` exclusion, clause for clause.

Three properties this rests on, each checked rather than argued:

* **It is a widening, and it adds no identification the kernel did not already
  make.** The replacement is an instance of the same structure-eta rule
  `try_eta_structure` already applies at def-eq, under the same predicate. The
  measurement above — `def_eq(s, Solo.mk)` true before the change while
  `Solo.rec … s` was stuck — is what makes this a statement about *position*
  rather than about *strength*.
* **The guard's four clauses each carry content, and each is pinned by a control
  that flips when that clause alone is removed.** See the table under
  Consequences.
* **The WHNF cache stays sound.** Like `k_like_major`, this rule needs the
  major's *type*, so it is a second door from reduction into inference and a
  second reader of the local context. `reduction_ctx_reads` is bumped before that
  read and only for an **open** major, matching `k_like_major` and the ζ arm: a
  closed major is typed from the environment alone, so a closed expression cannot
  make the kernel-global, context-free WHNF cache key wrong. The existing
  assertion in `whnf_no_unfolding` is what enforces it, and it did not fire
  across the paired 500-stream census.

## Consequences

* **`Nat.Linear.Poly.denote_reverse` imports clean** — 105 of 105 declaration
  records, zero declines, from the same retained stream that refused it. So do
  `Fin.shiftRight_val` (446 records) and `List.attach_cons` (75 records), the
  other two retained roots that were still declining.
* A paired A/B census — both binaries run **concurrently on the same retained
  500-stream `Init`+`Std` corpus**, same bounds (4 jobs, 120 s, 8 GB), compared
  per stream — was to be recorded in a lane diary, `diary-import-projrec.md`.
  **That file was never committed** — the lane was cut off before it landed, and
  it exists on no ref. The headline below is therefore this ADR's own record of
  the census and has no companion file to check it against; treat it as a result
  reported here rather than one with retained evidence, and re-run the census if
  it needs to be load-bearing.
  Headline: CLEAN 331 → 405 of 500, DECLINED 165 → 91, **74 streams recovered and
  none lost**; total declines 34,993 → 15,143; distinct decline roots 51 → 33.
* **Five removal controls**, each flipping exactly one test in
  `structure_eta_recursor_major.rs`:

  | removed | tests that fail |
  |---|---|
  | the `structure_eta_major` call in `reduce_rec` | 2 — both positives (closed major, open major) |
  | the one-constructor clause | 1 — `a_two_constructor_family_is_not_eta_expanded` |
  | the non-recursive clause | 1 — `a_recursive_structure_is_not_eta_expanded` |
  | the zero-indices clause | 1 — `an_indexed_family_is_not_eta_expanded` |
  | the `Prop` exclusion | 1 — `a_prop_structure_is_not_eta_expanded` |

  Each exclusion family is built so that dropping its clause makes the recursor
  reduce to a *named constant*, so the control fails on an accepted equation
  rather than on a coincidence.
* **One existing assertion flips, and it was over-strong.**
  `k_like_reduction::a_non_prop_family_with_one_nullary_constructor_is_not_k_reducible`
  used `inductive Solo : Type where | mk : Solo` — which is *also* a
  non-recursive structure, so it now reduces by eta rather than by K. Official
  Lean 4.30.0 accepts `Solo.rec (motive := fun _ => Nat) 0 s = 0 := rfl` for an
  opaque `s`, so the assertion disagreed with the kernel it is a port of. The
  test now carries **one index**, which breaks `is_non_rec_structure`
  (`nindices == 0`) and leaves K's `Prop` clause as the only thing that can
  refuse the probe — K itself is happy with indices, which is how `Eq` is K-like.
  Verified by removing K's `Prop` clause: exactly that test fails.
* **Checked by Lean.**
  `real_lean_structure_eta_recursor_crosscheck.rs` (new, registered, floor
  111 → 115) hands official Lean 4.30.0 one positive module and three refusals —
  one per claim, because Lean keeps elaborating past an error and three failures
  in one module would be indistinguishable from one. The positive module reads
  `#print axioms` back and fails on `sorryAx`, so an admitted goal cannot read as
  agreement. Gate measured: 16 suites, 53 tests, **126** real-Lean checks.
* The cost is wall clock, again, and for the same reason as ζ: a stream that used
  to give up at a def-eq failure now keeps reducing. The paired census moved
  three streams into the 120 s RESOURCE bucket and none out.

## Alternatives considered

* **Port `try_unfold_proj_app`, as the handover proposed.** Measured inert: 6,300
  entries and 0 fires across eight real streams, because this port has no
  `cheap_proj` mode for it to compensate for. Landing it would have added a rule
  that cannot fire and a claim that cannot be checked.
* **Port `cheap_proj`/`cheap_rec` first, then `try_unfold_proj_app`.** This is a
  real and separable piece of work — it is Lean's answer to exactly the runaway
  streams this corpus still has — but it is a *cost* change, not a capability
  change, and bundling it here would have made the A/B unattributable. Handed on.
* **Eta-expand structure-typed variables at import time.** Wrong in the same
  direction as zeta-expanding `let`s: it changes the terms we check away from the
  terms Lean checked, and it would expand under every binder rather than where a
  recursor actually needs it.
* **Reach the identification through `def_eq` instead, by having `def_eq_app`
  try structure eta on a stuck recursor's major.** This is the "bolt-on whose
  coverage is a list of call sites" that ADR-0462 rejected for ζ, one layer up:
  the rule would then fire only where def-eq happened to look, and not inside
  reduction, which is where `Nat.Linear.Poly.denote` needs it.
