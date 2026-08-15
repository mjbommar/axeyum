# Diary — lane `whnf-cache-key`, 2026-08-15

Taking over the landmine [`diary-import-brecon.md`](diary-import-brecon.md)
stopped in front of: K-like reduction needs a `LocalContext` inside reduction,
and that makes `Kernel::whnf_cache` — keyed on `(environment revision, ExprId)`
— context-dependent. That lane's instruction was literal: *settle the cache key
before the rule is written.* This is that, and then the rule.

Outcome in one line: **the collision is constructible and now runs as a test,
the key is split on `has_fvars` at no measured cost, `pub fn whnf` did not have
to change, and K-like reduction landed — the 40-stream import census is
40/40 clean, 0 declines, 0 root blockers.**

## 1. Is the unsoundness real? Yes, and it is one test

The brief asked for the construction: two distinct `LocalContext`s with
colliding fvar ids where a context-consulting reduction returns the first
context's answer for the second. It exists, it is small, and it is
`tc_tests::whnf_cache_key_collision_is_constructible`.

`True` is K-like (a `Prop` family, one constructor, that constructor with zero
fields, not mutual), so

```text
True.rec.{1} (fun _ : True => Prop) True h
```

reduces to `True` when reduction can establish that `h : True`, and is stuck
otherwise. It can only learn `h`'s type from a local context. So:

| | context A | context B |
|---|---|---|
| `fvar` id minted by `LocalContext::new` | **0** | **0** |
| its recorded type | `True` | `False` |
| environment revision | *r* | *r* (nothing admitted in between) |
| correct normal form of the **same `ExprId`** | `True` | stuck |

Every precondition is asserted in the test rather than assumed — that
`fresh_fvar` really does hand back `0` in both, that `Kernel::fvar` interns so
one id is one `ExprId`, and that the revision does not move.

Then the payoff. The pre-fix algorithm is kept verbatim as
`Kernel::whnf_core_context_free_cached` (`#[cfg(test)]`, so nothing that ships
can call it), and the test runs it over the same two contexts:

```rust
let stale_b = k.whnf_core_context_free_cached(probe, &mut ctx_b);
assert_eq!(stale_b, minor, "the pre-fix cache returns the FIRST context's normal form in the second");
assert_ne!(stale_b, normal_b, "...which is not the second context's normal form: this is the collision");
```

This is a demonstration, not an argument. It also means the answer to "latent or
live?" is unambiguous: **latent**. Before this commit nothing in reduction
consulted `ctx`, so the old key was sound for the code that existed; the
collision only becomes reachable with a context-consulting rule in the loop, and
the fix landed in the same commit as the rule. No fact and no ADR are owed for a
live defect, because there was not one.

Two further contexts of the same construction are pinned:
`context_scoped_whnf_entries_do_not_leak_between_contexts` interleaves both
contexts while both are live, and
`popping_the_local_that_justified_k_reduction_invalidates_the_entry` shows the
answer expiring with the local that justified it.

## 2. The key: split on `has_fvars`, and the split is *checked*

Four options were on the table. What decided it was that one of them has a
**structural** argument rather than a disciplinary one.

- *Add a context discriminator to the key.* Every fresh context is a new
  discriminator and every `push`/`pop` invalidates, so this is the "no open-term
  cache" option wearing a hat.
- *Taint: memoise only reductions that did not read the context.* Cheapest, and
  it works — but its correctness rests on **every** context read remembering to
  set the flag. A future rule that reads `ctx` and forgets is silently unsound.
- *Prove the dependence cannot be observed.* True only for the closed fragment.
- *Scope the cache to a context's lifetime.* True for the open fragment.

The last two are the same answer cut in two, so that is the shape:

**Closed expressions go in the kernel-global cache.** A closed term cannot reach
a context lookup at all: β, ζ, ι, projection and δ each build only from subterms
of the input and from environment declarations, and both are closed, so no
`FVar` can appear part-way through a reduction that did not start with one. The
key needs no context component because there is nothing to key on.

**Open expressions go in a cache owned by the `LocalContext`**, next to the
`infer_cache` and `def_eq_cache` that were already there and already cleared on
every `push`/`pop`. That clearing is what scopes an entry to the exact
declaration stack that produced it, so an answer that depended on a local's type
cannot outlive the local. No new argument was needed: this is the validity
domain the context's other two caches already use.

And the closed half's argument is a **run-time check, not a comment**.
`Kernel::reduction_ctx_reads` counts context reads performed inside reduction,
and `whnf_no_unfolding` asserts the counter does not move while a closed
expression is normalized:

```rust
assert_eq!(
    self.reduction_ctx_reads, reads_before,
    "reducing a closed expression read the local context; the kernel-global \
     whnf cache key has no context component and would be unsound"
);
```

This is the part that survives me. The day someone adds a second
context-consulting rule, the tripwire fires on the first closed reduction that
touches it instead of the cache going quietly wrong.

## 3. What it cost: nothing measurable

The prelude build is the workload that matters (a kernel rebuild is on the
critical path of six call sites), so `examples/prelude_build_timing.rs` now
measures it. Release build, same binary shape, `nat`/`integer` means over 9
iterations, two runs each — the two heavy preludes; `logic`/`real`/`string` are
~1.5 ms each and move by less than their own noise.

| WHNF cache | `nat` | `integer` |
|---|---|---|
| one global cache, keyed `(revision, ExprId)` — **the old, unsound key** | 22.3 / 22.9 ms | 39.5 / 40.8 ms |
| **split: closed global + open per-context** (shipped) | 22.5 / 22.8 ms | 39.6 / 40.0 ms |
| closed global only, open terms not memoised | 24.2 / 25.0 ms | 42.9 / 44.8 ms |

So the split costs **nothing measurable** — the two top rows are inside each
other's run-to-run spread — and the open half is worth about **8–9%**, which is
what the simplest correct option (just stop caching open terms) would have paid.

A methodological note against my own first number. My initial "baseline" was
25.1 / 44.4 ms, taken from a binary built before the change, and it made the
split look like a *speed-up*. It is not; rebuilding the old behaviour behind a
toggle in the *same* source tree brought the baseline to 22.3–22.9 / 39.5–40.8.
The A/B has to be two builds of one tree, not two trees.

## 4. Threading the context, and the public API

`pub fn whnf(&mut self, e)` **did not change**, so nothing outside the crate had
to. It is now `whnf` in the *empty* local context, delegating to a new
`pub(crate) whnf_core(e, ctx)`. That is a restriction and never a widening:
without a context, K-like reduction cannot fire on an open term, so the public
entry point identifies strictly fewer terms than the internal one. Its ~30
callers inside `inductive.rs` are inductive-admission telescope walks over closed
declaration types, where the empty context loses nothing.

The threading itself was far smaller than the ~55 sites the handover estimated,
because it stops at the boundary where a context is actually needed:
`whnf_no_unfolding`, its uncached body, `reduce_projection`, `reduce_rec`,
`reduce_quotient`, `reduce_nat_succ`, `delta`. `whnf_local_value` took
`&LocalContext` and now takes `&mut` so it can share the same context cache.

## 5. K-like reduction

`Kernel::k_like_major` is Lean's `to_cnstr_when_K`, consulted from `reduce_rec`
after the major has been WHNF'd and before a constructor head is required. The
guard is Lean's, and all three clauses carry weight:

1. the family satisfies `is_k_like_inductive` (the predicate we already computed
   and used only to emit the wire `k` flag);
2. the major's inferred type WHNFs to an application of that family;
3. the constructor applied to the parameters *read off that type* has a type
   definitionally equal to the major's type.

Clause 3 is what keeps an **indexed** K-like family honest. For `h : @Eq α a b`
the candidate is `Eq.refl α a : @Eq α a a`, so the guard demands `a ≡ b` before
`h` may be treated as `Eq.refl`. Drop it and the rule would let an arbitrary
index be treated as the canonical one.

Inference is fail-closed throughout: any `KernelError` means K does not fire.

### The negative suite, and the control I ran

`tests/k_like_reduction.rs` goes through `Kernel::add_declaration`, never
through `whnf` or `def_eq` directly, because the gate is what has to be right.
The probe shape is uniform — for a family `F`,

```text
probe : ∀ (h : F …), @Eq Prop (F.rec (fun _ => Prop) True h) True
probe := fun h => @Eq.refl Prop True
```

which is admitted **iff** K fires for `F`. Seven tests: two positives (`True`,
and the `eq_of_heq` shape `Eq.rec` on a variable proof of a reflexive instance)
and five that must be refused.

Then the control, because a negative test that passes with the rule disabled is
not evidence about the rule. Each clause was removed in turn and the suite
re-run:

| control | effect |
|---|---|
| K-like reduction disabled entirely | both **positives** fail; all negatives still pass |
| clause 3 (`def_eq` of the two types) dropped | `eq_rec_does_not_reduce_on_a_variable_index` **fails** |
| `Prop` clause dropped | `..._excludes_a_non_prop_family` **fails** |
| zero-fields clause dropped | `..._excludes_a_constructor_with_fields` **fails** |
| mutual clause dropped | `..._excludes_mutual_groups` **fails** |
| single-constructor clause dropped | `..._accepts_a_prop_family_with_one_nullary_constructor` **fails** |

Every clause is load-bearing on exactly one test, and the negatives are guards
rather than artifacts of the new code.

**But the first version of that table was wrong, and the way it was wrong is the
point.** Run against the `add_declaration` probes alone, dropping the
zero-fields clause and dropping the mutual clause each changed **nothing** — all
seven tests still passed. Two different reasons, neither of them "the clause is
unnecessary":

- for a constructor *with* fields, clause 3 refuses first (the constructor
  applied to parameters alone has a `Pi` type, not the family's type), so the
  probe cannot see the zero-fields clause at all;
- for a mutual `Prop` group the probe **cannot be built**. A mutual `Prop` group
  is not a subsingleton, so its recursors are *small*-eliminating and carry no
  universe parameter, and the probe needs a `Sort 1`-valued motive. The
  declaration was refused with `UniverseArityMismatch` — a refusal that has
  nothing to do with K. That test was passing while measuring nothing.

An earlier version of the mutual test was worse still: it under-applied the
mutual recursor (one motive and one minor, where the group's recursor takes two
of each), so it was stuck on arity. Both problems are now fixed — the probe
supplies the full pre-major telescope — and the three clauses that no probe can
reach are pinned directly on the predicate in
`inductive_tests::the_k_like_predicate_*`, where the controls above do flip
them. The integration test that cannot attribute its own refusal now says so in
its doc comment instead of implying otherwise.

This is the repository's standing lesson in a new costume: *an empty result from
a tool that was never pointed at your subject is indistinguishable from a strong
negative result.* Four green negative tests, two of which were green for reasons
unrelated to the thing they named.

### Where a negative test could not be built

I could not construct an `add_declaration`-level witness in which dropping
clause 3 admits an **ill-typed** declaration, as opposed to admitting a
declaration whose proof needed a reduction it should not have got. The reason
looks structural rather than incidental: K over-firing makes two *terms*
definitionally equal, and our checker compares declared types by inference, so
the reduct's type does not follow the reduct. For a `Prop`-valued motive proof
irrelevance already identifies the two sides, so K adds nothing observable
there; the interesting case is a large-eliminating motive, and the minor premise
is pinned at the canonical index by construction. I am recording this as *not
achieved* rather than as *not possible* — it is the shape of question that wants
a dedicated session, and the `eq_rec_does_not_reduce_on_a_variable_index` +
control pair is what stands in for it.

## 6. The corpus

Re-running the committed census (`scripts/lean-import-census.sh`, the same 40
`Init`/`Std` declarations, so it is comparable to the previous lane's numbers):

| | collect | brecOn | **here** |
|---|---|---|---|
| streams admitting completely | 13 (uncounted corpus) | 37 of 40 | **40 of 40** |
| declaration records | — | 1255 | 1255 |
| declines | — | 13 | **0** |
| distinct root blockers | 10 | 1 | **0** |
| distinct cascades | 28 | 8 | **0** |

`eq_of_heq` imports (5 records, 9 declarations). So does `heq_of_eq`. The last
root blocker on this corpus is closed.

**No new fact, deliberately** — same reasoning as the previous lane. Nothing here
establishes a proposition we did not already hold; it is a *capability*, and a
capability is pinned by a test that regresses, not by a fact that would have to
be re-asserted. The corpus number is the honest headline and it is re-measurable
by one script.

## 7. Gates

- `cargo test -p axeyum-lean-kernel -p axeyum-lean-import` — **465 passed, 0
  failed**, of which **15 are new here**: 7 in `tests/k_like_reduction.rs`, 4
  `inductive_tests::the_k_like_predicate_*`, 4 in `tc_tests` for the cache.
- `cargo clippy -p axeyum-lean-kernel -p axeyum-lean-import --all-targets
  --all-features -- -D warnings` — clean.
- `./scripts/check-lean-gate.sh` — 12 suites, 49 tests, 113 real-Lean checks
  (floor 105), Lean 4.30.0 discovered automatically.
- `python3 scripts/validate-facts.py` — 0 errors.
- `scripts/check-fact-evidence-replay.sh` — green.
- `nat_theorem_inventory` 119 theorems; `nat: axiom=0 opaque=0 quotient=0`;
  `integer: axiom=1` — unchanged.

One existing test changed and it was **strengthened, not weakened**:
`whnf_cache_retains_only_the_current_environment_revision` used free variables
as its probe arguments, which are exactly the expressions no longer eligible for
the kernel-global cache. It now uses closed literals, and the property it used
to imply for open terms is asserted directly and in the opposite direction by
`open_expressions_never_enter_the_context_free_whnf_cache` — which also checks
that *every* key in that cache is closed, not just the one it put there.

## 8. What I did not do

- No end-to-end ill-typed-declaration witness for a dropped clause 3 (§5).
- No `to_cnstr_when_structure` (eta-expanding a non-constructor major of a
  non-recursive structure). Still not blocking anything.
- No `cheap_proj` ordering in `reduce_projection`. Still performance, not
  correctness.
- No re-pin of the toolchain (4.30.0 → current). Still one decision made once,
  still not made — this is the third diary to say so.
- The next corpus is not a bigger one of the same kind. 40/40 means this corpus
  has stopped measuring; what it should be replaced by is whatever exercises
  the rules we know we lack.
