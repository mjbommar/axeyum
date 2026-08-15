# Diary — lane `import-wfrec`, 2026-08-15

Continuing [`diary-import-strings.md`](diary-import-strings.md), which landed
primitive `String` literals, re-censused both corpora, and handed over one named
target with the sizing left open: `Nat.bitwise._unary`, the top declined root in
both censuses, *"a def-eq gap on a shape the kernel already represents, so the
work is diagnosis first and the fix is unsized until the mismatch is exhibited
as one pair of terms."*

Outcome in one line: **the pair is exhibited, it is a ζ (local `let`) rule that
this port put in the wrong place, the fix is one arm in the reduction loop that
deletes two functions, and it takes the `Init`+`Std` clean rate from 254 of 500
to 331 of 500 while erasing 129 of Mathlib's 167 distinct decline roots.**

## 1. The pair

```text
lhs  PSigma.casesOn.{1,1,1} Nat (fun _ => Nat) (fun _ => Nat)
       (PSigma.mk (n / 2) (m / 2)) (fun n m => n)

rhs  PSigma.casesOn.{1,1,1} Nat (fun _ => Nat) (fun _ => Nat)
       (PSigma.mk n'       m'    ) (fun n m => n)
```

in a local context where `n'` and `m'` are **let-bound locals** with values
`n / 2` and `m / 2` — Lean's own `let n' := n / 2` in the source of
`Nat.bitwise`.

Same head. Same arity. All five arguments pairwise definitionally equal by our
own `def_eq`. Pair refused.

And the fully weak-head-normalized forms of the two sides are the **same
interned expression** — `ExprId(62170)`, printed by the probe in the run that
found it. So `def_eq` said `false` about a pair whose normal forms are literally
one term.

## 2. Why, exactly

`def_eq_core_uncached` ran `whnf_no_unfolding` (no δ) and then a separate
`whnf_local_value` pass, twice, at the top — and `whnf_local_value` only ever
looked at the *head* of a spine. `lazy_delta_step` then took over and never
consulted it again.

`PSigma.casesOn` carries `ReducibilityHint::Abbrev`, so `try_eq_const_app` (which
is gated on `Regular`/`Regular`, exactly as Lean's optimization is gated on
`d_t->get_hints().is_regular()`) does not fire and never gets to notice that the
five arguments agree. Both sides δ-unfold; ι fires on each; the loop continues
with `n / 2` on the left and the bare let-local `n'` on the right. `is_delta`
now reports `(Some, None)`, so the left side is unfolded — through `HDiv.hDiv`,
`Nat.div`, into a `Decidable.rec` stuck on `Nat.decLe 2 n` — while the right
side sits at `n'` and is never ζ-reduced. Delta exhausts, every structural rule
fails on `Decidable.rec …` against an `FVar`, and the answer is `false`.

Lean does not have this hole because **ζ for a local `let` lives inside
`whnf_core`**, not at the entry points (`references/lean4` at `d024af0`):

```cpp
// type_checker.cpp:401  whnf_core
case expr_kind::FVar:
    if (is_let_fvar(m_lctx, e)) break; else return e;
...
case expr_kind::FVar: return whnf_fvar(e, cheap_rec, cheap_proj);

// type_checker.cpp:346
expr type_checker::whnf_fvar(...) {
    if (auto decl = m_lctx.find_local_decl(e))
        if (auto const & v = decl->get_value())
            return whnf_core(*v, cheap_rec, cheap_proj);   /* zeta-reduction */
    return e;
}
```

and `lazy_delta_reduction_step` calls `whnf_core(*unfold_definition(t_n), …)`
after every unfolding. So in Lean the rule reaches wherever δ reaches. In ours
it reached two call sites.

[ADR-0462](../research/09-decisions/adr-0462-local-let-zeta-belongs-inside-whnf-core.md).

## 3. The fix

An `FVar` arm in `whnf_no_unfolding_uncached` — this port's `whnf_core` — and
then `whnf_local_value` and `whnf_in` are dead and deleted:

```rust
ExprNode::FVar(fvar) => match ctx.value_of(fvar) {
    Some(value) => {
        self.reduction_ctx_reads += 1;
        cursor = self.foldl_apps(value, args.iter().copied());
    }
    None => return cursor,
},
```

`reduction_ctx_reads` is the existing tripwire that asserts a *closed*
expression never reads the local context, which is what keeps the kernel-global
WHNF cache's context-free key sound. The new arm bumps it on a **hit**, so the
argument that a closed term cannot reach it is a run-time check rather than a
paragraph.

### The tripwire fired, and it was mine

The first version of that arm bumped on every `FVar` head, hit or miss. The
census found it within 250 Mathlib streams:

```text
thread 'census' panicked at tc.rs:716:
reducing a closed expression read the local context; the kernel-global whnf
cache key has no context component and would be unsound
  left: 86723  right: 86715
```

A false positive, by a mechanism the tripwire's own doc comment does not cover.
Reducing a *closed* expression can call **inference** — K-like reduction infers
its major, and `k_like_major` is the single door from reduction into inference —
and that inference opens **its own** binders. Reducing under them meets ordinary
valueless locals; their lookups returned `None` and changed nothing, and were
counted anyway.

So count only a hit. A miss returns the term unchanged, which is exactly what an
empty context would return, so it cannot be a dependence on the context; a hit
is the context changing the reduct, which is precisely what the cache key must
not hide. `tc_tests::local_let_zeta_fires_in_whnf_core_and_only_a_hit_is_a_context_read`
pins both halves at the level the counter lives, with the removal control
(counting misses again fails exactly that assertion).

Two things worth keeping from this. First, **nothing in the committed suites
covered it** — the corpus found it, which is the argument for censusing a corpus
nobody chose. Second, it took `72207c6ba` to `b3b483f87` to get right, and the
intervening commit is on `main`: a bisect crossing it will panic on Mathlib
streams `127.ndjson` and `118.ndjson`.

## 4. The previous lane's assessment, tested rather than assumed

It held, and more cheaply than it sized. **No new IR construct, no new
bootstrap, no new reserved name, no environment-shape gate.** The whole change
is one arm in the reduction loop and the removal of two functions that the arm
subsumes. The strings lane's leverage estimate — *"comparable to the `Proj`/`Proj`
congruence fix … one narrow def-eq rule, a large fraction of the roots"* — was
the right shape of guess.

Its family claim — that `Nat.Linear.*` and the `Std.DTreeMap.Internal.*.eq_def`
roots are "the same family" — is **half right, and the census says which half**.
The `eq_def` roots really were the same missing rule and are gone
(`Std.DTreeMap.Internal.Impl.modify.eq_def` 58 → 0,
`…Const.modify.eq_def` 58 → 0 on the 500-stream `Init`+`Std` pair).
`Nat.Linear.*` is not: it still declines after
this fix, and its pair is `Prod.rec …` against `(Nat.brecOn.go … ).1` — a
projection of a `brecOn`, a different question. It is now the **top** root in
both corpora. §7 has the numbers.

## 5. How the pair was actually found, including the wrong turn

`lean4export_census` prints `TypeMismatch { expected: ExprId(61873), got:
ExprId(61879) }`. Two arena indices are not a diagnosis and cannot be printed
after the fact, because the staging kernel is dropped with the census. So
`axeyum-lean-import` gained `probe_first_decline`, which drives a stream through
the same gate and hands the failing kernel *and* the exact `KernelError` to a
caller-supplied inspector at the first decline, then fails closed as before.
Nothing is published: the inspector's bound is higher-ranked, so the staging
kernel cannot escape the call, and the refused declaration is not in it.

`crates/axeyum-lean-import/examples/wf_recursion_decline_probe.rs` is the
inspector: it renders both sides and walks down — whnf, spine, congruence,
binders — printing the first pair at each depth the kernel says is not def-eq.

**And it lied to me, in a way worth recording.** `KernelError` carries two
`ExprId`s and nothing else, so the probe reduces them in a *fresh, empty*
`LocalContext`. Its descent stopped at

```text
depth=2  lhs = _fvar.34
         rhs = Decidable.rec.{1} (LE.le Nat instLENat 2 _fvar.23) …
```

which reads as "the kernel is stuck on an opaque local against a `Nat.div`
reduct". It is not: `_fvar.34` has a *value* in the real context, and in the
probe's empty one it is inert. Dumping the actual local context at the failure
is what turned the picture around —

```text
TCDUMP|fvar=34|value=HDiv.hDiv Nat Nat Nat (instHDiv Nat Nat.instDiv) _fvar.23 2|type=Nat
TCDUMP|fvar=35|value=HDiv.hDiv Nat Nat Nat (instHDiv Nat Nat.instDiv) _fvar.24 2|type=Nat
```

— and re-running the descent *inside* that context is what produced §1. The
probe now says this in its own header, because the next lane will point it at
the next root and get the same misleading stop. Read a bare `_fvar.N` in its
output as "ask the local context", never as "the kernel is stuck here".

## 6. Negative tests, and the removal control

`crates/axeyum-lean-kernel/tests/local_let_zeta_reduction.rs`, four tests, every
positive paired with a control in the same test so a positive cannot pass
because the rule was switched on globally and stopped discriminating. The
fixture is the minimal reproducer, stripped of everything `Nat.bitwise` brings:

```text
axiom N  : Type
axiom g  : N → N                       -- opaque, for the controls
axiom K  : ∀ (a : N), Eq.{1} N a a → N  -- second argument's type mentions the first
def   id2 : N → N := fun x => x         -- δ-reducible, so the delta loop runs
def probe : N → N := fun n => let n' : N := n; K n (@Eq.refl.{1} N (id2 n'))
```

`id2 n' =?= n` is the obligation, and because `id2` is a definition and `n` an
ordinary local, `lazy_delta_step` unfolds the left side and only *then* is a
let-local a head — the exact position the old pass could not see. Everything
goes through `Kernel::add_declaration`, never `def_eq` directly, because the
gate is what has to be right.

The four: the delta-exposed positive (+ control binding `n'` to `g n`); the
head-position positive that the old pass already handled (+ its control); the
refusal of a *valueless* local, so ζ is not an excuse to identify two lambda
binders; and a chained `let a := n; let b := a` that needs ζ to be a fixed point
rather than one step (+ its control).

**Removal control, because a rule that exists is not a rule that fires.** Delete
the new `FVar` arm and re-run:

| removed | tests that fail |
|---|---|
| the `FVar` ζ arm in `whnf_no_unfolding` | **2** — delta-exposed, chained |
| — head-position and valueless-local | **0**, as they must: the old pass covered the first and neither pass covered the second |

and in the other direction, deleting `whnf_local_value` and `whnf_in` after the
arm is in changes **no** test outcome (500 passing before and after, clean
snapshot). That is what says the arm subsumes them rather than coexisting.

## 7. What it bought

The retained root streams under `/nas3/data/axeyum/lean-import-scale/roots/`,
90 s and 8 GB each. The "before" column is the previous lane's recorded result,
the "after" column is measured here:

| stream | before | after |
|---|---|---|
| `Nat.bitwise._unary` | 301 of 302 records, 1 decline | **302 of 302, 367 declarations, 0 declines** |
| `UInt16.toFin_ofNatTruncate_of_lt` | clean | clean |
| `Nat.Linear.Poly.denote_reverse` | 1 decline | 1 decline (different shape — §4) |
| `Fin.shiftRight_val` | 1 decline | 1 decline |
| `List.attach_cons` | 1 decline | 1 decline |
| `Char.toUpper`, `Char.utf8Size.fun_cases_unfolding`, `UInt32.ofFin_lt_iff_lt` | runaway | runaway, both binaries |

### The corpus, measured A/B rather than against a remembered number

The strings lane's census numbers are not a usable baseline for this: they were
taken under whatever load that machine had, and this box runs several lanes
(`load average` 11–22 during this session). A per-stream timeout is wall clock,
so a RESOURCE count is a statement about contention as much as about the
kernel. So both binaries were run **concurrently, on the same retained streams,
with the same bounds** — a pristine `lane-snapshot` of `HEAD` against the same
snapshot plus this lane's files, 4 jobs each, 120 s, 8 GB — and the comparison
below is **paired per stream**, not two aggregates.

**Mathlib**, `mathlib-sample-400`'s retained streams, 76 paired (the "after"
run is slower per stream and was stopped when the Init+Std pair was ready; the
sample is the first 76 in the deterministic file order, which is itself the
seeded sample order):

| | before | after |
|---|---:|---:|
| CLEAN | 24 | **39** |
| DECLINED | 48 | **31** |
| RESOURCE (120 s) | 2 | 6 |
| reader record cap | 2 | 0 |
| total declines | 51,040 | **15,735** |
| `TypeMismatch` / `NotAPi` roots | 801 / 11 | **125 / 0** |
| **distinct decline roots** | **167** | **64** |

Transitions: **15 DECLINED → CLEAN**. Four cost transitions, all to the wall
clock: two DECLINED and two record-capped streams now time out, because a
stream that used to give up at a def-eq failure now keeps reducing. That is the
price of the rule, and it is Lean's price too — Lean performs the same ζ.

The root table is where the size shows. **129 of 167 distinct roots
disappear**, and they are precisely the tail the strings lane named as
Mathlib-specific:

| root | before | after |
|---|---:|---:|
| `Nat.bitwise._unary` | 37 | **0** |
| `Pi.preorder`, `Prop.partialOrder` | 21, 21 | **0, 0** |
| `Lean.Grind.Ring.toIntModule` | 18 | **0** |
| `DistribLattice.ofInfSupLe._proof_4` | 17 | **0** |
| `Pi.addMonoid` | 16 | **0** |
| `Function.Injective.{partialOrder, addCommSemigroup}` | 15, 15 | **0, 0** |
| `Nat.{instMulZeroOneClass, instAddCommMonoidWithOne, instNonUnitalNonAssocSemiring, instSemigroupWithZero}` | 15 each | **0** |
| `Nat.Linear.Poly.denote_reverse` / `…ExprCnstr.denote_toNormPoly` | 27 / 27 | 26 / 26 |

So the strings lane's *"Mathlib's long tail is the instance hierarchy"* was
true, and the instance hierarchy was **this one rule**. `AddEquiv.trans`,
`AddMonoidHom.ker`, `AddSubgroup.instTop`, `AlgHom.id`, `Additive.addSemigroup`
… 129 of them, all gone, none individually diagnosed.

Twenty-six roots are **new**, which is the census working as designed rather
than a regression: a declaration that used to be an `UnknownConst` cascade
behind a refused ancestor is now reached and refuses on its own account
(`Std.DTreeMap.Internal.Impl.*`, `Cauchy.map`, `Polynomial.toFinsupp_add`, …).
The distinct-root count still falls by 62%.

> The first version of this table was **wrong, in my favour**, and the way is
> worth one line. The two runs had censused different *numbers* of streams when
> I read them, and my analysis counted roots over each run's own completed set —
> so "before" was summed over 169 streams and "after" over 76, inflating every
> before-column number by about 2.2x. A paired comparison has to be paired all
> the way down, not just in the status counts. The table above counts roots over
> the 76 streams both runs finished.

### `Init`+`Std`, and the baseline reproduces the previous lane exactly

For `Init`+`Std` the corpus had to be rebuilt: the census script deletes each
stream after reading it, so the strings lane's 500 were gone. Re-exported once
from the same `corpus.txt` (3.6 GB, `lean4export Init Std` per declaration) so
that *both* binaries read the identical bytes rather than two separate exports —
and this time **retained**, under
`/nas3/data/axeyum/lean-import-scale/initstd-500-streams/`, with the corpus
list, both paired analyses and the script that produced them. The next lane can
run its own A/B on this corpus without paying the twenty minutes of export
again, and against bytes that are provably the same.

The baseline run then reproduced the previous lane's census **exactly** — not
approximately:

| | strings lane, 2026-08-15 | this lane's `HEAD` baseline |
|---|---:|---:|
| CLEAN / DECLINED / RESOURCE | 254 / 242 / 4 | 254 / 242 / 4 |
| declaration records | 634,291 | 634,291 |
| distinct roots / cascades | 50 / 6,065 | 50 / 6,065 |

which is worth more than it looks: it says the corpus, the harness and the
kernel are all deterministic across a day and a re-export, so the "after" column
below is measuring the change and nothing else.

Paired, **all 500 streams**:

| | before | after |
|---|---:|---:|
| CLEAN | 254 (50.8%) | **331 (66.2%)** |
| DECLINED | 242 | **165** |
| RESOURCE | 4 | 4 |
| total declines | 97,341 | **34,993** |
| of which `UnknownConst` cascades | 96,175 | **33,855** |
| distinct cascade declarations | 6,065 | **3,386** |
| distinct decline roots | 50 | 51 |

**77 DECLINED → CLEAN, and not one stream moved the other way** — no new
RESOURCE, no new decline, and the same 634,291 declaration records reach the
gate in both runs. The strings lane's cumulative projection for this corpus was
*"top 1 root fixed → 76 of 242 declined streams recovered"*. Measured: **77 of
242**. Their arithmetic was right to within one stream.

| root | before | after |
|---|---:|---:|
| `Nat.bitwise._unary` | 236 | **0** |
| `Std.DTreeMap.Internal.Impl.{,Const.}modify.eq_def` | 58, 58 | **0, 0** |
| `Std.DHashMap.Internal.Raw₀.filter` | 51 | **0** |
| `Nat.Linear.Poly.denote_reverse` / `…ExprCnstr.denote_toNormPoly` | 153 / 153 | 153 / 153 |
| `Std.Internal.List.keys_eq_map` | 93 | 93 |
| `ByteArray.*`, `List.*_toByteArray` | 14–24 each | unchanged |

The distinct-root count barely moves (50 → 51) because `Init`+`Std`'s tail is
short and *broad*: seventeen roots go, eighteen newly-reachable ones arrive
(`Std.DTreeMap.Internal.Impl.{balanced_glue, size_glue, *_eq_*!}`), and the
container/`ByteArray` cluster the previous lane named is untouched by ζ. The
stream-level win is nonetheless **a third of everything that was declining**,
and the cascade count halves.


## 8. Checked by Lean

`crates/axeyum-lean-kernel/tests/real_lean_local_let_zeta_crosscheck.rs` (new,
registered in `scripts/check-lean-gate.sh`, floor 109 → 111) hands official Lean
4.30.0 the same four declarations and requires its verdicts to match ours —
positives accepted, controls rejected.

The honest caveat is in the file: `lean file.lean` runs the elaborator first,
and the elaborator's `isDefEq` has ζ on, so it would accept the positives even
if Lean's kernel could not. Two things keep it from being vacuous. Lean's `let`
elaborates to `Expr.letE` and Lean's kernel `infer_let` pushes a local *with a
value* exactly as ours does, so the kernel does face the obligation; and the
test reads `#print probe` back and requires a `let`/`have` to have survived
elaboration, so a toolchain that zeta-expands early fails the suite instead of
quietly checking nothing. (Measured: 4.30.0 prints `have n' := n;` — a
non-dependent `letE` is rendered `have`, same kernel node.)

The claim that the rule fires *in the position that was broken* is carried by
the removal control in §6 and by `Nat.bitwise._unary` importing clean, not by
this file.

## 9. Gates

All run in a `scripts/lane-snapshot.sh` of the commit under test, never in the
shared worktree — a concurrent `kernel-reuse` lane's in-progress
`prelude_cache.rs` sat in this crate for most of the session and failed
`clippy::single_match_else` until it landed, which would have made every
worktree run of a kernel gate report that lane's state rather than mine.

- `cargo test -p axeyum-lean-kernel -p axeyum-lean-import` — **512 passed, 0
  failed** at `016190b2c` (this lane's last commit, with `kernel-reuse`'s
  prelude-cloning work already merged in). 502 at this lane's own last code
  commit.
- `cargo clippy -p axeyum-lean-kernel -p axeyum-lean-import --all-targets
  --all-features -- -D warnings` — clean, same snapshot.
- `scripts/check-lean-gate.sh` — **15 suites, 52 tests, 122 real-Lean checks**,
  floor raised 109 → 111, Lean 4.30.0. Nonzero and above floor.
- `RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-lean-kernel --no-deps` —
  clean. It was **not** before this lane: `whnf`'s doc linked the private
  `Kernel::whnf_core`, which the strings lane found and left. The line became
  mine, so it is fixed.
- `python3 scripts/validate-facts.py` — 99 facts, 0 errors.
  `python3 scripts/gen-adr-index.py` — 464 rows. `./scripts/check-links.sh` —
  all links ok.
- **Failing before this lane and still failing, not mine:**
  `python3 scripts/check-parity-docs.py` reports four missing-marker errors
  (`73/73 accepted`, the 70-example inventory in two files, the CI representative
  Lean gate line). Confirmed identical on a pristine `HEAD` snapshot taken
  before this lane's first commit; it belongs to the examples-sweep work in
  flight.
- **Not run:** the full `just check`, for the clippy reason above.

## 10. What I did not do

- **`Nat.Linear.Poly.denote_reverse`, now the top root in both corpora.** It is
  probed — post-fix, with the same `wf_recursion_decline_probe` — and the pair
  is a *different* shape, so it gets its own lane rather than a guess here:

  ```text
  depth=1  lhs_head = Prod.rec.{1,0,0}                                    (6 args)
           rhs_head = (Nat.brecOn.go.{1} motive (Nat.Linear.Var.denote v (…)) Nat.mul._f).1   (1 arg)
           STOP: ARITY differs
  ```

  A `Prod.rec` application against a **projection of a stuck `brecOn.go`
  application**. And there is a named rule of Lean's that we do not have. In
  `lazy_delta_reduction_step` (`type_checker.cpp:884`), when exactly one side is
  δ-reducible Lean first asks whether the *other* side is a projection
  application it could unfold instead:

  ```cpp
  } else if (d_t && !d_s) {
      if (auto s_n_new = try_unfold_proj_app(s_n)) { s_n = *s_n_new; }
      else { t_n = whnf_core(*unfold_definition(t_n), false, true); }
  }
  ```

  with the comment that without it *"we would keep lazy unfolding
  `expensive_term` (e.g. it contains function defined using well-founded
  recursion)"* — which is this declaration exactly. Our `lazy_delta_step` has
  the `(Some, None) => x = delta(x)` arm and **no** `try_unfold_proj_app`, and
  no `lazy_delta_proj_reduction` either. That is the next thing to measure; it
  is not a claim that it is the whole fix.
- **The rest of the tail.** After this lane `Init`+`Std` and Mathlib both still
  have a `Std.DTreeMap.Internal.Impl.*` cluster (`balanced_glue`, `size_glue`,
  `toListModel_{min,max}View`, `*_eq_*!`), most of it *newly visible* because
  those declarations are now reached at all.
- **The runaway streams.** `Char.toUpper`, `Char.utf8Size.fun_cases_unfolding`
  and `UInt32.ofFin_lt_iff_lt` still exhaust their bounds without answering.
  ζ moving into the reduction loop did not change that either way.
- **The toolchain re-pin (4.30.0 → current).** Sixth diary to say so.
