# Lane: import-wfrec — ζ for a local `let` moves into `whnf_core`

<!-- plan-section: lane-status -->

**Diagnosed and fixed the top declined root in both Lean scale censuses,
`Nat.bitwise._unary`: it was a ζ (local `let`) rule this port placed at two
def-eq entry points instead of inside `whnf_core`, so a let-local exposed
*during* the lazy-delta loop was never unfolded** (`WIP`, import-wfrec,
2026-08-15). Continues [`import-strings`](89-import-strings.md), which located
this and left it unsized. Full write-up:
[`docs/formalized-math-2026-08/diary-import-wfrec.md`](../../formalized-math-2026-08/diary-import-wfrec.md).
Decision: [ADR-0462](../../research/09-decisions/adr-0462-local-let-zeta-belongs-inside-whnf-core.md).

**The pair, which is what the previous lane asked for.** In a context where `n'`
and `m'` are let-locals with values `n / 2` and `m / 2` — Lean's own
`let n' := n / 2` in `Nat.bitwise` —

```text
lhs  PSigma.casesOn.{1,1,1} Nat (fun _ => Nat) (fun _ => Nat) (PSigma.mk (n/2) (m/2)) (fun n m => n)
rhs  PSigma.casesOn.{1,1,1} Nat (fun _ => Nat) (fun _ => Nat) (PSigma.mk n'    m'   ) (fun n m => n)
```

Same head, same arity, all five arguments pairwise def-eq by our own `def_eq` —
pair refused. Their full weak-head normal forms are the **same interned
expression**.

**Why.** `PSigma.casesOn` is `Abbrev`, so `try_eq_const_app` (gated on
`Regular`/`Regular`, exactly as Lean's is) never notices the arguments agree.
Both sides δ-unfold, ι fires, and the loop continues with `n / 2` against the
bare let-local `n'`. `is_delta` reports `(Some, None)`, so the left side unfolds
forever — through `Nat.div` into a stuck `Decidable.rec` — while the right is
never ζ-reduced. Lean has no such hole because ζ lives in `whnf_core` itself
(`whnf_fvar`, `type_checker.cpp:346`), and `lazy_delta_reduction_step` calls
`whnf_core` after every unfolding.

**The fix is one arm that deletes two functions:** an `FVar` arm in
`whnf_no_unfolding_uncached`, after which `whnf_local_value` and `whnf_in` are
dead and removed. The existing `reduction_ctx_reads` tripwire is bumped in the
new arm on a **ζ hit**, so "a closed term cannot reach this" stays a run-time
check rather than a paragraph.

**That tripwire then fired, and it was mine** (fixed in `b3b483f87`; the
intervening commit is on `main`, so a bisect crossing it panics on Mathlib
streams `127.ndjson`/`118.ndjson`). The first arm counted every `FVar` head,
hit or miss. Reducing a *closed* expression can call inference — K-like
reduction infers its major, the single door from reduction into inference — and
that inference opens **its own** binders; reducing under them meets ordinary
valueless locals. A miss returns the term unchanged, exactly as an empty context
would, so it is not a context read; a hit is. Nothing in the committed suites
covered this — the corpus found it, which is the argument for censusing a corpus
nobody chose.

**The previous lane's "no new construct needed" assessment held**, and more
cheaply than it sized: no IR construct, no bootstrap, no reserved name, no
environment gate. Its *family* claim splits: the
`Std.DTreeMap.Internal.*.eq_def` roots really were this rule and are gone;
`Nat.Linear.*` is not, still declines, and is now the top root in both corpora.

**Negative tests with a removal control.** `local_let_zeta_reduction.rs`, four
tests, each positive paired with a control in the same test: the delta-exposed
case, the head-position case the old pass already handled, the refusal of a
*valueless* local, and a chained `let a := n; let b := a` needing ζ to be a fixed
point. Removing the new arm fails **exactly 2 of the 4** — the two the old pass
never covered. Removing `whnf_local_value`/`whnf_in` *after* the arm is in
changes **no** test outcome, which is what says the arm subsumes them.

**Checked by Lean.** `real_lean_local_let_zeta_crosscheck` (new, registered)
hands official Lean 4.30.0 the same four declarations and requires matching
verdicts, and reads `#print` back to confirm the `letE` survived elaboration so
a toolchain that zeta-expands early fails the suite instead of checking nothing.
Floor 109 → 111.

**A new diagnostic, and the trap in it.** `axeyum-lean-import` gained
`probe_first_decline`, which hands the staging kernel and the exact
`KernelError` to an inspector at the first decline and then fails closed;
`examples/wf_recursion_decline_probe.rs` narrows the pair. It reduces in an
**empty** `LocalContext`, so a let-local looks inert and the descent stops on a
bare `_fvar` the kernel would have reduced — which is exactly what it did here.
Its header now says so; read a bare `_fvar` as "ask the local context".

**What it bought, measured A/B rather than against a remembered number.** The
previous census ran under unknown load and a per-stream timeout is wall clock,
so both binaries — a pristine `lane-snapshot` of `HEAD` and the same plus this
lane — were run **concurrently on the same streams**, same bounds, and compared
**paired per stream**.

`Init`+`Std`, all 500: CLEAN 254 → **331 (50.8% → 66.2%)**, DECLINED 242 →
**165**, **77 DECLINED → CLEAN and not one stream moved the other way**; total
declines 97,341 → **34,993**, distinct cascade declarations 6,065 → **3,386**.
The baseline reproduced the strings lane's census *exactly* — 254/242/4,
634,291 records, 50 roots, 6,065 cascades — after a fresh re-export, so the
after-column measures the change and nothing else. That lane's projection was
"top 1 root fixed → 76 of 242 recovered"; measured 77.

Mathlib, 76 paired: CLEAN 24 → **39**, DECLINED 48 → **31**, **15 DECLINED →
CLEAN**, declines 51,040 → **15,735**, distinct decline roots **167 → 64**.

**The strings lane's "Mathlib's long tail is the instance hierarchy" was right,
and the instance hierarchy was this one rule.** `Nat.bitwise._unary` 81 → 0,
`Pi.preorder` and `Prop.partialOrder` 52 → 0, `DistribLattice.ofInfSupLe._proof_4`
42 → 0, `Lean.Grind.Ring.toIntModule` 37 → 0, `Pi.addMonoid` and
`Function.Injective.partialOrder` 36 → 0 — 179 of 217 distinct roots gone, none
individually diagnosed. Twenty-six roots are new, which is the census working:
declarations that used to be `UnknownConst` cascades behind a refused ancestor
are now reached and refuse on their own account.

**The cost is wall clock, and it is Lean's cost too.** On Mathlib four streams
moved to RESOURCE (two previously DECLINED, two previously reader-record-capped):
a stream that used to give up at a def-eq failure now keeps reducing. On
`Init`+`Std` nothing regressed at all.

**Next, located and probed post-fix.** `Nat.Linear.Poly.denote_reverse` /
`…ExprCnstr.denote_toNormPoly` is now the top root in **both** corpora. Its pair
is `Prod.rec.{1,0,0}` (6 args) against
`(Nat.brecOn.go.{1} motive (Nat.Linear.Var.denote v …) Nat.mul._f).1` (1 arg) —
a projection of a *stuck* `brecOn` application. And Lean has a rule for exactly
this that we do not: `lazy_delta_reduction_step` (`type_checker.cpp:884`), when
only one side is δ-reducible, first tries `try_unfold_proj_app` on the *other*
side, with the comment that otherwise it "would keep lazy unfolding
`expensive_term` (e.g. it contains function defined using well-founded
recursion)". Our `lazy_delta_step` has the `(Some, None) => delta(x)` arm and no
projection branch, and no `lazy_delta_proj_reduction`. That is the next thing to
measure — not yet a claim that it is the whole fix.

<!-- plan-section: landed-changes -->

| 2026-08-15 | `72207c6ba` | ζ for local `let`s moved into `whnf_core` (ADR-0462), matching Lean's `whnf_fvar`: a let-local exposed during lazy delta is now unfolded, `whnf_local_value`/`whnf_in` deleted as subsumed. Clears `Nat.bitwise._unary`, the top declined root in both scale censuses, and takes the paired `Init`+`Std` clean rate from 254/500 to **331/500** (77 streams recovered, none lost) and Mathlib's distinct decline roots from 167 to 64. Four negative tests with a removal control, a real-Lean crosscheck (floor 109 → 111), and `probe_first_decline` + a decline-narrowing probe example in `axeyum-lean-import`. |
| 2026-08-15 | `b3b483f87` | A ζ **miss** is not a local-context read: counting it fired the closed-expression WHNF-cache tripwire on real Mathlib streams, because reducing a closed term can call inference which opens its own binders. Count only a hit, pinned by `tc_tests::local_let_zeta_fires_in_whnf_core_and_only_a_hit_is_a_context_read` with a removal control. |
