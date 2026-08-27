# Why there is no exact IVT root yet, verified at the kernel

**2026-08-26.** Three results — exact `lt` reflection, Chapter 12's inverse
function theorem, and **tightness of apartness** (`¬ Apart x y → Equiv x y`) —
all wait on an *exact* preimage. `CReal.ivt_approx` supplies an *approximate*
one. A lane was sent to settle whether the gap closes.

**It does not, and the answer is overdetermined: two independent obstructions,
either of which alone is fatal.** The lane verified both from source rather than
citing precedent, which is what makes this worth recording.

## Obstruction 1: the sequence cannot be formed

`ivt_approx`'s conclusion is `∀ e, ∃ x, …`; `ivt_iter`'s is `∀ n, ∃ P Q, …`.
Building a limit needs `f : Nat → CReal` **as data**, and `converges_of_cauchy`
takes exactly that. You cannot project the witness out of an `Exists`.

The lane did not stop at "Lean works that way" — it read this kernel's own rule,
`inductive.rs`'s `allows_large_elimination`:

```rust
let allows_large_elimination = self.level_is_nonzero(group.result_level)
    || (group.families.len() == 1
        && match group.families[0].constructors.as_slice() {
            [] => true,
            [constructor] => constructor.exposes_non_prop_fields,
            _ => false,
```

For `Exists (motive : α → Prop) : Prop`, the constructor's field `w : α` is not
among the **result indices** (`Exists motive` has none), so
`exposes_non_prop_fields` is false and `Exists.rec` is `Prop`-only here.
`Or.rec` fails the same test on the two-constructor arm — so even
`lt_cotrans`'s branch choice cannot drive a data-level recursion.

This is the wall `pos_bound_of_lt` hit, and the reason `CReal.inv` takes an
explicit `Nat`. **It is structural, not a missing helper.**

## Obstruction 2: the slack never shrinks

Even granting data extraction, `{x_e}` is not Cauchy, and the reason is not
incidental. `ivt_approx` picks a **fresh** slack `eps(e) := 1/(2e+2)` and a
**fresh** bisection depth per accuracy `e`, and each step's branch is chosen by
`lt_cotrans` against the fixed pair `(−eps, eps)`. Different `e` therefore take
**different bisection trajectories** — not a shared nested refinement.

A single fixed-`eps` run of `ivt_iter` *does* give literally nested brackets with
geometrically shrinking width. But its slack is an **invariant maintained
throughout, not a decreasing quantity**, so its limit recovers `|F r| ≤ eps` for
that one `eps` and never an exact root.

That distinction — *width shrinks, slack does not* — is the crux, and it is
invisible from the theorem statement.

## What would remove it, and it is two new slices

1. **A data-valued bisection**, replacing the `Exists`-wrapped `ivt_iter`:

   ```text
   CReal.ivt_bisect : (F : CReal → CReal) → CReal → CReal → CReal → Nat → (CReal × CReal)
   ```

   buildable by ordinary `Nat.rec` into `Type` (`Nat`'s result level is nonzero,
   so it passes the rule above). The per-step branch must become **computable
   data**: `CReal.mk : (f : Nat → Rat) → Regular f → CReal` makes the
   representative sequence accessible, so the choice can be decided by comparing
   a sufficiently precise **rational** approximation of `F m` against the
   rational `eps` using ℚ's decidable order — with a companion `Prop`-valued
   spec theorem proving that data choice satisfies the same six-part invariant.

   **Note: this kernel has no `Prod` and no `Sigma`** (checked — nothing declared
   outside `inductive_tests.rs`), so the pair result needs a new minimal
   `Type`-valued two-field structure, or two mutually recursive
   `Nat → CReal` functions.

2. **A diagonal bisection with shrinking slack** `eps_n → 0` on top of (1),
   carrying a strengthened invariant relating width and slack **jointly**. Not a
   corollary of `ivt_iter`; comparable new work.

## The pattern this is the sixth instance of

In a setting where `Exists.rec` eliminates only into `Prop`, **a computed
projection is worth more than a proved existence.** That has now decided the
form of `CReal.inv` (explicit `Nat` modulus), `CReal.bound` (total projection,
not a search), `bucketIndex`, `mesh_le_of_ge` (reads its Archimedean witness off
`bound` rather than eliminating `archimedean`'s `∃`), the boundedness theorem's
return type, and now this.

**When a construction stalls here, the first question is whether the thing you
need is stated as an existence rather than computed.**

---

## `CReal.ivt_bisect` landed — and the design beat the sketch

The data-valued bisection is built. Three decisions, two of them better than what
this note proposed.

**1. The pair carrier: none.** The sketch offered a new `Type`-valued two-field
structure or two mutually recursive functions. The lane took neither:

```text
CReal.ivt_bisect : (CReal → CReal) → CReal → CReal → Nat → Nat → Bool → CReal
```

**one `Nat.rec` into `Bool → CReal`** — a plain Pi type, so **no new inductive at
all**. `ivt_bisect_lo`/`_hi` are one-line projections at `Bool.false`/`Bool.true`.
Two independent recursions were rejected for a concrete reason: each step's
midpoint needs *both* current endpoints, so they would have had to reconstruct
the identical pairing anyway.

That is worth generalising. **A function into `Bool → X` is a pair of `X`s that
costs no carrier**, and this kernel has no `Prod` or `Sigma`. Anywhere a
construction wants to return two things, this is available today.

**2. The branch: `Rat.ble`, a genuine `Bool`.** `ivt_step` decides with
`lt_cotrans`, which is `Prop` and unusable in a `Type`-valued recursion. Here the
branch is `Rat.ble s thresh` on a **rational sample** of `F m` — legitimate
precisely because ℚ's order is decidable where `CReal`'s is not — and `Bool.rec`
then selects a `CReal` freely. `sqrt.rs`'s `natSqrt` already makes the same move
one type down.

**3. A third decision this note did not anticipate.** `eps` cannot be an
arbitrary `CReal`: **a real carries no `Nat` for a construction to sample at.**
So it is an explicit `Nat` `n`, with `eps_n := ofRat (natDivSucc 1 n)`. That is
the same constraint already forced on `CReal.inv`'s modulus — and it is the
seventh instance of the pattern this note ends on.

Sampling index: `j := succ (2n)`, fixed at every step, threshold
`thresh := natDivSucc 1 j`. By `natDivSucc_halve`, `thresh + thresh ~ eps_n`
exactly, so `thresh` is `eps_n/2`.

## The test that was impossible before

`F := id` on the asymmetric bracket `[−1, 2]`, `n := 0` (so `eps = 1`,
`j = 1`, `thresh = 1/2`):

| k | midpoint | `F m` vs `1/2` | bracket | width |
|---|---|---|---|---|
| 0 | — | — | `(−1, 2)` | 3 |
| 1 | `1/2` | `≤` | `(1/2, 2)` | 3/2 |
| 2 | `5/4` | `>` | `(1/2, 5/4)` | 3/4 |

All confirmed by the kernel's own reduction, both branches of `Rat.ble` exercised.

**This is the first test in the IVT development that could catch a
transposed-branch defect** — swapping the two branches type-checks identically
and computes a different function. A `Prop`-valued bisection has no reduction to
check; a data-valued one does. That is a second reason to prefer computed
constructions here, independent of the elimination rule.

## Still open

The **invariant spec theorem**: that this computed bracket satisfies `ivt_step`'s
six-part invariant. It needs a "remembering" `Bool.rec` at every step, converting
the computed `Bool` back into a `Prop` fact via `ble_eq_true_of_le` /
`le_of_ble_eq_true` — comparable in size to `ivt_step` itself. And after that,
the diagonal version with shrinking slack.

**Landed** (a later lane): `CReal.ivt_bisect_invariant` proves exactly this,
by ordinary `Prop`-induction on `k` (no `Exists.rec`), for the FIXED slack
`eps_n := ofRat (natDivSucc 1 n)` `ivt_bisect` already carries as its explicit
parameter `n`. See `CRealPrelude::ivt_bisect_invariant`'s doc comment.

---

## The diagonal construction — landed as data, and it does not give an exact root

Two independent, kernel-verified counterexamples, both on `F := id` on
`[−1, 2]` (the same instance every reduction test in this file uses).

**Design, worked on paper first, per this task's own requirement.**
`ivt_bisect`'s `step` closure already receives the recursion depth `j` as an
argument and discards it, closing over a fixed external `n` instead. The
"diagonal" move is to use `j` itself in place of that captured `n`:
`(sample_idx, thresh) := bisect_sample_index(j)`, recomputed at every step
from the step's own depth — `succ (2·j)` and `natDivSucc 1 (succ (2·j))`. No
second `Nat` parameter, one `Nat.rec`: `CReal.ivt_bisect_diag`. Concrete
numbers for `F := id` on `[−1, 2]`: step `j=0` uses `thresh_0 = 1/2` (`eps_0 =
1`); step `j=1` uses `thresh_1 = 1/4` (`eps_1 = 1/2`). Bracket: `k=0: (−1, 2)`
width `3`; `k=1: (1/2, 2)` width `3/2` (`F(1/2) = 1/2 ≤ 1/2`, lo moves); `k=2:
(1/2, 5/4)` width `3/4` (`F(5/4) = 5/4 > 1/4`, hi moves) — both the width and
the per-step slack shrink, verified in the kernel by
`ivt_bisect_diag_reduces_on_the_identity_bracket_neg_one_two`.

**Does the invariant close? No — verified by extending the same trace, exact
rational arithmetic, no informal step:**

```
j   thresh_j   F(m)      branch    lo        hi
0   1/2        1/2       lo moves  1/2       2
1   1/4        5/4       hi moves  1/2       5/4
2   1/6        7/8       hi moves  1/2       7/8
3   1/8        11/16     hi moves  1/2       11/16
4   1/10       19/32     hi moves  1/2       19/32
...                                1/2   -> 1/2  (from above)
```

`lo` is accepted **once**, at step `j=0`, against the COARSEST slack in the
entire run (`eps_0 = 1`, the largest value `eps_j` ever takes), and is never
tested again: only the endpoint that MOVES at a step gets re-examined against
that step's tighter threshold, so a stationary endpoint's bound is frozen at
whatever justified its last move, however early. Here `hi` moves at every
subsequent step (the sample is always `> thresh_j`) and its width shrinks
geometrically, forcing `hi_k → 1/2`. Since `lo_k = 1/2` for all `k ≥ 1`, the
bracket converges to `L = 1/2` — but the true root is `0`, and `F(1/2) = 1/2`
is not `0` and does not shrink toward it: this is a **fixed real number**,
constant for all `k` past the first step, not an artifact of finite
precision. No joint width/slack invariant closes here because the claim
itself is false for this instance.

**The other natural reading of "diagonal" fails independently, for the
opposite reason — non-nesting, not a frozen bound.** Interpret "diagonal" as
re-running `ivt_bisect`'s own two-parameter interface fresh from `(P0, Q0)`
for `k` steps at slack `n := k` (i.e. `ivt_bisect F P Q k k`, both arguments
set equal), rather than folding the schedule into one recursion. Since all
`k` steps of a given run share `n`'s single threshold, changing `k` changes
EVERY step's threshold at once, which can flip an early decision:

```
k   bracket           k   bracket
1   (−1, 1/2)         3   (1/8, 1/2)
2   (−1/4, 1/2)       4   (−1/16, 1/8)
```

`k=3`'s bracket `(1/8, 1/2)` and `k=4`'s `(−1/16, 1/8)` are not nested (their
interiors are disjoint) — exactly the diary's original obstruction-2 symptom
("different `e` take different bisection trajectories"), reproduced here for
`k` instead of the caller's accuracy target. No shared refinement exists for
a limit argument to close over, independent of the frozen-bound problem
above.

**Conclusion.** Both natural diagonal constructions from this bisection are
closed off for a general `F` satisfying only the one-sided approximate-IVT
sign hypothesis. Landed: `CReal.ivt_bisect_diag`/`_lo`/`_hi` (the first
reading, `CRealPrelude::ivt_bisect_diag`'s doc comment) as data plus the
concrete reduction test above — deliberately **not** an invariant or
exactness theorem, because none holds. An exact root from this style of
bisection needs an additional hypothesis on `F` (e.g. strict
monotonicity/injectivity, so a converged bracket cannot land away from the
zero set) that the general approximate IVT does not assume; this is the
seventh instance of `docs/mathematics-2026-08/diary-exact-root-obstruction.md`'s
own closing pattern, in the opposite direction — here a computed projection
exists and is exactly what proves the desired theorem FALSE.

---

## Correction: the counterexample already refuted its own proposed fix

The addendum above closes by saying an exact root "needs an extra hypothesis
(e.g. **strict monotonicity**)". **That recommendation is wrong, and its own
counterexample proves it.**

The counterexample runs on `F := id` over `[−1, 2]`. **`id` is already strictly
monotone** — derivative identically `1`, so `k = 0` with uniform bound
`1/(k+1) = 1`. And the diagonal bisection still converges to `1/2` while the
true root is `0`.

So strict monotonicity does **not** rescue `ivt_bisect_diag`. The defect is not
a missing hypothesis on `F` at all — it is **algorithmic**: a stationary
endpoint keeps whatever slack justified its last move, forever, and no property
of `F` repairs a freezing bug in the recursion.

I then repeated that recommendation in a brief, directing a lane to build on
`ivt_bisect_diag_lo/_hi`. The lane checked before building, noticed the
counterexample's own instance was strictly monotone, and said so. **Both the
original recommendation and my repetition of it were refuted by evidence already
sitting in this file.**

The generalisable lesson: **when a refutation closes by proposing a fix, check
whether its own witness already satisfies the proposed hypothesis.** A
counterexample that happens to lie inside the repair's precondition refutes the
repair too, and it is easy to miss because the refuting lane is reasoning about
what went wrong, not about what its instance happens to satisfy.

## What the route actually is

Not the diagonal construction. Instead: the **fixed-slack** `ivt_bisect_lo`/`_hi`
— which already has a proven invariant (`ivt_bisect_invariant`) — run at
independent `(n, K(n))` pairs per accuracy, i.e. exactly `ivt_approx`'s existing
schedule (`bisect_n := M·delta + c`, via `width_le_via_bound`), realised as
**data** rather than through an `Exists`. Those runs are not nested across `n`,
but nesting is not required once a genuine magnitude bound is available.

**The quantitative bound, worked out and confirmed:** for `x ≤ y` in `[a,b]`
with `F' ≥ 1/(k+1)` uniformly, `hd_spec` at accuracy `e := 2k+1` gives
`F y − F x ≥ (1/(2(k+1)))·(y − x)` — the same halving `strict_mono_of_pos_deriv`
already performs internally (`half_frac_eq`). Hence

    |x − y| ≤ 2(k+1)·(|F x| + |F y|) ≤ 2(k+1)·(1/(e+1) + 1/(e'+1))

At `F := id`, `[−1,2]`, `k = 0`, `e = 9`, `e' = 19`: `|x − y| ≤ 0.3` (true value
`0.15`; the general bound reserves half the derivative rate as spec margin).

**So the mathematics works.** Two engineering obstacles remain, both newly
identified:

1. **The global bound is not exposed.** It exists only *mid-proof* inside
   `declare_strict_mono_of_pos_deriv` (`monotone.rs`, ~830 lines), and every
   helper it needs — `half_frac_eq`, `cabs`, `cdiff`, the mesh toolkit — is a
   private `fn` scoped to that file, not `pub(super)`. Reaching it from `ivt.rs`
   means duplicating the whole subdivision argument. **A natural fix is to
   expose the magnitude form as its own declared theorem in `monotone.rs`**,
   which would serve Chapter 12's inverse-function continuity as well.
   *(Resolved — see "Obstacle 1" below; the extraction happened.)*
   <!-- was-absent: CReal.strict_mono_magnitude, CReal.diff_le_of_strict_mono_magnitude -- the magnitude form this bullet says exists only mid-proof; extracted in monotone.rs and consumed by ivt.rs -->
2. **A "continuity transports convergence" lemma does not exist** —
   `Converges f L → UniformlyContinuousOn F … → Converges (F ∘ f) (F L)`.
   Grepped for; absent. Without it, `F(x_n) → 0` does not give `F L ~ 0`.
   *(Resolved in the weakened eventual form — see "Obstacle 2" below.)*
   <!-- was-absent: CReal.converges_comp_eventually -- the repair for this bullet; its own doc comment names this file -->

<!-- Both bullets above are historical. The markers make that machine-checked:
     `scripts/check-absence-claims.py` fails if either declaration is ever
     removed or renamed, so this record cannot quietly start pointing at
     nothing -- and had the markers read `absent:` instead, it would have gone
     red the day the declarations landed. -->


Also worth recording: **`converges_of_cauchy`'s conclusion is itself
existential**, so obtaining `L` as *data* means inlining its own internal
`CReal.mk (speedup (diagonal f) K) …` construction — mirroring `sqrtApprox` —
rather than calling it and projecting. That is the seventh place this kernel's
`Prop`-only `Exists.rec` has dictated a construction's shape.

---

## `converges_comp` as I stated it is FALSE — the modulus has no growth bound

I briefed a lane on "continuity transports convergence":

```text
Converges f L → UniformlyContinuousOn F a b → Converges (fun n => F (f n)) (F L)
```

calling it "a Chapter 5/6 staple". **It is not a theorem here**, and the reason
is a genuine feature of how this development states convergence.

`CReal.Converges f L := ∃ K, ∀ n, Within (seq (f n) n − seq L n) (natDivSucc K n)`
— **a fixed `O(1/n)` rate**, one `K` for all `n`, not eventual convergence.

To invoke `UniformlyContinuousOn.spec` at output accuracy `e`, the required
*input* accuracy is `1/(modulus(e)+1)`. For the output to keep an `O(1/n')`
rate, `e` must grow proportionally to `n'` — but **`modulus` is an arbitrary
`Nat → Nat` and nothing in `UniformlyContinuousOn`'s type bounds its growth.**
Give `F` a √-shaped modulus (`modulus(e) ~ e²`) and composing an `O(1/n)`
sequence through it genuinely converges at `O(1/√n)`. No fixed `K'` exists.

So the classical statement is true and its constructive transcription is not,
because the constructive `Converges` carries a **rate** that the classical
definition does not. That is a sharper failure than the usual constructive
losses: nothing here is undecidable, the theorem is simply about a stronger
conclusion than the hypotheses support.

**Two real repairs, both bounded:**

1. **Weaken the conclusion** to an eventual `∃ N` form. Provable by forward
   evaluation, `N := K·(modulus(e)+1)` — and note the lane's correction to an
   older doc's framing: **no `Nat` division or search is needed**, because
   `modulus` is only ever *evaluated forward*, never inverted.
2. **Bound the modulus**: add a Lipschitz/linear hypothesis
   (`modulus n ≤ c·n + c`) and choose `e` proportional to `n'/(K·c)`.

## What did land

The domain question I asked as an aside turned out to be the answerable part.
**`le a L` and `le L b` ARE derivable** from the pointwise bounds plus
convergence — a limit of points in `[a,b]` does stay in `[a,b]` here — and the
lane proved it rather than asserting it:

- `CReal.converges_lower_bound : ∀ a f L, (∀ n, le a (f n)) → Converges f L → le a L`
- `CReal.converges_upper_bound : ∀ f L b, (∀ n, le (f n) b) → Converges f L → le L b`

by `le_trans`'s "compare at an arbitrary third index" idiom routed through
`f j` — a four-term telescope closed by `Rat.le_of_le_add_nat_div_succ`.

**The pattern, for the fourth time**: a target I named was refuted, and the
refutation came with the true neighbouring statement already built. Briefs that
ask for a verdict *before* building keep converting my wrong targets into right
ones instead of into wasted lanes.

---

## Correction, 2026-08-27: BOTH engineering obstacles were already landed

The "What the route actually is" section above ends by naming two engineering
obstacles and calling the mathematics done. **Neither obstacle exists.** Both
were closed by earlier lanes, and this file was never updated — so a lane was
dispatched to build two things that are already in the kernel, registered, and
under test.

### Obstacle 1 ("the global bound is not exposed") — resolved

The claim was that the magnitude bound "exists only *mid-proof* inside
`declare_strict_mono_of_pos_deriv`" and that reaching it from `ivt.rs` "means
duplicating the whole subdivision argument". It was hoisted out. `monotone.rs`
now declares **three** public theorems on this axis, all with `BuildStep`s in
`creal.rs`, entries in `creal/inventory/monotone.rs`, and axiom footprint 0:

- **`CReal.strict_mono_magnitude`** (`declare_strict_mono_magnitude`,
  `monotone.rs:2883`) — the hoisted bound itself, stated on `le x y` rather
  than `lt x y` because nothing up to this bound needs strictness:

      ∀ F F' a b, HasDerivativeOn F F' a b →
      ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
      ∀ x y, le a x → le x y → le y b →
        le (mul (ofRat (natDivSucc 1 (Nat.succ (Nat.mul 2 k)))) (add y (neg x)))
           (add (F y) (neg (F x)))

  Its own doc comment states it is exactly `strict_mono_of_pos_deriv`'s internal
  `chained2`, and that `strict_mono_of_pos_deriv` is now a corollary of it plus
  the strict-gap-to-rational-witness step. So there is **one** proof of this
  fact, not two — the aliasing hazard this file warns about was avoided.

- **`CReal.diff_le_of_strict_mono_magnitude`**
  (`declare_diff_le_of_strict_mono_magnitude`, `monotone.rs:3815`) — and this is
  the exact statement this diary derived by hand and called the route's
  quantitative core:

      ∀ F F' a b, HasDerivativeOn F F' a b →
      ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
      ∀ x y, le a x → le x y → le y b →
        le (add y (neg x))
           (mul (ofNat (Nat.succ (Nat.succ (Nat.mul 2 k))))
                (add (abs (F x)) (abs (F y))))

  `Nat.succ (Nat.succ (Nat.mul 2 k))` is `2k+2 = 2(k+1)`, so this is literally
  `|x − y| ≤ 2(k+1)·(|F x| + |F y|)` — the bound written out above, cancelled
  through `scale_cancel_le` and the two-term triangle inequality. Its doc
  comment names the two consumers this diary predicted: "This is what an exact
  IVT root needs … and what Chapter 12's inverse-function continuity needs."

- **`CReal.inverse_lipschitz_of_pos_deriv`**
  (`declare_inverse_lipschitz_of_pos_deriv`, `monotone.rs:5980`) — the
  order-free two-sided `abs` form, taking `Apart x y` as data instead of an
  ordering:

      … → ∀ x y, le a x → le x b → le a y → le y b → Apart x y →
        le (abs (add x (neg y)))
           (mul (ofNat (Nat.succ (Nat.succ (Nat.mul 2 k))))
                (abs (add (F x) (neg (F y)))))

  This is precisely the "would also serve Chapter 12's inverse-function
  continuity" the paragraph above speculated about, built.

The private helpers this section worried about — `half_frac_eq`, `cabs`,
`cdiff`, the mesh toolkit — never had to move: the extraction happened **inside
`monotone.rs`**, where they are already in scope, and `ivt.rs` consumes the
result by kernel name (`d.lemma(p.diff_le_of_strict_mono_magnitude, …)`). A
private Rust `fn` scoped to a file is not a barrier to another file at all once
the fact it proves is a *declaration*; only an un-named inline step is. That
distinction is the whole content of obstacle 1, and stating it as "the helpers
are private" pointed the next reader at the wrong thing.

### Obstacle 2 ("continuity transports convergence does not exist") — resolved

`CReal.converges_comp_eventually` (`creal/convergence.rs`, documented at
`creal.rs:1085`, `BuildStep` `convergence::declare_converges_comp_eventually`):

    ∀ F a b (u : UniformlyContinuousOn F a b) f L,
      (∀ n, le a (f n)) → (∀ n, le (f n) b) → Converges f L →
      ∀ e, ∃ N, ∀ n, Nat.le N n → close_within (F (f n)) (F L) (natDivSucc 1 e)

Its doc comment opens by naming this file: "**The repair for
`docs/mathematics-2026-08/diary-exact-root-obstruction.md`'s refuted
`converges_comp`.**" It is repair **(1)** from the section above — weaken the
conclusion to the eventual `∃ N` form — with the witness `N := K·(modulus(e)+1)`
by forward evaluation, no `Nat` division and no search, exactly as that section
predicted. Repair (2) (bound the modulus) was not needed and was not built.

Two consumption notes, since the shape is not what the naive statement would be:

- The conclusion is **`close_within`**, not `Within`. `close_within` is the
  real-valued bound `uc_spec` itself produces; `Within` is the index-tied
  canonical-sample form `Converges` uses. They are different, deliberately, and
  the spec application is a one-step consumer of `close_within`.
- The domain hypotheses `le a L` / `le L b` are **not** separate arguments —
  `converges_lower_bound` / `converges_upper_bound` (landed by the same lane
  that refuted `converges_comp`, recorded above) derive them from the pointwise
  bounds plus `Converges f L`.

And the refutation stands: do not try to strengthen this to the fixed-rate
`Converges (F ∘ f) (F L)`. That statement is false here for the reason this file
gives, and the doc comment repeats it.

### What this cost, and the rule

This is the twenty-first instance this session of a lane being dispatched at
work already in the tree, and the second where **this file itself** was the
authority that sent it. The failure is structural, not careless: a document that
records obstacles accumulates stale ones by construction, and its authority is
exactly what makes them expensive.

The cheap check that would have caught both, and did:

    grep -n 'strict_mono_magnitude\|converges_comp' crates/axeyum-lean-kernel/src/creal.rs

Two seconds, against a brief that budgeted an ~830-line proof extraction and a
new convergence lemma. Note that **`shape_search` could not have answered
obstacle 1** — an inline step has no declaration to index — but it answers it
perfectly *now*, because the step has a name. That asymmetry is the argument for
extracting inline steps eagerly: extraction converts an unsearchable fact into a
searchable one, and the retrieval saving outlives the proof saving.

**So: verify a blocker still exists in the tree before treating it as one —
including, and especially, a blocker this file names.** When a diary section is
acted on, the acting lane should update it in the same commit; the sections
above were each written by a lane that had just learned something and had no
reason to re-read what came before.

## So what actually remains — a composition in `ivt.rs`, and no missing lemma

With both obstacles gone the honest question is what is left. I checked every
piece the route names. **Every one exists and is declared; `ivt.rs` consumes
none of them.**

    grep -n 'strict_mono_magnitude\|diff_le_of\|inverse_lipschitz\|converges_comp' \
      crates/axeyum-lean-kernel/src/creal/ivt.rs
    -> (no output; the positive control is monotone.rs, which has 40+ hits)

That is the whole remaining gap: **wiring, not mathematics.** The route, with
every step named by the declaration that discharges it:

1. **The sequence, as data.** `x n := CReal.ivt_bisect_lo F a b n (K n)`, with
   `K n` the bisection depth. `ivt_bisect_lo` is a `Definition`, so `x` is a
   plain `Nat → CReal` lambda — no `Exists` to project, which is what
   obstruction 1 at the top of this file was about. `K n` is computed by
   `ivt.rs`'s own `width_le_via_bound` (private `fn`, line 1593, already called
   once by `declare_ivt_approx` at line 1881) — in the **same file**, so
   reusable without moving anything.

2. **`F (x n)` is two-sidedly small.** `ivt_bisect_invariant` gives only the
   ONE-sided pair `le (F lo) eps_n` and `le (neg eps_n) (F hi)` — the upper
   bound on `lo` and the lower bound on `hi`, never both on one endpoint. This
   is the step most likely to be mis-planned, so state it explicitly: the
   missing lower bound on `F lo` comes from the **width** plus uniform
   continuity, not from the invariant. `hi − lo ≡ (Q₀−P₀)·(1/2)^k` (the
   invariant's sixth conjunct) is driven under `1/(modulus(e)+1)` by choosing
   `K n`, and `uc_spec` then bounds `|F hi − F lo|`, giving
   `F lo ≥ F hi − small ≥ −eps_n − small`.

   Note what does **not** work here, since it is the tempting move:
   `strict_mono_magnitude` gives `(1/(2k+2))·(hi−lo) ≤ F hi − F lo`, a LOWER
   bound on the gap. Turning that into a lower bound on `F lo` needs an UPPER
   bound on `F hi − F lo`, i.e. an upper bound on `F'` — a hypothesis
   `HasDerivativeOn` does not carry. Uniform continuity is the right source,
   and `ivt_approx` already assumes it.

3. **`x` is Cauchy.** `diff_le_of_strict_mono_magnitude` needs `le x y`, and we
   do not know which of `x n`, `x m` is smaller — `CReal.le` is not decidable.
   The way through is the lattice, not a case split: apply it to the ordered
   pair `(min (x n) (x m), max (x n) (x m))`, which is ordered by
   `min_le_left`/`le_max_left`/`le_trans`, and whose domain hypotheses come
   from `le_min`/`max_le` against the invariant's `le P0 lo` and `le hi Q0`.
   Then `abs_le` closes `|x n − x m| ≤ max − min ≤ (2k+2)·(|F(x n)| + |F(x m)|)`
   — both one-sided halves follow from `x n ≤ max`, `min ≤ x m` and
   `add_le_add`. **No `Apart` is needed**, so this does not want
   `inverse_lipschitz_of_pos_deriv`, whose `Apart x y` hypothesis is exactly
   what a bisection cannot supply.

4. **The limit.** `converges_of_cauchy` — and its conclusion being existential
   is fine here, unlike everywhere else in this file, because the final target
   `∃ c, le a c ∧ le c b ∧ Equiv (F c) zero` is itself a `Prop`. `Exists.rec`
   into `Prop` is allowed; the wall only ever blocked `Type`-valued
   elimination. The domain conjuncts come from `converges_lower_bound` /
   `converges_upper_bound`.

5. **`F L ≡ zero`.** `converges_comp_eventually` at accuracy `e` gives an `N`
   past which `close_within (F (x n)) (F L) (1/(e+1))`; step 2 gives
   `|F (x n)|` small at that same `n`; so `|F L|` is under an arbitrary
   `1/(e+1)`, and `equiv_zero_of_small` converts "smaller than every
   `1/(e+1)`" into `Equiv (F L) zero` outright.

**Assessment.** The route closes on paper with **zero new lemmas outside
`ivt.rs`**, which is a materially different position from what the section
above describes, and it is the direct consequence of the two obstacles having
been resolved without this file noticing. Steps 2 and 3 are the substantial
ones — each is a real estimate assembly comparable to `declare_ivt_approx`
itself — and step 3's lattice detour around undecidable order is the piece
most likely to be re-derived badly, which is why it is written out above.

**What is NOT claimed:** none of this has been through
`Kernel::add_declaration`. It is a route verified by reading every
declaration's statement, not a proof. `cargo check` would not distinguish the
two, and neither does this section — the estimates in steps 2 and 3 are where a
kernel rejection would land, and the `le_congr` direction traps this file's
neighbours document apply throughout.

---

## Resolved, 2026-08-27: `CReal.ivt_exact_root` is in the kernel

The route above closes, one step of it does **not** close as written, and the
whole thing is now a kernel-checked theorem. Six declarations landed in
`creal/ivt.rs`, all with axiom footprint `0`
(`prelude_theorem_inventory --release --include-constructed`,
`every_creal_declaration_is_checked_and_axiom_free`):

```text
creal  CReal.abs_diff_le_of_small_image   0
creal  CReal.ivt_bisect_approx            0
creal  CReal.ivt_bisect_cauchy_bound      0
creal  CReal.cauchy_of_abs_diff_le        0
creal  CReal.ivt_bisect_cauchy            0
creal  CReal.ivt_exact_root               0
```

The headline:

    CReal.ivt_exact_root :
      ∀ F F' a b, HasDerivativeOn F F' a b → UniformlyContinuousOn F a b →
      le a b → le (F a) zero → le zero (F b) →
      ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
      ∃ c, le a c ∧ (le c b ∧ Equiv (F c) zero)

`Equiv (F c) zero` outright — not `|F c| ≤ ε` per accuracy. Read from the
kernel, not from source: `shape_search --include-constructed --name-like
ivt_exact_root` reports `arity=11 … → Exists`.

**It is not vacuous, and that is checked rather than argued.**
`creal_tests::ivt_exact_root_is_inhabited_by_the_identity_on_the_unit_interval`
discharges every hypothesis at `F := fun r => r` on `[0,1]` with `k := 0`
(`hasDerivative_id`, `uniformly_continuous_id`, `zero_lt_one`) and runs
`Kernel::infer` on the closed application. Mutation-verified: swapping the two
interval endpoints makes it a `TypeMismatch`, so the guard fires.

Nothing here decides the sign of a real, and the classical IVT remains
unavailable for the reason this file's top section gives. What unlocks the
exact statement is the extra hypothesis — a uniformly positive derivative —
and the reason is worth stating precisely, because "we assumed our way out"
would be the wrong reading: **the hypothesis does not make any sign decidable,
it makes the root unique with a modulus**, which is what turns a sequence of
approximate roots into a *Cauchy* sequence. The approximate statement
(`ivt_approx`) still needs no derivative and still cannot be strengthened.

### The correction: step 3's lattice route does not close

The section above says the Cauchy step routes through the lattice — apply
`diff_le_of_strict_mono_magnitude` to the ordered pair
`(min (x n) (x m), max (x n) (x m))` and close with `abs_le` — and asserts the
resulting bound is `(2k+2)·(|F(x n)| + |F(x m)|)`. **It is not.** That lemma's
conclusion is

    le (add v (neg u)) (mul (ofNat (2k+2)) (add (abs (F u)) (abs (F v))))

so instantiating at `u := min`, `v := max` puts `abs (F (min x y))` and
`abs (F (max x y))` on the right-hand side, and the hypotheses bound
`abs (F x)` and `abs (F y)`. Recovering the former needs a **lower** bound on
`F (min x y)`, and every bound the interface supplies points the other way:
`min_le_left`, `min_le_right`, and the monotonicity `strict_mono_magnitude`
gives all bound it **above**, by `F x` and by `F y`. A lower bound would need
an upper bound on `F'`, which `HasDerivativeOn` does not carry — *the same
asymmetry this file already identifies one step earlier, for `F lo`*, and the
reason it identifies it there is exactly why it should have been caught here.
The meet-semilattice interface does not entail
`Equiv (min x y) x ∨ Equiv (min x y) y`, which is the case split the detour
existed to avoid, so the missing bound is not derivable from it either.

**Cotransitivity supplies the case split instead**, and without deciding any
order — the same move `ivt_step` already makes one section up. For a target
`x − y ≤ R` and any strictly positive `q`, `lt_cotrans` at the pair
`(zero, q)` evaluated at `x − y` gives `Or (lt zero (x−y)) (lt (x−y) q)`, and
both disjuncts close the goal at slack `q`: the first hands back `le y x`,
which is precisely the ordering `diff_le_of_strict_mono_magnitude` wants — at
the pair whose right-hand side is `|F y| + |F x|`, the two terms the
hypotheses actually bound — and the second gives the goal outright since `R`
is nonnegative. `le_of_forall_le_add_small` then removes the slack, so no
positivity hypothesis on the accuracy is needed anywhere. That is
`CReal.abs_diff_le_of_small_image`, and it needs no `Apart`, which matters
because a bisection cannot produce one.

Everything else the section above says held: `ivt_bisect_lo`/`_hi` as data,
`ivt_bisect_invariant`'s one-sided pairs, `converges_comp_eventually` in its
eventual form, and `converges_of_cauchy`'s existential being fine here because
the final target is a `Prop`. Every `Exists` eliminated in the finished proof
has a `Prop` target; the wall this file records only ever blocked
`Type`-valued elimination, and the data-valued bisection is what keeps the
*sequence* out of that case.

### The gap nobody had named: real bound → `CReal.Cauchy`

The route as written jumps from "`x` is Cauchy" to `converges_of_cauchy`. It
is one lemma short, and the missing lemma is general rather than
IVT-specific. Every estimate here produces a **real** inequality about
`abs (f m − f n)`; `CReal.Cauchy` is stated on the canonical rational
**samples**, `Within (seq (f m) m − seq (f n) n) (K/(m+1) + K/(n+1))`.
Measured before building it: `shape_search --concl CReal.Cauchy` returns nine
theorems and not one takes a `CReal`-level pairwise bound;
`close_within_of_within` and `close_within_of_within_indexed` run the *other*
direction. `riemannSum_cauchy`'s own doc comment records the identical gap for
the integral — "NOT `CReal.Cauchy` in that definition's own canonical-index
shape … separate, unattempted work".

`CReal.cauchy_of_abs_diff_le` closes it, with witness `K+2`:

    ∀ (f : Nat → CReal) (K : Nat),
      (∀ m n, le (abs (add (f m) (neg (f n))))
                 (ofRat (natDivSucc K m + natDivSucc K n))) → Cauchy f

`within_of_two_sided_le` reaches a `Within` at an arbitrary shared index;
`sharedIndexToCanonical` moves to the two canonical ones at the cost of two
regularity legs, leaving

    ((1/(m+1) + 1/(sj+1)) + (qmn + 2/(j+1))) + (1/(sj+1) + 1/(n+1)),  sj = 2j+1

with `j` free. **The choice `j := 3m+2` makes that collapse an equality, not a
chain of widenings**: `Rat.natDivSucc_halve j` turns the two `1/(sj+1)` legs
into exactly `1/(j+1)`, `Rat.natDivSucc_add` fuses that with the `2/(j+1)`
slack into `3/(j+1)`, and `Rat.natDivSucc_scale 2 m` — whose index shape is
literally `(c+1)·m + c` — turns `3/(j+1)` into exactly `1/(m+1)`. The
seven-term bound is therefore *equal* to `(K+2)/(m+1) + (K+1)/(n+1)`, and the
single inequality in the whole proof is `Rat.natDivSucc_le_add_left` raising
the second numerator to the shared witness. The seven-summand rearrangement
goes through `rsum_perm`, which panics on a non-permutation and so fails with
a Rust message naming both lists rather than an opaque `TypeMismatch`.

It is filed in `creal/ivt.rs` because the exact root is what first needed it.
That is the "general infrastructure under its first consumer's module" hazard
`CLAUDE.md` names, logged here deliberately: nothing in its statement or proof
mentions the IVT, and it should be the lemma `riemannSum_cauchy` reaches for.

### What `ivt_approx` was missing, and why it was one refactor not two proofs

The other piece the route needed was `ivt_approx` **without the `Exists`**.
`ivt_approx`'s witness is `ivt_iter`'s existentially-quantified bracket, so
nothing outside that proof can name the point — and a *sequence* of such
points cannot be formed at all, since `∀ e, ∃ x` → `Nat → CReal` is an
`Exists` elimination into a `Type`. `CReal.ivt_bisect_approx` states the
identical bound about the point `ivt_bisect_hi` **computes**, at the depth
`ivt_approx`'s own schedule already chose:

    X e := ivt_bisect_hi F a b (Nat.succ (Nat.mul 2 e)) K,
    K   := (bound (b−a) + 1)·modulus(2e+1) + bound (b−a)

so `fun e => X e` is an ordinary lambda. The estimate is **shared, not
copied**: `declare_ivt_approx`'s closure body and accuracy schedule were
extracted into `approx_endpoint_bound`/`approx_setup`, and both declarations
call them, so the two instantiations of `ivt_bisect_invariant`'s slack cannot
drift apart. `ivt_approx` is unchanged as a statement.

### Three things a re-derivation would get wrong

Kept here because each cost a rejection or nearly did, and none is guessable:

1. **A non-dependent `arrow` for the `UniformlyContinuousOn` argument leaves
   its occurrence free.** `ivt_bisect_approx`'s conclusion mentions `u` —
   the bisection depth reads `ucModulus F a b u` — so the binder must be
   `pi_fv`. The symptom is `UnboundFVar`, which names nothing. `ivt_approx`
   itself gets away with `arrow` because its conclusion does not mention `u`.
2. **A `rat_eq_rewrite` rewriting a subterm takes the SUBTERM as `from`/`to`,
   with the surrounding sum in the motive.** Passing the whole rational while
   the motive also wraps it duplicates the context; the kernel then reports a
   right-hand side with one summand appearing twice, several steps away from
   the line that is wrong.
3. **`converges_comp_eventually` bounds `|F (X n) − F L|` and the triangle
   step needs `|F L − F (X n)|`.** There is no `CReal.abs_neg` or
   `abs_sub_comm`; it is `abs_le` over the two halves, each transported across
   `neg_sub_swap` (the private `abs_diff_symm` in `creal/ivt.rs`).

### What this unblocks, and what it does not

π is now reachable as twice the first zero of `cosFn`, once `cosFn` is
extended past that zero with a positive-derivative certificate on a bracketing
interval — not attempted here. The exact **inverse function** direction that
Chapter 12 wants is the same shape and should follow from `ivt_exact_root`
plus `inverse_lipschitz_of_pos_deriv`.

What is **not** claimed: the approximate IVT still needs no derivative
hypothesis and is still the right statement for a general continuous `F`. This
theorem does not weaken to it and does not supersede it.
