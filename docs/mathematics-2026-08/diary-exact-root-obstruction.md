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
2. **A "continuity transports convergence" lemma does not exist** —
   `Converges f L → UniformlyContinuousOn F … → Converges (F ∘ f) (F L)`.
   Grepped for; absent. Without it, `F(x_n) → 0` does not give `F L ~ 0`.

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
