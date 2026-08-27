# The `integral_split` gap register — two prerequisites four sizings missed

Status: **`CReal.integral_split` is PROVED** (seventeenth lane, 2026-08-27),
admitted axiom-free and registered in the prelude. Both gaps below were closed
by the sixteenth lane; the seventeenth found no further gap. Kept as the record
of how the gaps were found, what was wrong about the first characterisation,
and — in the closing section — what the four sizings got wrong about the
*remaining* work, which is a separate and more interesting error.

## Why this file exists

The active goal is: *any time there is a deficiency or gap, log it and launch an
Opus lane against it.* This is that log. It is deliberately a **register** rather
than a one-off note — `CReal.integral_split` has now absorbed fifteen lanes, and
the pattern that keeps repeating is that a gap gets found, gets fixed by
reslicing, and the *next* gap underneath it was never written down. Append here.

## What is actually landed

Reslicing `integral_split` into individually-verified pieces worked. These are in
the kernel and checked:

`mesh_count_align`, `bnd_leg_plus_share_le_at`, `riemannSum_split_exact`,
`riemannSum_split_exact_of_uc`, `riemannSum_split_scale_invariant`,
`close_within_of_within_indexed`, `riemannSum_sharedAccuracyClose_at`,
`uniformlyContinuousOn_restrict`.

The fifteenth lane then declined to assemble `integral_split` from them, on the
grounds that two prerequisites do not exist. **That refusal was correct** and is
the reason the gaps are known at all — eleven earlier lanes attacked the whole
theorem and produced no characterisation of why it failed.

## Gap A — CLOSED. The alignment was midpoint-only, and worse than described

`mesh_count_align` pads with `depth_ac := depth_cb := deep_ab + big_n`, which is
**additive**. The fifteenth lane measured the resulting split ratio drifting to
1:1 and concluded the stratum was bisection-only.

**Its ratio formula was off by one, and correcting it makes the finding
stronger.** `delta_of a b m` is `(b−a)/(m+1)`, so the split fraction is
`succ(m_ac)/(combined+1) = n_ac/(n_ac+n_cb)`, not `succ(m_ac)/combined`.
Corrected, with `deep_ac = deep_cb` the ratio is **exactly 0.5 at every `big_n`,
including 0** — not a sequence converging to it. Asymmetric deeps drift toward
it (0.2857 → 0.4118 → 0.4860 → 0.49985 → 0.4999985).

And the decisive fact is structural, not numeric: **`mesh_count_align` takes no
ratio argument at all** — its parameters are three uniform-continuity moduli plus
`big_n` — so no choice of arguments reaches a non-midpoint split.

### The fix, and what it says about the retraction below

`mesh_count_align_mul` (commit `40eb61c1c`) scales both counts through
`succ_mul_succ` at a common `succ k`, which cancels out of the ratio
identically, giving
`succ(m_ac)/(combined+1) = succ(m_ac0)/(succ(m_ac0)+succ(m_cb0))` for every `k`.
Verified numerically first — 40 of 40 (base ratio, k) pairs exactly equal for k
up to 1e6 — then kernel-verified four ways, including **both child thresholds**
(which `mesh_count_align` never had to prove) and a **negative control asserting
the additive counts FAIL that identity at 1:5**. The threshold inequality had
0 counterexamples in 200,000 draws, against 1,435 in 20,000 for a deliberately
weakened `k`, so the check is not vacuous.

Uses no `Nat.sub`. Two sub-helpers were needed: `nat_le_add_left` (the prelude
carries `le_add_right` only) and `le_dest_elim`.

### Correction to the correction

An earlier revision of this file recorded that the coordinator's claim of
*"every rational proportion"* was **wrong**. That retraction went too far in the
other direction, and the record should be precise:

- **Wrong about the lemma.** `mesh_count_align` as landed is midpoint-only and
  cannot be argued into anything else.
- **Right about the goal.** Every rational proportion *is* reachable — through
  multiplicative scaling, which is what `mesh_count_align_mul` now provides.

**Bisection-only is NOT the honest stratum.** The only in-tree overstatement was
`creal/integral.rs`'s own module doc, corrected in place by the closing lane.

## Gap B — CLOSED, and the impossibility argument was false

Gap B is **load-bearing**: it is not avoidable by sharing one `ExprId`, for a
reason the coordinator's suggested shortcut could not have anticipated. The split
point `c_k` is *derived from* `m_ac`/`m_cb` — the very counts that must grow
without bound — so it is a fresh `Nat` arithmetic expression at every accuracy
and there is nowhere to put a shared literal.

**But it was the wrong lemma.** Naming the three legs shows the two *integrals*
are never compared at all: `riemann_sum_integral_close` already relates the
caller's `c`-integrals to `c`-Riemann **sums**, and the only mismatch is
`riemannSum F a c_k m_ac` against `riemannSum F a c m_ac`. That is a
`riemannSum` fact, not the `integral_congr_endpoint` that was sized.

The fifteenth lane's argument that this was impossible in principle — because
`sample x n` is rational while `Equiv` reals agree only in the limit — rules out
proving it **sample by sample**, which nothing requires. `riemannSum` is
`sumRange` of `mul (F (add x (mul (ofNat i) Δ))) Δ`, so the congruence follows
from the setoid's own lemmas with `sample` appearing nowhere.

`riemann_sum_congr_endpoints` (commit `e18799228`) is that proof, kernel-accepted
on the first attempt:

    ∀ F aa bb, UniformlyContinuousOn F aa bb → ∀ x y x2 y2 m,
      le x y → le x2 y2 → le aa x → le y bb → le aa x2 → le y2 bb →
      Equiv x x2 → Equiv y y2 →
      Equiv (riemannSum F x y m) (riemannSum F x2 y2 m)

Every step names an existing lemma. **Gap A is a prerequisite for Gap B**:
`riemann_sum_split_scale_invariant` gives `Equiv c_k c_0` only for the
`succ_mul_succ` family. `split_identity_at_equiv_point` (commit `8a6bacfb2`)
builds the join rather than asserting it.

### The one kernel rejection, and what it teaches

`riemann_sum_congr_endpoints` takes the **outer interval its witness is about**
separately from the endpoints being moved. The `[c_k,b]` leg was given
`(c_k,b)` as the outer interval, but `u` witnesses continuity on `[a,b]` and
nothing else — **both legs take `(a,b)`**. The message was a bare `TypeMismatch`
between two `ExprId`s naming neither `u` nor `c_k`, indistinguishable from a
transposed endpoint pair. The `[a,c_k]` leg was correct from the start, which is
exactly why a both-endpoints helper needs a caller test exercising **both**
directions — a one-directional test would have stayed green.

## What remains: `integral_split` did NOT close

No further gap appeared. What is left is exactly the twelfth lane's estimated
volume, and **both named prerequisites are now landed and kernel-checked**:
three `riemann_sum_integral_close` legs, `close_within_of_within_indexed` and
`bnd_leg_plus_share_le_at` per leg, `abs_add_le` twice, `equiv_zero_of_small` to
close, with `big_n` and `e_inner` as functions of `e`.

Prelude build: 31.58 s at merge → 32.66 s isolated final, band 29–39 s, no
movement. (A 35.93 s reading came from a batched run; the isolated
re-measurement is the one to quote — a lesson worth keeping, since a contended
reading looks exactly like a regression.)

## Standing note on the dead-code warnings

Dead-code warnings went from **2 to 7**, and the closing lane added no
`#[allow]`: `mesh_count_align`, `bnd_leg_plus_share_le_at`,
`mesh_count_align_mul`, `riemann_sum_congr_endpoints`,
`split_identity_at_equiv_point`, `nat_le_add_left`, `le_dest_elim`,
`MeshAlignMul`. They carry dead-code warnings because nothing consumes them. **That is the honest signal and must not
be silenced with `#[allow]`.** The fifteenth lane deliberately declined to wire
them into an unverified assembly, on the grounds that doing so would ship a
checker that cannot fail. Wiring them into a *verified* declaration is the only
acceptable fix.

**Resolved to 4 by the seventeenth lane, and the residue is the finding.** See
the closing section.

## The close — SEVENTEENTH lane, 2026-08-27: proved, and no seventeenth gap

`CReal.integral_split` is admitted, axiom-free, and in `EXPECTED_STEP_ORDER`:

```text
∀ F a b (m_ac0 m_cb0 : Nat) (hab : le a b) (u : UniformlyContinuousOn F a b)
  (hac : le a c) (hcb : le c b)
  (uac : UniformlyContinuousOn F a c) (ucb : UniformlyContinuousOn F c b),
    Equiv (integral F a b hab u)
          (add (integral F a c hac uac) (integral F c b hcb ucb))
  where c := add a (mul (ofNat (succ m_ac0))
                        (delta_of a b (add (succ m_ac0) m_cb0)))
```

Kernel-accepted symbolically in every one of those, **on the first attempt**,
with zero rejections in the whole lane.

### The remaining volume was an estimate of a different proof

Four sizings (tenth, twelfth, fifteenth, sixteenth) agreed on what was left:
three `riemann_sum_integral_close` legs, `close_within_of_within_indexed` and
`bnd_leg_plus_share_le_at` per leg, `abs_add_le` twice, `equiv_zero_of_small`
to close, `big_n`/`e_inner` as explicit functions of `e`. **Not one of those
five lemmas is in the proof.** They size a route that builds a three-way
triangle inequality on `abs` by hand.

`declare_integral_add` and `declare_integral_le` already show the shorter one:
once every leg is a `Converges` fact at a shared mesh family, the combine is
three named lemmas and no `abs` estimate is done at this level at all.

```text
conv_ab/ac/cb  leg_converges, three times
conv_sum       converges_add
cross          split_identity_at_equiv_point APPLIED at n -- `CReal.Equiv x y`
               IS `∀ n, Within (seq x n − seq y n) (2/(n+1))`, so the split
               identity at n is already `converges_of_close`'s hypothesis;
               the same step `declare_converges_of_equiv` takes
step           converges_of_close at Kc := 2
final          converges_unique
```

The whole rational estimate collapses into one private helper,
`leg_converges`, which is `declare_integral_le`'s own `step_f` plus exactly two
things: `riemann_sum_shared_accuracy_close` at a **free** `k1` (so the leg
reaches the caller's mesh rather than `common_refinement`'s), and
`Rat.natDivSucc_antitone` at `Nat.le n l` (reconciling that lemma's
`modulus(l, shift n)` leaf with `bnd_leg_plus_share_le`'s `modulus(n, shift n)`
shape).

Generalizing the mistake: **a sizing derived from the shape of the obstruction
is not a sizing of the cheapest proof.** Every one of the four estimates was
produced by staring at what `riemann_sum_integral_close` hands you and asking
how to combine three of them. None asked which *existing declaration in the
same file* already combines two integrals, which is `integral_add`, twenty
lines of lemma applications.

### Two parameters that turned out not to be free

- **`c` is not universally quantified.** Gap B's entry already said why —
  `riemann_sum_split_scale_invariant` gives `Equiv c_k c_0` for the
  `succ_mul_succ` family and no other — but this is where it becomes a
  signature. `c` is the base split point of the caller's proportion
  `succ m_ac0 : succ m_cb0`. Every rational proportion is reachable, and the
  test asserts the transposed proportion yields a *different* `CReal`, so the
  reachable stratum is demonstrably not bisection-only.
- **`big_n := n`.** `leg_converges` needs `Nat.le n (M n)` per leg for the
  antitone step, and the scale factor is
  `((deep_ab + deep_ac) + deep_cb) + big_n`. The twelfth lane's plan left
  `big_n` free "to be driven to infinity against `e`"; nothing drives it.

### Dead code 7 → 4, and the residue is the measurement

Consumed by the verified declaration: `riemann_sum_congr_endpoints`,
`split_identity_at_equiv_point`, `nat_le_add_left`, `le_dest_elim`.

Still unconsumed, still not `#[allow]`-ed:

| helper | why the shipped proof does not need it |
| --- | --- |
| `mesh_count_align` | additive predecessor, superseded by `mesh_count_align_mul` |
| `MeshAlignMul`, `mesh_count_align_mul` | the CPS form. `leg_converges` runs its own `le_dest_elim` per leg and needs the `Nat.le` facts as plain terms, so the scaling argument was factored into a new non-CPS `mesh_count_align_mul_bounds` and the CPS wrapper now calls it |
| `bnd_leg_plus_share_le_at` | the independent-index variant. This route runs every index at `n`, so the same-index `bnd_leg_plus_share_le` suffices |

Those three rows are exactly the distance between the sized proof and the
shipped one. `bnd_leg_plus_share_le_at` in particular was built *because* the
twelfth lane's plan called for it once per leg at independent accuracies.

### Cost

Matched A/B on one tree, the declaration disabled and re-enabled between
readings, `creal_prelude_builds` isolated:

| load | without | with |
| --- | --- | --- |
| ≈18.7 | 42.82 s | 78.00 s |
| ≈10.9 | — | 46.53 s |
| ≈8.4 | **31.55 s** | — |
| ≈4.6 | — | **39.70 s** |

The box was carrying 5–19 load throughout (two sibling `axeyum-cas` test
binaries at ~450 % CPU each), so no reading here is isolated in the sense the
band was set in. The bottom pair is the closest matched one and the `with`
reading was taken at the *lower* load, so **+8 s is a floor; +8 to +15 s is the
honest range**, putting the gate at the top edge of its 29–39 s band.

Bisected as this file's own guidance requires: a `leg_converges` at a SIMPLE
mesh family (`deep(n) + n`) costs **0.3 s** over the bare prelude. So the cost
is not the estimate machinery — it is the size of the aligned mesh terms
(`succ_mul_succ` over three `deep_at` moduli) that all three legs and the cross
are stated at. **No `CReal.integral` `Definition` is unfolded anywhere**: every
`integral` is one shared `const_app` on both sides of every step, which is the
discipline `riemannSum_integral_close`'s own 74 s incident established.

## Piece 1 — LANDED conditionally, NINETEENTH lane, 2026-08-27

The eighteenth lane named two missing pieces. Piece 1 (the close-endpoint
estimate) is now built and kernel-verified, in three increments, **under three
explicit hypotheses** — one of which is the residual gap. Piece 2 was not
attempted and its analysis is unchanged.

### Absence re-verified a third time

`/usr/bin/grep -rniE 'endpoint.*(le|bound|estimate|close)|(le|bound|estimate|
close).*endpoint'` over every `creal/*.rs`: only prose (module docs, test
comments), zero declarations, against **21** hits for
`riemann_sum_congr_endpoints` as the same-shape positive control. The third
check cost one command and confirmed the eighteenth lane's finding.

### The shorter route existed AGAIN — and the level matters

The register's own closing lesson pays a third time, but only when the
question is asked at the right LEVEL. Asked about *integrals*, "which
declaration already relates two of these under a bound?" finds nothing: the
endpoint estimate is genuinely a `riemannSum` fact and there is no way around
it. Asked about **finite sums** it finds `CReal.sumRange_const`
(`Equiv (sumRange (fun _ => w) (succ m)) (mul (ofNat (succ m)) w)`), which
turns a uniform per-term bound into `(succ m)·K` in ONE lemma application and
deletes the induction the eighteenth lane's sizing implied.

`shape_search` (ADR-0608) found it in one query and earned its keep twice
more: `--concl CReal.le --const CReal.riemannSum` returns exactly two rows,
both same-endpoint — the negative result piece 1 rests on — and `--ns CReal
--name-like abs` surfaced `CReal.abs_mul_le_of_bounds`, `derivative.rs`'s
product-rule lemma, which turns out to be the entire analytic content of the
per-term estimate. Note the prebuilt binary in the SHARED checkout's
`target/release/examples/` was stale (it lacks `integral_abs_le`, landed
hours earlier), which does not affect a query about older declarations but
would silently produce a false ABSENT for a recent one.

### The three increments

1. `sum_range_pair_diff_le` — SUM level, no `riemannSum`/mesh/modulus.
2. `product_pair_diff_le` — PER-TERM, purely algebraic on four bare factors.
3. `riemann_sum_endpoints_le` — the assembly, stated at the `rsum` type.

Exact statements are in `creal/integral.rs`'s module documentation.

### The residual gap is ONE index-arithmetic chain

`riemann_sum_endpoints_le` takes `dd` (a bound on `|Δ₁ − Δ₂|`), `d2b` (a
bound on `|Δ₂|`) and — the one that matters — a per-index hypothesis that
`|p_i − p'_i|` is inside the modulus at accuracy `e`. The first two are cheap
for a caller. The third is not: `p_i − p'_i = (x − x₂) + i·(Δ₁ − Δ₂)`, so
bounding it uniformly in `i` needs `i ≤ m` carried through `CReal.ofNat_le`
and `CReal.meshReciprocalMul` (Rust field `mesh_reciprocal_mul` -- the two
spellings differ, which is exactly the retrieval hazard `shape_search
--name-like` exists for) to turn `i·|Δ₁−Δ₂|` into `|w₁ − w₂|`. Both
lemmas exist; the chain was not built.

**So piece 1 is a CONDITIONAL estimate, and calling it "piece 1 landed"
without that qualifier would be the overstatement this register exists to
prevent.** The analytic content is all kernel-checked; what remains is
arithmetic over existing lemmas.

### Piece 2 unchanged, and piece 1 does not move it

Every hypothesis in `riemann_sum_endpoints_le` is about `[x,y]` versus
`[x₂,y₂]` at a FIXED mesh count. None of them constructs a split point. The
`PosBound`-on-the-width obstruction stands exactly as the eighteenth lane
stated it, and the next stratum remains **`integral_split` at arbitrary `c`
GIVEN a `PosBound` on the interval width** — not a universally quantified
`c`.

### Dead code 4 → 8, none silenced

Six new private helpers, each with
`#[cfg_attr(not(test), expect(dead_code, reason = "…"))]` naming its own
specific future consumer. No prelude declaration was added.

### Cost: none — and a SINGLE PAIR would have said +5 s

Matched A/B on one tree, `integral.rs` swapped to its pre-lane content and
back (restore verified byte-identical with `cmp`), `creal_prelude_builds`
isolated:

| tree | end load | reading |
| --- | --- | --- |
| WITHOUT | 2.69 | 36.10 s |
| WITHOUT | 4.88 | 40.32 s |
| WITH | 4.10 | 41.91 s |
| WITH | 4.44 | 41.18 s |

The first pair taken (36.10 / 41.18) reads as **+5 s**, and it is an artifact
of load: the `WITHOUT` run landed at 2.69 and the `WITH` runs at 4.1–4.4. A
second `WITHOUT` reading at 4.88 gives 40.32 s against 41.18 s `WITH` at
4.44 — 0.86 s. **Read the pair at matched load, not the pair you took
first**; this register has recorded the same trap before from the other
direction (a batched run reading 35.93 s).

The decisive check is structural, not a timing: `git diff` against this
lane's base over `creal.rs`, `creal_tests.rs`, `inventory.rs` and
`inventory/` is **empty**, so both sides build the identical environment and
any difference could only have been the harness.

### A FAILING `def_eq` between two `riemannSum`s is PATHOLOGICAL

New entry in this register's failure list, and it cost the only wasted run of
the lane. `riemann_sum_endpoints_le`'s first negative control transposed the
two `riemannSum`s in the CONCLUSION and asserted `!Kernel::def_eq` on the two
`abs` terms beforehand for non-vacuity. Both are FAILING defeq checks between
`riemannSum`s at different endpoints, so the kernel must unfold both
`Definition`s — `sumRange`'s `Nat.rec` over a symbolic `succ m`, `delta_of`
inside — before it can conclude they differ.

Measured: **> 300 s with RSS climbing 2.0 → 3.1 GB and no sign of stopping**,
against **34.9 s** for the positive check on the identical proof term. A
succeeding defeq stops at the first shared head; a failing one has no such
stopping rule. Same family as this file's own 74 s incident, arriving through
a test rather than a declaration.

Replaced, not investigated, per the standing rule. The control now varies
**only the term count in the bound** (`mul (ofNat m) kb`) and leaves the
left-hand side the identical `ExprId`: equally discriminating (false at
`m := 0`, where the sum has one term and the claimed bound is `0`) and free —
both tests together run in 34.45 s. Non-vacuity is asserted STRUCTURALLY with
`assert_ne!` on the two hash-consed `riemannSum` ids.

**The rule to carry: a negative control must differ in a SMALL term.** If the
two conclusions differ deep inside a `Definition`-heavy subterm, the refusal
you are testing for is a defeq search, and it can cost more than the proof.

### What the kernel rejected

Once, in the first increment, and it is a family this register has not
recorded before: a **SORT** error wearing a `TypeMismatch`'s clothes. The
constant function fed to `sumRange` was built with a `CReal` binder instead
of `Nat`, and the kernel printed
`TypeMismatch { expected: ExprId(3), got: ExprId(1503219) }` — an
unrenderable low id naming neither the lambda nor `sumRange`, and at a glance
indistinguishable from this file's usual `le_congr` direction bugs. **The
tell is the tiny `expected` id**: a sort lives at a single-digit `ExprId`; a
real term does not.

That same run also produced a control lesson worth keeping: the NEGATIVE
control PASSED while the positive was rejected. A refusal proves nothing
until the acceptance is green beside it, so the later increments build both
probes in ONE function and assert both outcomes together.
