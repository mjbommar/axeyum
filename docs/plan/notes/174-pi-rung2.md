# Notes: 174-pi-rung2

Detail moved out of [`../status/174-pi-rung2.md`](../status/174-pi-rung2.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

## The shifted-series route is NOT the one that works, and the reason is structural

`169-pi.md` proposed re-indexing: apply `alternatingLowerBound` to
`b k := a (k+1)`, whose alternating sum is `T = 1 − cos(8/5)`, and conclude
from `T ≥ 1888/1875 > 1`. That needs `Converges (sumRange t_b) T`, which the
π lane correctly identified as the open work.

**It is worse than open — it is blocked by `Converges`'s own definition.**
`Converges f L := ∃ K, ∀ n, Within (seq (f n) n − seq L n) (K/(n+1))` is a
UNIFORM-rate condition that constrains **every** index including `n = 0`. Any
bridge of the form "`g` is eventually equal to `f`, so `g` converges to `f`'s
limit" therefore has an index-`0` obligation with nothing to discharge it: `g 0`
is arbitrary. Concretely, `sumRange t_b n = t 0 − sumRange t (n+1)` holds for
`n ≥ 1` and fails at `n = 0` (both partial sums are `zero` there, but the
constant-shifted comparison sequence is not). So the naive transfer needs a
bound on `seq (g 0) 0 − seq L 0` with `L` universally quantified, which no
fixed `K` provides.

## What works instead: CLAMP the sequence, do not shift it

    â k := a (Nat.succ (Nat.pred k))

— `a` with its index-`0` value replaced by its index-`1` value. That spelling
is chosen for `ι`, not for elegance: `Nat.pred` is a `Nat.rec` with base `zero`
and step `(j, ih) ↦ j`, so **`â 0 ≡ a 1` and `â (succ j) ≡ a (succ j)` both
hold definitionally**, and every step below is free of index bookkeeping.

- `â` IS globally antitone, by a two-case `Nat.rec` that never uses its own
  induction hypothesis: at `k = 0` both sides reduce to `a 1` (`le_refl`), at
  `k = succ j` the goal reduces to exactly `htail j`. So
  `CReal.alternatingBracketUpper` applies to `â` unchanged.
- `â`'s partial sums differ from `a`'s by the single CONSTANT
  `c := a 1 + neg (a 0)` at every index `≥ 1`
  (`∀ n, Equiv (sumRange t̂ (succ n)) (add (sumRange t (succ n)) c)`, one
  induction: the base is ordinary ring algebra, and the step is free because
  `t̂ (succ j) ≡ t (succ j)`).
- The bracket at base `m := 1` gives `∀ n, le (sumRange t̂ (add n 2)) (Ô 1)`.
  Both sides carry `c`; it cancels (`add_le_add` against `le_refl (neg c)`,
  then `add_assoc`/`add_neg`/`add_zero`), leaving
  `∀ n, le (sumRange t (add n 2)) (sumRange t 3)` — about `a`'s own partial
  sums, whose `Converges` witness is the hypothesis in hand.
- `CReal.converges_upper_bound_shift` at `s := 2` closes `le L (sumRange t 3)`.

**The clamp is why the whole thing stays inside existing machinery.** The
shifted route changes what the series converges to; the clamp does not — it
only changes finitely much of the sequence, and the change is a constant that
cancels.

## `CReal.converges_upper_bound_shift` was hiding place 2

`creal/alternating.rs::declare_alternating_upper_bound`'s doc comment says, in
so many words, "this development has no `converges_upper_bound_shift`", and
then performs the negation route INLINE on its own concrete sequence:
`neg_le_neg` → `converges_neg` → `converges_lower_bound_shift` →
`neg_le_neg` → `double_neg` twice via `le_congr`. That is a general theorem
about an arbitrary `f`, `L`, `b` and shift `s`, written privately for one
caller. Lifting it took ~90 lines and no new mathematics, and both this file's
own second theorem and any future eventual-upper-bound argument now compose
rather than rebuild.

## What is left for rung 2, sized

`alternatingUpperBoundTail` is the *general* half. Instantiating it at cosine
needs four things, none of which this lane built:

1. `a := fun j => mul (expTerm (Nat.add j j)) (pow R (Nat.add j j))` with
   `R := ofRat (natDivSucc 8 4)`, and `hnn` from `exp_term_nonneg` /
   `pow_nonneg`. Cheap.
2. **`htail : ∀ k, le (a (succ (succ k))) (a (succ k))` — the real analytic
   work.** Reduces to `expTerm (m+2) · R² ≤ expTerm m` for `m = 2k+2`, i.e.
   `64 · m! ≤ 25 · (m+2)!` = `25 (m+1)(m+2) m!`, which needs `m ≥ 1` (at
   `m = 0` it is `64 ≤ 50`, false) and holds with room from `m = 2` on. Needs
   `Nat.factorial_succ` and a symbolic-in-`k` `Rat` cross-multiplication. There
   is no `expTerm`-scaled antitonicity lemma in the tree; `expTerm_antitone` is
   the unscaled one.
3. `Converges (sumRange t) (cosFnWide R)`: `cosFnWideUniformConverges`'s
   `.spec` at the point `x := R` (needs `le zero R` and `le R R`), then
   `sumRange_congr` for the `mul_assoc` reassociation
   `cosFnTerm k R = mul (mul (pow (neg one) k) (expTerm (k+k))) (pow R (k+k))`
   into `t k = mul (pow (neg one) k) (a k)`, then a `Converges`-transfer across
   a pointwise `Equiv` — which, unlike the shifted-series case, is safe,
   because the `Equiv` holds at EVERY index including `0`, so
   `converges_of_close` at `Kc := 2` applies uniformly.
4. The numeric evaluation `le (sumRange t 3) zero`, i.e.
   `a 0 − a 1 + a 2 = −13/1875 ≤ 0`. This is where `169-pi.md`'s measured
   `Nat.mul` budget binds: reduce to the common denominator `1875` BEFORE
   adding (largest product `32 · 1875 = 60,000`, ~0.5 s, needs
   `on_a_deep_stack`), never letting `normalize_add_normalize` combine first
   (`88,500,000`, out of reach).

Item 2 is the one to size a lane against; items 1, 3 and 4 are mechanical
given it.

## What the kernel rejected

**Nothing.** Both declarations were accepted on their first
`add_declaration`, and neither needed `on_a_deep_stack`. The four kernel
facts the brief warned about were all avoided rather than survived, and it is
worth saying which and how, because the avoidance was deliberate:

- **`UnboundFVar` / `pi_fv` vs `d.arrow`.** Neither theorem's conclusion
  mentions a *hypothesis* variable, only the value variables `s`/`f`/`L`/`b`
  and `a`/`L`. So the two proof hypotheses bind with `d.arrow` and every value
  binds with `d.pi_fv` — the split is forced by the statement, not guessed, and
  no free-variable scan was needed.
- **`neg (neg x)` is not defeq to `x`.** `converges_upper_bound_shift` hits it
  twice (both `L` and `b` come back doubly negated) and closes each with
  `trig.rs`'s `pub(super) double_neg` rather than hoping. Note
  `creal/alternating.rs` carries a *second, private copy* of `double_neg`
  beside `trig.rs`'s public one — two proofs of one fact already in the tree.
- **Concrete vs symbolic witnesses.** Everything here is built over bound
  variables; the only concrete `Nat`s are the numerals `0`, `1`, `2`, `3` in
  the clamp and the shift, and each is a *literal index*, never an
  accumulator that partially evaluates against a symbolic one.
- **`Nat.add` recurses right.** Used deliberately, not merely respected: the
  bracket's index arithmetic is reused verbatim from `alternating.rs`'s own
  `direct_hyp` shape, and `add n 2 ≡ succ (succ n)` is exactly why the
  `∀ n, le (sumRange t (add n 2)) …` hypothesis
  `converges_upper_bound_shift` wants is defeq to the `succ (succ n)` form
  the proof produces, with no `Nat` rewriting at all.

## Verification

Foreground, this worktree, `env -u RUST_MIN_STACK` not needed (no
`RUST_MIN_STACK` was ever set in this lane's shell):

- `cargo test -p axeyum-lean-kernel --lib creal::creal_tests::creal_prelude_builds`
  — **95.38 s green** after `converges_upper_bound_shift`, **95.28 s green**
  after `alternatingUpperBoundTail`. The second theorem costs **no measurable
  prelude-build time**; both numbers sit inside `169-pi.md`'s own 91–117 s
  band, so neither is evidence of a slowdown and neither is evidence against
  one.
- `cargo test --release … creal::creal_tests::every_creal_declaration_is_checked_and_axiom_free`
  — **1 passed, 17.30 s**. Environment-derived, both directions: both new
  declarations are present, `Theorem`-kind, and carry an **empty**
  `axiom_footprint`.
- The new statement pin,
  `the_eventual_upper_bound_and_the_tail_leibniz_bound_state_what_pi_rung_2_needs`
  — **1 passed (nonzero), 14.18 s** in `--release`. Interned-id equality, never
  `def_eq`, with each negative control differing in a SMALL term (one
  transposed `le`; `sumRange t 2` for `sumRange t 3`) and each control asserted
  non-vacuous before use.
- **Mutation-verified**: changing the pin's expected conclusion from
  `sumRange t 3` to `sumRange t 4` fails that test and only that test, on the
  `assert_eq!` that names the statement — so the pin is load-bearing rather
  than decorative.
- `cargo check -p axeyum-lean-kernel --lib --tests`: clean, no warnings.
- `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings`:
  green.

**PLAN.md was deliberately not regenerated** (the lane brief says not to touch
it); the coordinator's regeneration will pick this file up.

## Archived landed-changes rows

| 2026-08-27 | pi-rung2 | the route that works is a CLAMP, `a_hat k := a (succ (pred k))`: `Nat.pred` is a `Nat.rec` with step `(j, ih) -> j`, so `a_hat 0` and `a_hat (succ j)` both reduce by iota alone, `a_hat` is globally antitone by a two-case `Nat.rec` that ignores its own IH, and `a_hat`'s partial sums differ from `a`'s by ONE constant `c := a 1 - a 0` at every index `>= 1`, which cancels off both sides of the bracket |
| 2026-08-27 | pi-rung2 | arithmetic re-verified independently: `a 1 - a 2 = 1888/1875`, margin `13/1875`; equivalently `O 1 = 1 - 32/25 + 512/1875 = -13/1875 < 0`, the same margin read off `a`'s OWN partial sums rather than a shifted limit |
| 2026-08-27 | pi-rung2 | test: both statements pinned structurally against interned ids (never `def_eq`), each negative control differing in a SMALL term -- one transposed `le`, and `sumRange t 2` for `sumRange t 3` (the EVEN partial sum `E 1`, a LOWER bound, so the substitution is exactly the wrong-direction bug) -- and each control asserted non-vacuous before use. Mutation-verified: `sumRange t 4` for `sumRange t 3` kills that test and only that test |
| 2026-08-27 | pi-rung2 | measured: the kernel rejected NOTHING in this lane, and no `on_a_deep_stack` was needed. `creal_prelude_builds` 95.38 s then 95.28 s -- `alternatingUpperBoundTail` costs no measurable prelude-build time; `every_creal_declaration_is_checked_and_axiom_free` green in `--release` (17.30 s), both new declarations `Theorem`-kind with an EMPTY axiom footprint |
| 2026-08-27 | pi-rung2 | sized: rung 2's remaining blocker is ONE lemma, `htail : forall k, le (a (succ (succ k))) (a (succ k))` for `a j := expTerm (2j) * R^(2j)`. It reduces to `64 * m! <= 25 * (m+2)!` for `m = 2k+2`, false at `m = 0` and true with room from `m = 2`; needs `Nat.factorial_succ` and a symbolic `Rat` cross-multiplication. No `expTerm`-scaled antitonicity exists (`expTerm_antitone` is the unscaled one) |
