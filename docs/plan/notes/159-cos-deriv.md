# Notes: 159-cos-deriv

Detail moved out of [`../status/159-cos-deriv.md`](../status/159-cos-deriv.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**What that unblocked, and what landed instead.** The classical fix routes
(A) through a mean value estimate on the tail. That estimate did not exist —
but `creal/monotone.rs`'s `monotone_of_nonneg_deriv` already owns the whole
subdivide-and-telescope construction, so the mean value INEQUALITY is that
theorem applied twice rather than a new analytic development. Landed,
kernel-accepted on the first attempt, axiom-free:

    CReal.abs_diff_le_of_deriv_bound :
      ∀ F F' a b, HasDerivativeOn F F' a b →
      ∀ M, (∀ z, le a z → le z b → le (abs (F' z)) M) →
      ∀ x y, le a x → le x y → le y b →
      le (abs (add (F y) (neg (F x)))) (mul M (add y (neg x)))

**Remaining work to reach the target**, sized against what now exists:

1. `∀ n, HasDerivativeOn Sₙ Sₙ' 0 (8/5)` for cosine's partial sums — an
   induction over `hasDerivative_add`, with a per-term witness from
   `hasDerivative_pow` + `hasDerivative_smul` + `hasDerivative_congr`. Needs
   the two Skolem `BoundedOn` functions `hasDerivative_pow` demands, and the
   **index-shifted** coefficient identity `cosTerm (j+1) · (2j+2) ~ −sinTerm j`
   (`cosFnTerm k x = cosTerm k · x^(k+k)`, `sinFnTerm k x = sinTerm k ·
   x^(k+k+1)`, so `d/dx Σ_{k<n+1} cosFnTerm k = −Σ_{k<n} sinFnTerm k`).
2. The general uniform-limit-of-derivatives theorem, now unblocked: modulus
   `m(e) := m_{n(e)}(3e+2)` with `n(e)` read off the derivative series' own
   `UniformConvergesOn.rate`, a three-way `1/(3e+3)` accuracy split of exactly
   the shape `hasDerivative_mul` already performs, `abs_diff_le_of_deriv_bound`
   on the tail `Sₖ − Sₙ`, and `le_of_forall_le_add_small` to remove the `k → ∞`
   slack. Comparable in size to `hasDerivative_mul` (~1,000 lines).
3. `hasDerivative_congr` to move from the `succ n`-indexed partial sums to
   `cosFnWide`/`neg ∘ sinFn` as named.

Each is a lane on its own; step 2 is the one that was blocked and no longer is.

**Timings** (this host, load 2–4): `creal_prelude_builds` **93.97 s** with the
new declaration against **95.05 s** for the same tree with the five files
reverted to the parent commit — a matched A/B in one target directory, restore
verified byte-identical. No measurable cost.
`every_creal_declaration_is_checked_and_axiom_free` (`--release`) 16.63 s, green.

**Kernel rejections: none.** `add_declaration` accepted the proof term on the
first attempt. The only friction was tooling (`sed`/heredoc calls refused by
the worktree-isolation guard).
