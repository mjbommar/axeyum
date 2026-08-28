# Lane 159 — `HasDerivativeOn cosFnWide (fun x => neg (sinFn x))`

<!-- plan-section: lane-status -->

**Status: PARTIAL — the keystone landed, the target did not, and the gap is
now precisely sized.** 2026-08-27.

The target itself is NOT landed and nothing here should be read as implying
π. What landed is the one missing analytic fact standing under it.

**The searched question, answered.** A "uniform limit of derivatives" theorem
is **genuinely absent** from this development. Measured against a FRESH
`shape_search` index (`declarations=1889`, matching the current tree, so the
stale-prebuilt false-ABSENT hazard does not apply):

- `--concl CReal.HasDerivativeOn` → **FOUND 16**, and all sixteen are
  pointwise combinators (`mk`, `const`, `id`, `sq`, `neg`, `add`, `sub`,
  `smul`, `mul`, `pow`, `pow_two`, `cube`, `chain`, `chain_id_sq`, `congr`,
  `integral_const`). Not one takes a limit hypothesis.
- `--concl CReal.HasDerivativeOn --hyp CReal.UniformConvergesOn` → **ABSENT**
  (exit 1, positive control `any-kind=1889 ns CReal=512`).
- `--hyp CReal.UniformConvergesOn` → **FOUND 5**: `.rate`, `.rec`, `.spec`,
  `uniform_converges_add`, and `uniform_limit_uniformly_continuous`. The
  last is the ONLY theorem in the tree that transports any property at all
  through a uniform limit.

**The finite-partial-sum route does not avoid the interchange.** Writing `Sₙ`
for a partial sum and `F` for its uniform limit, the standard split is
`(A) |(F y − F x) − (Sₙ y − Sₙ x)| + (B) |(Sₙ y − Sₙ x) − Sₙ'(x)(y−x)| +
(C) |Sₙ'(x) − F'(x)|·|y−x|`. (B) is each partial sum's own `spec`; (C) is
uniform convergence of the derivative series, which `sinFnUniformConverges`
already supplies. (A) is bounded by uniform convergence of the FUNCTIONS only
by a **constant** `2δₙ`, while `deriv_spec_body`'s budget is
`(1/(e+1))·|y − x|` quantified over every `y` within `1/(m e + 1)` of `x` —
including points arbitrarily close to it. No `n` absorbs a constant into an
`ε·|y − x|` budget, so the interchange is required by the shape of the spec,
not by how the limit happens to be taken.

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

<!-- plan-section: landed-changes -->

| 2026-08-27 | cos-deriv | `CReal.abs_diff_le_of_deriv_bound` -- mean value inequality; `monotone_of_nonneg_deriv` applied twice, to `r ↦ M·r ∓ F(r)`; axiom-free |
| 2026-08-27 | `creal/mvt.rs::build_hd_linear` → `pub(super)` | reused rather than copied; `hasDerivative_smul ∘ hasDerivative_id` would need a magnitude bound on `M` |
| 2026-08-27 | measured: uniform-limit-of-derivatives is ABSENT | `shape_search` at `declarations=1889`; 16 `HasDerivativeOn` conclusions, all pointwise |
