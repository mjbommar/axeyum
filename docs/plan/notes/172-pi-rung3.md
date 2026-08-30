# Notes: 172-pi-rung3

Detail moved out of [`../status/172-pi-rung3.md`](../status/172-pi-rung3.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Largest cross-product actually needed: 512·... / a fixed 3,000-denominator
sum**, comfortably under the 10³ estimate in the brief and far under the
10⁵ danger zone: `64·8 = 512` (R³ = (8/5)³ = 512/125), and the fixed
`1/4 + 512/750` check normalizes to denominator `4·750 = 3,000` (numerator
cross-terms `1·750 = 750`, `512·4 = 2,048`). No step approached the
60,000-product SIGABRT threshold this repo's own pricing note warns about.

## What the kernel rejected, and what each rejection actually was

Five distinct rejections, found by bisecting with `Kernel::infer_in` +
`Kernel::def_eq` + `Kernel::render_lean` diagnostics (temporarily inserted,
removed once each fix was confirmed) rather than by re-deriving from the
opaque top-level `TypeMismatch`/`UnboundFVar` each time:

1. **`UnboundFVar`** — `Kernel::infer` on `sum_range_converges_of_dominated`'s
   application used the fresh, EMPTY context; the application mentions `z`/
   `hz1`/`hzr`, still open at that point in construction (only abstracted at
   the very end via `pi_fv`/`lam_fv`). Fixed with `infer_in` + a
   `LocalContext` registering the three, mirroring this file's own
   `bounded_via_uc` convention.
2. **`Int` vs `Nat` argument mixup** (×2, same bug in two places) —
   `Rat.normalize_mul_normalize`'s numerator parameters are `Int`; passed a
   bare `Nat` literal (`d.num(64)`, `d.num(1)`) instead of `d.of_nat(...)` in
   the R³ computation and the `1/4 + 512/750` sum.
3. **`rat_eq_rewrite`'s anchor mistyped** — passed the raw `Nat`
   numerator/denominator as the rewrite anchor instead of the `Rat` VALUE
   built from them (`rat_eq_rewrite`'s `p`/`q` must be `Rat`-typed, matching
   the `Eq` the rewrite is over).
4. **`NatOps` transport used on a `CReal` value** — `eq_to_equiv` (converting
   `CReal.expTerm_one_eq_one`'s `Eq` into an `Equiv`) used `d.eq_motive`/
   `d.transport`, which HARDCODE `Nat` as the carrier
   (`nat_prelude/ops.rs`'s own `transport`: `let nat = self.nat_ty(); …`).
   This repository's own CLAUDE.md already names this trap ("the `NatOps`
   family is `Nat`-only") and it still cost a full bisection round to find.
   Fixed by writing `creal_transport`/`creal_eq_motive` (mirroring
   `rat_prelude::ops`'s `rtransport`/`req_motive` pattern, substituting
   `creal_ty` for `rat_ty`).
5. **A ι-defeq assumption that does not hold** — `sin_lb_magnitude_dec`'s
   antitonicity proof builds its LHS at the succ-chain exponent `ssskk :=
   succ (succ (succ (add k k)))` (needed for `exp_term_succ_scale`/`pow_add`'s
   own ι-reductions to fire), then asserted without proof that this is defeq
   to `odd_index (succ k) = add (add (succ k) (succ k)) 1` (what
   `alternatingLowerBound`'s `hdec` parameter actually names, via `a_fn
   (succ k)`'s own beta-reduction). It is NOT: `add (succ k) (succ k)`
   recurses on its symbolic RIGHT argument and gets stuck one step short of
   `succ (succ (add k k))` — only the PROPOSITIONAL `Nat.succ_add` closes the
   gap. Fixed by transporting the already-computed (previously unused)
   `bridge_rev` proof at the very end, rather than assuming raw ι sufficed.
6. **`t_lam` vs `sinFnTerm` associativity** — the largest of the five.
   `alternatingLowerBound`'s `hconv` parameter is stated over its OWN
   internally-built `t_lam := build_t_lam a_fn` (RIGHT-associated:
   `sign·(coeff·pow)`), never over `CReal.sinFnTerm` (LEFT-associated:
   `(sign·coeff)·pow`) — Equiv via one `mul_assoc` step, never defeq. Passing
   a domination-built `Converges` fact about `sinFnTerm`-sums where
   `alternatingLowerBound` expects one about `t_lam`-sums produced a
   `TypeMismatch` naming neither term shape; only `infer_in` bisection down
   to the individual `hconv`/`dom_hyp` arguments localized it. Fixed by
   building the WHOLE "domination → `Exists(L, Converges)` → squeeze" chain
   around `t_lam` from the start (`build_t_lam_here`, reproduced to match
   `alternating.rs`'s private `build_t_lam` exactly so structural interning
   gives the IDENTICAL `ExprId`), bridging to `sinFnTerm` only where
   something else genuinely needs it: `dom_hyp` via one `mul_assoc`-based
   `abs_congr`/`le_congr` step per `j`, and the squeeze's second leg (which
   is necessarily `sinFnTerm`-based — that is what `sinFnUniformConverges`
   itself proves) via `sum_range_congr` at the FIXED, universally-quantified
   `n` already in scope inside that leg's own construction — an EXACT
   per-`n` equiv, so no uniform-in-`n` modulus was ever needed, unlike the
   `converges_of_close`-based route considered and rejected first.

**Nothing else was rejected.** Every other declaration and lemma application
in this proof was accepted on inspection once the five above were fixed; no
further kernel rejections occurred in the runs that produced the final
passing state.

## Verification run

- `existing_step_order_is_topologically_valid` (builds the FULL `CReal`
  prelude, foreground, default 2 MiB stack): **ok, ~97–99 s**, three
  consecutive runs (one before final cleanup, two after — timing stable,
  confirming the debug-scaffolding removal changed nothing observable).
- `creal_prelude_builds`: **ok, 92.87 s** (within the 91–119 s band this
  lane's own status doc already recorded for this stage of the prelude).
- `every_creal_declaration_is_checked_and_axiom_free` (`--release`): **ok,
  17.49 s** — confirms the new declaration is present, `Theorem`-kind, and
  `axiom_footprint` **0**, read from `kernel.environment()` directly (both
  directions), not from a hand-maintained list.
- `steps_table_matches_recorded_extraction`: **ok**.
- `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D
  warnings`: **green** (one `used_underscore_binding` trip from a debug-code
  rename, fixed in a follow-up commit).
- `rustfmt --edition 2024` applied to the touched file.
- Did **not** run a full `--lib creal::` sweep (per this task's own
  instruction).

## What is new, reusable infrastructure for later lanes

- `CReal.sinFnLowerBoundOneToR` itself, and everything it composes:
  `sin_lb_magnitude_lam`/`_nonneg`/`_dec` (sine's alternating-series
  magnitude sequence and its GLOBAL antitonicity on `[0, 8/5]`, no shift),
  `z_squared_le_prod`/`six_le_two_three_shift`/`nat_mul_le_mul` (the
  `z² ≤ (2k+2)(2k+3)` chain), `r_squared_eq_64_over_25`/
  `r_cubed_eq_512_over_125` (`(8/5)²`, `(8/5)³` as exact rationals),
  `sin_fn_term_dom_at`/`sin_fn_cauchy_g` (domination-based Cauchy witness
  for `sinFnTerm`-sums), `nat_div_succ_self_eq_one` (`(n+1)/(n+1) = 1`, a
  drop-in generalization of `one_le_r_domain`'s own `n := 4` instance),
  `add_sub_cancel_right`, `one_mul_eq`, `build_t_lam_here` /
  `t_lam_eq_sinfnterm` (the `t_lam`↔`sinFnTerm` associativity bridge —
  directly reusable by rung 2's own shifted-series construction, which needs
  the identical bridge for cosine's magnitude sequence).
- `creal_transport`/`creal_eq_motive`: the CReal-typed analogues of
  `NatOps::transport`/`eq_motive` this file was missing. Any future
  `Eq CReal a b → Equiv a b` conversion in `creal/trig_fn.rs` should use
  these, not the `Nat`-hardcoded `NatOps` family.

## What is NOT done

- Rung 2 (`cos (8/5) < 0`, the shifted-series alternating bound) remains
  unbuilt — `docs/plan/status/169-pi.md` already sizes its own remaining gap
  (the `Converges` witness for the shifted series) and nothing here closes
  it, though `t_lam_eq_sinfnterm`'s bridging TECHNIQUE (build the whole
  chain around the internally-needed `t_lam`/shifted form, bridge to the
  pre-existing declaration only at the two points that need it) transfers
  directly.
- `CReal.pi` itself is not constructed; no root is asserted to exist. Rungs
  1–3 are the three numeric ingredients `ivt_exact_root` needs
  (`cos 1 ≥ 0`, `cos(8/5) < 0`, a uniform positive lower bound on `sinFn`
  over `[1, 8/5]`) — rung 3 is now landed, rung 2 is not.
