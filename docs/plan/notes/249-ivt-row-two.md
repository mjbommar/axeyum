# Notes: 249-ivt-row-two

Detail moved out of [`../status/249-ivt-row-two.md`](../status/249-ivt-row-two.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

| declaration | kind | what it is |
| --- | --- | --- |
| `CReal.uniformly_continuous_max` | theorem | `∀ F G a b, UC F a b → UC G a b → UC (fun r => max (F r) (G r)) a b` |
| `CReal.uniformly_continuous_min` | theorem | the same for the meet |
| `CReal.ivtPlateau` | def | `fun v x => min x (max (add x (neg one)) v)` |
| `CReal.ivtPlateau_nonpos_at_zero` | theorem | `∀ v, le (ivtPlateau v zero) zero` |
| `CReal.ivtPlateau_nonneg_at_one` | theorem | `∀ v, le zero (ivtPlateau v one)` |
| `CReal.ivtPlateau_uniformly_continuous` | theorem | `∀ v, UniformlyContinuousOn (ivtPlateau v) zero one` |
| `CReal.ivt_exact_root_decides_sign` | theorem | **row 2** |

## The family, and how its hypotheses were discharged

`ivtPlateau v := fun x => min x (max (x + (−1)) v)` on `[0, 1]` — the **clamp of
`v` into the unit-width window `[x − 1, x]`**. Classically a ramp `x ↦ x`, then
a horizontal **plateau** at height `v`, then a ramp `x ↦ x − 1`:

| `v` | value on `[0, 1]` | root |
| --- | --- | --- |
| `0 < v` | `x` on `[0, v]`, then the plateau `v > 0` | unique, at `x = 0` |
| `v < 0` | the plateau `v < 0`, then `x − 1` on `[v + 1, 1]` | unique, at `x = 1` |
| `v = 0` | identically `0` | every `x ∈ [0, 1]` |

The root sits at the **left** endpoint exactly when `v ≥ 0` and at the **right**
endpoint exactly when `v ≤ 0`, so its *position* is the sign of `v`. A plateau
is what forces this, which is why no polynomial family could serve —
constructive IVT *is* available for polynomials, and the two lattice operations
are exactly what takes this family outside that fragment.

The interval and the parameterisation were chosen so that the endpoint
conditions fall out of the lattice's universal properties with **no case split
and no condition on `v`**. That was not free — the textbook family
`min (3x−1) (max (3x−2) v)` needs sign reasoning at both ends.

- **Left endpoint, `le (ivtPlateau v zero) zero`.** ONE `min_le_left`. The
  window's ceiling is `x` itself, so the value at `x = 0` is `min zero _`.
- **Right endpoint, `le zero (ivtPlateau v one)`.** One `le_min` against
  `le zero one` (`le_of_lt zero_lt_one`) and `le zero (max (1 + (−1)) v)`, the
  latter being `le_max_left` transported across `add_neg one`.
- **Uniform continuity.** Pure assembly, once the lattice closure lemmas exist:
  `uniformly_continuous_min` at `F := id` (`uniformly_continuous_id`) and
  `G := fun r => max (r + (−1)) v`, which is `uniformly_continuous_max` at
  `uniformly_continuous_add`(`id`, `const (−1)`) and `uniformly_continuous_const v`.
  All the β-reducts line up by defeq; nothing is transported.

## The two lemmas that did not exist

**`CReal.uniformly_continuous_max` / `_min` are new and general.** The lattice
had no entry in the closure table `uniformly_continuous_add`/`_neg`/`_sub`/
`_mul` already fill for the ring. Combined modulus `mF n + mG n` — `Nat.add`
rather than a `Nat.max` this development does not have, unblocked by
`Rat.natDivSucc_antitone`, exactly as `uniformly_continuous_add` does it — and
**no index shift**: `max`/`min` are one-Lipschitz *jointly* (`creal/lattice.rs`,
`Rat.sub_max_le`), so both specs are consulted at the caller's own accuracy `n`
and no `1/(2n+2)` halving argument is needed.

`two_sided_of_abs_sub_le` / `abs_le_of_two_sided` are what make the estimate
short: split each `close_within` into `F x ≤ F y + q` and `F y ≤ F x + q`, do
the lattice step, rebuild. Found by searching for the STEP — the shape
"`|x − y| ≤ q` split into two shifted one-sided `le`s" — not by name; they live
in `creal/integral.rs` and `creal/order_extra.rs`, filed under their first
consumers, which is hiding place 1 exactly.

**`_min` is NOT a transcription of `_max`, and the asymmetry is real.** For the
join, `max_le` applies directly because `max (F x) (G x)` is on the LEFT of the
goal and the two bounds come from `le_max_left`/`_right` on the right. For the
meet, `min` is *also* on the left, so `le_min` would need the RIGHT to be a
meet — and `min (F y) (G y) + q` is not one. Distributing `q` over `min` would
need a lemma that does not exist. The fix is to move `q` across first: prove
`min (F x) (G x) + (−q) ≤ min (F y) (G y)` by `le_min`, then shift back. That
is the whole reason this file carries the two `((x + a) + b) ≈ x` cancellation
helpers and the `max` half does not.

## The proof of row 2

Write `a := c + (−1)`, `w := max a v`; the root hypothesis is `min c w ≈ 0`.
Two consequences are free off the meet's projections: `0 ≤ c` (`min_le_left`)
and `0 ≤ w` (`min_le_right`, transported along the root).

One `lt_cotrans` on the fixed, always-strict pair `zero_lt_one` at `z := c` —
the same device `evt_attained_max_decides_sign` and `ivt_step` both use — gives
`Or (lt zero c) (lt c one)`. Each branch makes ONE more cotransitivity call, and
**both of its cases land a disjunct**, so there are exactly four leaves:

- **`0 < c`**, cotransitivity at `z := v` → `Or (lt zero v) (lt v c)`.
  - `0 < v` → `le_of_lt` → right disjunct.
  - `v < c` → with `a ≤ c` (that is `c + (−1) ≤ c + 0 ≈ c`), `max_le` gives
    `w ≤ c`, `le_min` gives `w ≤ min c w`, antisymmetry gives `w ≈ 0`, and
    `le_max_right` gives `v ≤ w ≈ 0` → left disjunct.
- **`c < 1`**, so `a < 0` (add `(−1)` to both sides, transport `(−1) + 1 ≈ 0`);
  cotransitivity at `z := v` → `Or (lt a v) (lt v zero)`.
  - `a < v` → `max_le` gives `w ≤ v`, `le_max_right` gives `v ≤ w`, so `w ≈ v`,
    and `0 ≤ w` from above → right disjunct.
  - `v < 0` → left disjunct.

Neither interval hypothesis is consumed. They are kept because IVT's own
conclusion supplies them, and their being unnecessary strengthens the
reduction — the root need not even be known to lie in `[0, 1]`. Same as EVT's.

## The principle derived, and the command confirming it is ABSENT

The conclusion `∀ v, Or (le v zero) (le zero v)` is **analytic LLPO**,
equivalently the total order `le_total` over `CReal`. Non-vacuity is part of the
claim, not a preliminary — a reduction to something the kernel already proves is
worth nothing. Confirmed by reading `kernel.environment()`:

```sh
cargo test -p axeyum-lean-kernel --lib \
  creal::creal_tests::ivt_row_two_derives_a_principle_absent_from_the_environment \
  -- --exact
#  -> 1 passed (111.60 s)
```

That test enumerates every display name in the environment and asserts
`CReal.le_total`, `CReal.lt_total`, `CReal.leTotal`, `CReal.ltTotal` are all
absent, matching **exactly**, not by substring — `Rat.le_total` and
`Nat.le_total` both exist and a substring match would wrongly report the
principle as present. It is paired with a POSITIVE control of the same
declaration kind found by the identical lookup, `CReal.lt_cotrans`, which
exists precisely because the total comparison does not. Without that control an
empty answer and a broken query are the same observation.

## What the kernel rejected

**Nothing.** All seven declarations were accepted on the first
`add_declaration`. Three things are why, and they are worth reusing:

1. The whole file was written against `creal/extreme_value.rs`'s proof term
   rather than from scratch — same `or_elim`/`or_inl`/`or_inr` shape, same
   `lt_congr` transport for the `c < 1` → `c + (−1) < 0` step, and
   `uniformly_continuous_lattice` copied the modulus/antitone/`uc_mk` skeleton
   out of `declare_uniformly_continuous_add` line for line.
2. Every `le_congr` direction was read off an existing call site rather than
   assumed. `le_congr(x, x', y, y', hxx', hyy', h)` takes `h : le x y`, the
   **pre**-substitution type; that family produced eleven rejections in one
   session elsewhere.
3. The step whose lemma did not exist (`min`'s shift) was identified on paper
   *before* any term was built, so the two cancellation helpers were written
   once instead of being discovered by a `TypeMismatch`.

## Measurements

| check | result |
| --- | --- |
| `cargo check -p axeyum-lean-kernel --lib` | clean |
| `creal_prelude_builds` (`--lib`, debug, `RUST_MIN_STACK` unset) | **ok, 112.49 s** — the band on this box across recent lanes is 89–123 s, so no regression signal; no per-leg bisect was needed |
| `creal::creal_tests::ivt_` (7 tests, incl. the 4 pre-existing) | **ok, 7 passed, 113.18 s** |
| `every_creal_declaration_is_checked_and_axiom_free` (`--release`) | **ok, 18.09 s** — coverage read from `kernel.environment()`, so all seven are kind-checked and footprint-checked |
| `nat_axiom_inventory --include-constructed --require-axiom-free creal` | `ok: creal trusted surface = 0`, exit 0 |
| `python3 scripts/validate-facts.py` | **1926 facts checked, 0 errors** |
| `cargo fmt --all --check` | clean |
| `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` | clean |

Not run, deliberately: the workspace gate. The coordinator re-verifies.

## Tests added

- `ivt_plateau_endpoint_values_reduce_and_the_root_endpoint_flips_with_the_sign_of_v`
  — the **evaluation test a `Definition` needs**, since `add_declaration` has
  nothing to compare a definition's body against. `min`/`max`/`neg` take no
  index shift, so index 0 of a constant argument is the value: at `v = 3` the
  endpoints reduce to `(0, 1)` and at `v = −3` to `(−1, 0)`. The root ENDPOINT
  flips, which is the whole counterexample. Numerals deliberately differ from
  the EVT test's `(0, 3)` / `(0, −3)` so a copy-paste fails loudly, and it
  closes with an explicit non-vacuity assertion.
- `ivt_plateau_is_the_clamp_the_row_two_theorem_uses` — one *positive* `def_eq`
  at closed arguments. No failing-`def_eq` negative control: a failing `def_eq`
  has no early exit, and the evaluation test above discriminates strictly
  better for free.
- `ivt_row_two_derives_a_principle_absent_from_the_environment` — above.

## The fact

`artifacts/facts/F-creal-ivt-exact-root-decides-sign.json`, `curated`,
`epistemic_status: proved`, `proof_route: kernel-lean`, `external_status:
proved` with `prior_art` on Bishop / Bridges & Richman carrying an explicit
`attribution` saying this lane did **not** consult the primary sources. Four
evidence rows, each with an exit status that depends on the finding:

- `theorem_dependency_inventory … | /usr/bin/grep -cE '^CReal\.ivt_…[[:space:]]'`
  — two failure modes (a named filter matching nothing; an absent anchored
  line). `[[:space:]]`, never `\t`. `grep -c`, never `grep -q`.
- `test "$(… prelude_theorem_inventory … | grep -cE …)" = 3` for the three
  hypothesis-class theorems. The count is **tested**. The prelude column is
  anchored to `creal` because `complex` and `cpoint` re-declare them and the
  unanchored pattern returns 9 — which would keep returning a plausible number
  if two of the three vanished. The footprint column is anchored at `0`.
- the absence test, `-- --exact`.
- `nat_axiom_inventory --require-axiom-free creal`.

**A measured trap worth carrying:** `theorem_dependency_inventory` consumes only
its **first** name argument and silently ignores the rest. A three-name
invocation prints one row and `1 theorems, 1 with dependencies, 1 edges`, which
reads as success. Anything checking several declarations at once must use
`prelude_theorem_inventory` with a tested count instead.

## Honest scope

This is **not** a proof that `∀ v, Or (le v zero) (le zero v)` is false, and no
such proof is available: analytic LLPO is consistent with Bishop's constructive
mathematics, so it is *unprovable here*, not refutable. ADR-0603's name
"boundary refutation" is looser than what is proved, for this row and for EVT's.

It does **not** contradict `CReal.ivt_exact_root`, which does produce an exact
root: that theorem carries a uniformly positive derivative hypothesis, and
`ivtPlateau` has a plateau — derivative `0` on an interval of positive length —
so it is precisely the shape that hypothesis excludes. The two bound the
constructive fragment from opposite sides.

It does **not** supersede `creal/ivt.rs`'s two bisection counterexamples, which
are untouched. Those close off two specific *construction routes* to an exact
root; this is a claim about the *statement*. Neither implies the other.

## Docs updated

- `docs/research/11-design-review/2026-08-28-ivt-evt-pareto-position-measured.md`
  — corrected, not restated: the row-2 paragraph now says what the old
  "kernel-computed reduction test" actually was and that IVT's row 2 is a
  declaration; the declaration table, the "no counterpart at all" bullet, a new
  `ivt_exact_root` caveat, and a dated verdict update.
- `docs/research/11-design-review/2026-08-29-ivt-has-no-row-2-theorem-evt-does.md`
  — CLOSED banner at the top, body kept: its algorithms-vs-statement
  distinction is still exactly right and is why `ivt.rs` was left alone.

## Commits

| sha | what |
| --- | --- |
| `138129b8f` | status stub (early commit, no kernel work) |
| `e5130895d` | the seven declarations + `creal.rs` wiring + inventory shard |
| `8f57fa2b9` | the three tests |
| `ca74e8d2d` | the fact, plus rustfmt reflow |

Plus this file and the two doc corrections in the following commit.
