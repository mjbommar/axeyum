# Notes: 246-int-gcd-div

Detail moved out of [`../status/246-int-gcd-div.md`](../status/246-int-gcd-div.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The fourth lemma:** `Int.emod_eq_zero_iff_dvd_general : ∀ a b, b ≠ 0 →
(a % b = 0 ↔ b ∣ a)` (`int_prelude/dvd.rs`, `declare_emod_eq_zero_iff_dvd_general`).
Identical proof shape to `declare_emod_eq_zero_iff_dvd` (the positive-only
original), with every positive-only ingredient swapped for its sign-general
sibling (`Int.emod_natAbs_bound` for `Int.emod_lt_of_pos`,
`Int.ediv_emod_unique_general` for `Int.ediv_emod_unique`; `Int.emod_nonneg`
was already sign-general and carries over unchanged). The one new step: the
`b = 0` branch's required upper bound (`zero < ofNat (natAbs b)`) is not a
hypothesis handed in directly (unlike the positive-only proof, where
`h_pos : 0 < b` already IS that type) — derived instead via
`Int.lt_of_le_of_lt` from `Int.emod_nonneg`/`Int.emod_natAbs_bound` at the
SAME `a, b` (`0 ≤ emod a b < ofNat (natAbs b)` implies `0 < ofNat (natAbs b)`).

**`Int.gcd_div` itself** (`int_prelude/gcd.rs`, `declare_gcd_div`). Sized
the actual work myself rather than trusting either prior lane's estimate,
and it came out LARGER than "comparable to `gcd_div_gcd_div_gcd`'s proof":
that theorem's divisor is always `ofNat (gcd i j) ≥ 0`, so it never needed
the sign-general bridge above, and Mathlib's own route (`Nat.gcd_div` via
`Nat.gcd_mul_left`, both proved in Lean core by a `gcd.induction` strong
induction principle) does not exist in this development and would need a
FRESH strong-induction principle over `Nat.gcd`'s `WellFounded.fix`
recursion to build — comparable in cost to the `gcd_dvd`/`dvd_gcd`/
`gcd_bezout` constructions already in this file, not a one-line borrow.

Built instead by **mutual divisibility**, generalizing
`gcd_div_gcd_div_gcd`'s Bézout route rather than Mathlib's cancellation
route. With `qa := a.ediv c`, `qb := b.ediv c`, `C := natAbs c`,
`G := gcd a b`, `H := gcd qa qb`, and (for `c ≠ 0`) `K := G/C` (exact,
`C ∣ G` follows directly from the theorem's own `c ∣ a`, `c ∣ b`
hypotheses via `nat_abs_dvd_nat_abs_of_dvd` + `Nat.dvd_gcd` — no Bézout
needed for this half):

- **`H ∣ K`.** Bézout on `a, b` gives `ofNat G = a*u + b*v`; substituting
  `a = c*qa`, `b = c*qb` and factoring gives `ofNat G = c*X` for
  `X := qa*u + qb*v` — an UNCONDITIONAL equation, no sign case needed at
  all. Taking `natAbs`: `G = C * natAbs X`. Combined with `C*K = G` and
  cancelling the shared positive factor `C` (`Nat.mul_left_cancel_of_pos`):
  `natAbs X = K`. Separately `H` divides `qa`, `qb`, hence `qa*u`, `qb*v`,
  hence their sum `X`; taking `natAbs` gives `H ∣ natAbs X = K`.
- **`K ∣ H`.** Bézout on `qa, qb` gives `ofNat H = qa*u' + qb*v'`;
  multiplying by `c` and substituting back gives `c*(ofNat H) = a*u' +
  b*v'`. `G` divides `a`, `b`, hence this sum, hence `c*(ofNat H)`; taking
  `natAbs`: `G ∣ C*H`. Cancelling `C` from the divisibility itself (not
  just an equation) via a small locally-built helper (`cancel_dvd_of_pos`
  — no such lemma exists in this development yet) gives `K ∣ H`.
- `Nat.dvd_antisymm` closes `H = K = G/C`.

**Neither direction needed `c`'s sign decomposed into `±ofNat C`** — only
`natAbs` identities, which hold unconditionally. The sign case split that
DOES remain (`c = 0` / `c = ofNat (succ m)` / `c = negSucc n`, via
`case_split` on `c` then `d.induct` splitting the `OfNat` branch's magnitude)
exists only to supply `c ≠ 0` and `1 ≤ natAbs c` per branch, and to prove
`c = 0` as a genuine degenerate case rather than exclude it: both `a` and
`b` collapse to `zero` (`0 ∣ x → x = 0`, a small `zero_dvd_elim` helper
built locally), at which point both sides of the conclusion collapse to `0`
via `gcd_zero_right`/`Nat.zero_div`, and the general `a, b` case is
recovered by two `int_eq_rewrite`s.

**One real defect found and fixed via the kernel's own `TypeMismatch`, not
by inspection.** The first attempt's `K ∣ H` step tried to feed
`cancel_dvd_of_pos` a term of type `Nat.dvd g (cabs*natAbs(ofNat hh))`,
assuming the kernel would bridge `g` and `cabs*kk` by **defeq** — wrong:
`g := Int.gcd a b` does not delta/iota-reduce to a product with its own
quotient; `cabs*kk = g` is a PROVED fact (`cabs_kk_eq_g`), not a
computation. (`natAbs(ofNat hh) ≡ hh` in the same term IS pure `iota` and
needed no fix — the two gaps look identical in the render but are not the
same kind.) Found by a temporary `GCD_DIV_DIAG` `eprintln!` comparing the
kernel's own `TypeMismatch { expected, got }` via `Kernel::render_lean` on
both sides (added, used once, then removed — not left in the tree), which
made the exact missing rewrite obvious in one run rather than a bisect.
Fixed with an explicit `nat_rewrite` through `cabs_kk_eq_g` before the
cancellation.

**Instantiated at three sign combinations, all confirming BOTH sides of the
conclusion compute (`def_eq`) to the expected `Nat` numeral**, not just
that the application type-checks (`gcd_div_applies_at_a_positive_a_negative_
divisor_and_at_zero`, `int_prelude_tests.rs`):
- `a=12, b=18, c=6` (positive divisor): `gcd(2,3) = gcd(12,18)/6 = 1`.
- `a=12, b=18, c=-6` (negative divisor) — a case
  `Int.gcd_div_gcd_div_gcd` cannot even STATE, since its divisor is always
  `ofNat (gcd i j) ≥ 0`: `ediv(12,-6)=-2`, `ediv(18,-6)=-3`,
  `gcd(-2,-3) = gcd(12,18)/natAbs(-6) = 1`.
- `a=0, b=0, c=0` (the degenerate case this proof does NOT exclude):
  both sides compute to `0`.

Each builds its `Int.dvd` witnesses via the same `irefl`-relies-on-defeq
idiom the theorem's own proof uses internally (an explicit-witness route
that would have caught the exact same class of defeq-vs-theorem confusion
described above, had one been present in the witness construction itself).
Did NOT additionally build a "free variable" instantiation check beyond
the theorem's own construction: `int_theorem`'s `arity` parameter already
universally quantifies `a, b, c` as genuine fresh `fvar`s during the
ORIGINAL proof, so the disjoint-defect-class requirement (symbolic +
concrete) is satisfied by the theorem's own existence plus these three
concrete checks, not by a fourth redundant symbolic-only pass.

**Two existing private helpers made `pub(super)` for reuse from `gcd.rs`**
(no behavior change, one-word visibility edits each): `division::positive_of_succ`
(`Nat.le (succ zero) (succ n)`, unconditionally, reused for BOTH `Int.lt
zero cc` and `Nat.le 1 (natAbs cc)` in the nonzero branches — the same raw
term types via defeq for both purposes, since `natAbs cc` unfolds to
`succ n`/`succ m` exactly), and `decide::discriminate` (the constructor-shape
discrimination principle, used to prove `negSucc n ≠ 0` directly rather
than deriving it from an order fact).

**Verified:** `cargo test -p axeyum-lean-kernel --lib int_prelude::` — 47
passed, 0 failed (46 before this lane's first commit, i.e. after the prior
`int-emod-negative` lane; +1 for `Int.emod_eq_zero_iff_dvd_general` proper
inclusion in `derived_laws`, then this pass adds `Int.gcd_div` and its own
instantiation test), including `every_int_declaration_is_checked_and_axiom_free`
and `derived_laws_have_no_axiom_footprint`. `cargo fmt --edition 2024
--check` and `cargo clippy -p axeyum-lean-kernel --all-targets -- -D
warnings` both clean. `python3 scripts/validate-facts.py`: 0 errors, 1840
proved (was 1839).

`derived_laws`'s pinned array in `int_prelude_tests.rs`: 156 → 158 (two
new entries, `p.gcd_div` and `p.emod_eq_zero_iff_dvd_general`), recounted
by grepping the array body for `^\s*p\.` lines (158), not by adding to the
old number.

`theorem_axiom_footprint --release -- Int.gcd_div` (once built) prints
`integer	Int.gcd_div	0	` — empty trailing footprint column, axiom-free,
matching the fact's own `--expect`-style checker.

**What the kernel REJECTED and why:** one `TypeMismatch`, described above
in full (a proposed defeq bridge between `Int.gcd a b` and `cabs*kk` that
does not exist — `cabs*kk = g` is a proved fact, not a reduction). Fixed
with an explicit rewrite; no other term was rejected across either the
bridge lemma or the main theorem.
