# Notes: 242-int-emod-negative

Detail moved out of [`../status/242-int-emod-negative.md`](../status/242-int-emod-negative.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Instantiated at a positive divisor (`b = 1`), a negative divisor (`b = -1`,
where `emod_lt_of_pos`'s own hypothesis `0 < b` is structurally FALSE, so
that theorem could not even be invoked there), and independently checked
the excluded `b = 0` corner as a negative control: `emod a 0 = a` and
`natAbs 0 = 0` make the excluded conclusion demand `5 < 0`, refuted by
`Nat.not_succ_le_zero` — confirming the hypothesis is genuinely
load-bearing, not decoration.

**Build-order gotcha**: `Int.natAbs` is not declared until well after
`Int.ediv_emod_unique` in `build_int_prelude_uncached`'s call sequence, so
`declare_emod_natabs_bound` (and later `declare_ediv_emod_unique_general`)
had to move to right after `nat_abs::declare_nat_abs(&mut d)?;`, not beside
their `emod_nonneg`/`emod_lt_of_pos`/`ediv_emod_unique` siblings higher up
the list. Confirmed by a temporary debug harness
(`match build_int_prelude(&mut k) { Err(UnknownConst{name}) => panic!("{}",
k.display_name(name)), ... }`) which named `Int.natAbs` directly — this is
the fast way to diagnose this build-order class of failure, cheaper than
bisecting call-site positions by hand.

**2. `Int.ediv_emod_unique_general`** (same file): `∀ a b q1 r1 q2 r2, Not
(Eq Int b zero) → a = b*q1+r1 → 0 ≤ r1 → r1 < ofNat (natAbs b) → a =
b*q2+r2 → 0 ≤ r2 → r2 < ofNat (natAbs b) → q1 = q2 ∧ r1 = r2`. `
ediv_emod_unique` needs `0 < b` for two independent reasons — it bounds the
remainder against `b` itself, AND its proof (`build_core`/`solve_le_case`)
reasons about `Int.mul b _` growing monotonically in the quotient, which
only holds for a positive multiplier. Rather than re-deriving that
machinery for a negative divisor, this reduces to the already-proved
positive case by a change of variable, exploiting a definitional
coincidence: `Int.neg (negSucc n)` ι-reduces to `ofNat (succ n)` — the SAME
value `Int.natAbs (negSucc n)` ι-reduces to. So for `b < 0`, `neg b` already
**is** (up to defeq) the positive divisor the bound hypotheses are already
stated against; only the two reconstruction equations need rewriting (`b*q
= (neg b)*(neg q)`, via a small local `neg_mul_neg` extraction of `gcd.rs`'s
already-proved `neg_mul`/`neg_neg`). Applying `ediv_emod_unique` at divisor
`neg b` and negated quotients gives `neg q1 = neg q2`; un-negate with
`neg_neg` twice to recover `q1 = q2`. The positive-divisor branch needs no
rewriting at all — `natAbs (ofNat n) ≡ n` makes the general bound already
defeq to `ediv_emod_unique`'s own bound.

Two bugs caught before the first successful build, both by immediate
compile/kernel feedback rather than inspection: a double-mutable-borrow in
the `case_split` `stmt` closure (`d.arrow(d.not(eq_ty), inner_goal)` —
flattened into a `let`, the exact idiom Gotcha #10 in `CLAUDE.md`
documents), and reusing bare hypothesis-value fvars as their own `lam_fv`
TYPE arguments in the negative-divisor branch (fixed by computing the six
actual hypothesis types via a new `unique_hyps_general` helper mirroring
`build_core`'s existing `UniqueHyps`-typed pattern, rather than improvising
types from the value fvars).

Instantiated at a genuine positive divisor (`13 = 4*3+1`, mirroring the
existing `ediv_emod_unique_applies_at_a_concrete_decomposition` test) and a
genuine negative divisor (`13 = (-4)*(-3)+1` — a decomposition
`ediv_emod_unique` cannot even be invoked on, since `Int.lt Int.zero (-4)`
is FALSE). Both type-check end to end and land on the exact `q1=q2 ∧ r1=r2`
conclusion.

**What the kernel REJECTED and why**: nothing, in either declaration, once
the two Rust-level bugs above were fixed (a borrow-checker error and a
malformed `lam_fv` call — both caught before `add_declaration` was ever
invoked). No proof term was rejected by the trusted gate.

**Left open, precisely: `Int.gcd_div` itself.** Assessed but not attempted
this pass, for a reason beyond the two lemmas above. The natural proof
route for a negative common divisor `c` is NOT a simple sign-flip of
`gcd_div_gcd_div_gcd`'s route (which only ever used a positive `c = ofNat
(gcd a b)`): `gcd_div_gcd_div_gcd` obtained `i = c*qi` via the POSITIVE-only
`emod_eq_zero_iff_dvd`'s `mp` direction plus `ediv_add_emod`. Generalizing
`Int.gcd_div` to a negative `c` needs the SIGN-GENERAL analogue of that
bridge (`c ≠ 0 → (emod a c = 0 ↔ c ∣ a)`) — a **fourth** lemma this lane's
two landed pieces make constructible (from `emod_natAbs_bound` +
`ediv_emod_unique_general`, by the same proof shape `emod_eq_zero_iff_dvd`
already uses, generalized) but which is **not itself built yet**, and which
the prior handoff's three-lemma decomposition did not name. Once that
bridge exists, `Int.gcd_div`'s own proof still needs a genuine new
mutual-divisibility argument relating `gcd(a.ediv c, b.ediv c)` to
`gcd(a,b)/natAbs c` — comparable in size to `gcd_div_gcd_div_gcd`, as the
prior handoff estimated, but now for an arbitrary sign `c` rather than the
always-nonnegative `c = gcd a b`.

Given the size and risk of that combined remaining work relative to this
lane's remaining budget, and given the brief's own framing that landing the
keystone (`emod_natAbs_bound`) alone was a complete success, this pass
stops here having landed both of the general-purpose lemmas rather than
risk a rushed or incorrect `Int.gcd_div` construction. A future lane can
pick up directly: build the sign-general `emod = 0 ↔ dvd` bridge first (it
is now a short derivation from the two lemmas this pass landed), then
attempt `Int.gcd_div` itself with `gcd_div_gcd_div_gcd`'s proof as the
template for the positive-divisor case.

**Timing / counts**: `cargo test -p axeyum-lean-kernel --lib int_prelude::`
— 40 passed before this lane started, 41 after landing
`emod_natAbs_bound`, 42 after landing `ediv_emod_unique_general`.
`derived_laws`'s pinned array: 151 → 152 → 153, recounted each time by
grepping the array body for `^\s*p\.` lines, never by incrementing the old
number. `cargo fmt --all --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both
clean at each commit. No `python3 scripts/validate-facts.py` run was needed
(no ledger file was edited this pass).
