# Notes: 306-totient-even-finish

Detail moved out of [`../status/306-totient-even-finish.md`](../status/306-totient-even-finish.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **Step 0** (peel index 0): `countRange_split(f, 1, n-1)` plus `f 0 = false`
  (from `gcd_zero_left` + `beq_eq_false_of_ne`, `n > 1`), reducing
  `Even (totient n)` to `Even (countRange h (n-1))` for `h(k) := f(1+k)`.
- **`reflection_pieces`** (shared by both of the general lemma's hypotheses):
  the index correspondence `k1 := succ j`, `k2 := succ (sub (pred L) j)`,
  `k1 + k2 = n` — built by peeling two `succ`s down to
  `add_sub_cancel_of_le(j, pred L, …)` rather than fighting `add`/`sub`
  associativity directly.
- **`gcd_reflection_iff`**: `gcd(k1,n)=1 <-> gcd(k2,n)=1` for `k1+k2=n`,
  composing THREE already-declared `Iff`s
  (`coprime_self_add_right` twice + `coprime_symmetric`) by direct
  `mp`/`mpr` function composition — no general `iff_trans` helper exists in
  this prelude and building one wasn't needed.
- **`bool_eq_of_iff_eq_one`**: bridges an `Iff` about `Eq _ one` to an
  `Eq Bool (beq _ one) _`, by deciding `beq a one` via `bool_true_or_false`
  and pushing each branch through `eq_of_beq_eq_true`/`ne_of_beq_eq_false`
  and `beq_eq_true_of_eq`/`beq_eq_false_of_ne`. Reusable wherever an `Iff`
  over `Eq _ 1` needs to become a `Bool`-level fact (i.e. anywhere a
  predicate is *defined* as `beq _ 1`, which is this whole `countRange`
  family's convention).
- **hyp2** (no fixed point): at a would-be fixed point `k1 = k2`, `k1 | n`
  (via `dvd_add` at `k1+k1`) combined with `gcd k1 n = 1` (from `h(j)=true`)
  gives `k1 | gcd k1 n = 1` (`dvd_gcd` + `eq_one_of_dvd_one`), forcing
  `k1 = 1`, hence `n = 2`, contradicting `2 < n` via `lt_irrefl`.

**The actual bug, found by bisection, not by reading the failure output.**
Wiring this in poisoned all 174 baseline `nat_prelude::` tests identically
(the "one bad declaration poisons the shared build" pattern CLAUDE.md
already names). Per that entry's own remedy, I split the one big `d.theorem`
closure into checkpoints — first via throwaway `declare_theorem` calls at
intermediate stages (which themselves failed with `UnboundFVar`, because a
checkpoint built with `d.theorem`'s convenience wrapper leaves the OUTER `n`
unbound — fixed by switching `declare_totient_even` to manage its own
`n_fv`/`hn_fv` by hand, the same manual `pi_fv`/`lam_fv` style
`declare_dvd_two_of_totient_le_one` already uses), then via
`Kernel::infer_in` against an explicit `LocalContext` (the
CLAUDE.md-documented debug-probe technique). The checkpoint on Step 0 alone
isolated a genuine `TypeMismatch` whose rendered sides
(`render_lean`) were:

```
expected: Eq.{1} AxNat _fvar.0 (AxNat.succ (AxNat.pred _fvar.0))
got     : ((x1 : AxNat.lt AxNat.zero _fvar.0) -> Eq.{1} AxNat _fvar.0 (AxNat.succ (AxNat.pred _fvar.0)))
```

i.e. a FUNCTION where an equality was expected. `finite.rs`'s
`pos_implies_succ_pred(d, p, n)` returns `Lt zero n -> Eq n (succ (pred n))`
— NOT the equality itself; the caller must apply it to a positivity proof
(`totient_le_one_contradiction_above_two` in this same file does this
correctly: `let eq_x_fn = pos_implies_succ_pred(…); let eq_x =
d.apply(eq_x_fn, &[pos_x]);`). I had used it unapplied at BOTH call sites
(`n = succ Lrng` and `Lrng = succ pm`). Fixed by deriving the needed
positivity witnesses (`zero_lt_via_c` for `n`, an explicit `Le one Lrng`
chain for `Lrng`) and applying the returned function to them. All
checkpoints then passed on the first retry, and the debug scaffolding
(checkpoints, rendered-mismatch panics) was removed before committing —
the committed proof is the clean version.

**Lesson for the next lane using `pos_implies_succ_pred` (or any
`X_implies_Y_fn`-shaped helper in this codebase): read whether the doc
comment's `h : …` is a PARAMETER the function itself supplies, or one the
CALLER must apply the RETURN VALUE to. `finite.rs`'s own doc comment on
`pos_implies_succ_pred` says exactly this (`` `h : Lt zero n ⊢ Eq n (succ
(pred n))` ``, meaning `h` is consumed, not produced) but is easy to
misread as "already discharges its own positivity side-condition."**

## Two mirrors, cheap once `totient_even` existed

`Nat.odd_totient_iff_eq_one : ∀ n, Iff (Odd (totient n)) (Eq (totient n)
one)` — the SAME `trichotomy(two, n)` shape `totient_eq_one_iff` already
uses, with the `2 < n` branch refuted by `totient_even` + `odd_not_even`
instead of a counting contradiction, and the `n = 0` sub-case refuted by
`even_not_odd` against a fresh `Even 0` witness (`even_zero_witness`, a
one-line `Exists.intro`). The reverse direction transports a fresh `Odd 1`
witness (`odd_one_witness`, `Exists.intro` at `k=0`, `Eq.refl`) along the
hypothesised `totient n = 1`.

`Nat.odd_totient_iff : ∀ n, Iff (Odd (totient n)) (Or (Eq n 1) (Eq n 2))` —
`odd_totient_iff_eq_one` composed with `totient_eq_one_iff` by direct
`mp`/`mpr` function composition (the same composition style
`gcd_reflection_iff` already uses for its own three-`Iff` chain).

Both type-checked on the FIRST kernel-verification attempt — no bisection
needed, unlike `totient_even` itself.

## What's left: `Nat.totient_coprime_totient_iff`

`∀ m n, Iff (gcd (totient m)(totient n) = 1) (Or (Or (Eq m 1)(Eq m 2)) (Or
(Eq n 1)(Eq n 2)))`. Not attempted this session (budget) — the module doc's
own triage is still accurate; here is the concrete route, more precise than
that triage since `totient_even`/`odd_totient_iff*` now exist to build on.

**`mpr` (cheap, ~20 lines):** given `(m=1 or m=2) or (n=1 or n=2)`, whichever
side holds gives `totient _ = 1` (via `totient_eq_one_iff`'s `mpr`), then
`gcd 1 x = 1` / `gcd x 1 = 1` via `coprime_one_left_iff`/
`coprime_one_right_iff` (unconditional, no case split needed on the other
argument).

**`mp` (the real work).** Given `h : gcd (totient m)(totient n) = 1`, split
`m` via `trichotomy(two, m)`:

- `m = 1` or `m = 2`: goal by `or_inl` directly, done.
- `m < 2` sub-case `m = 0`: `totient 0 = 0` (defeq), so `h` rewrites to
  `gcd 0 (totient n) = 1`. `gcd_zero_left(totient n) : gcd zero (totient n)
  = totient n` gives `totient n = 1` directly (no `gcd_zero_right` needed —
  `totient m` is the FIRST gcd argument in this fact's own statement, and
  `m=0` puts the zero on the side `gcd_zero_left` already covers). Then
  `totient_eq_one_iff.mp` gives `n=1 or n=2`, goal by `or_inr`.
- `m > 2`: `totient_even(m)` gives `Even (totient m)`. Split `n` via
  `trichotomy(two, n)` the same way:
  - `n = 1` or `n = 2`: goal by `or_inr`, done — **this branch does not need
    `m`'s parity at all**, so it is genuinely cheap even inside the hard
    case.
  - `n = 0`: `totient n = 0`. Need `gcd (totient m) 0 = totient m` — THIS
    prelude does not have `gcd_zero_right` as a named field (checked:
    `nat_prelude.rs` line ~896-925 only lists `gcd_zero_left`). Build it
    inline: `gcd_comm(totient m, 0)` composed with `gcd_zero_left(totient
    m)` (`gcd 0 (totient m) = totient m`) gives `gcd (totient m) 0 =
    totient m` by `trans`. Then `h` (after the `n=0` rewrite) gives
    `totient m = 1`, contradicting `Even (totient m)` via `even_not_odd` +
    `odd_one_witness` (**exactly the same pattern
    `odd_totient_iff_eq_one`'s `n=0` sub-case already uses, just with
    `Even`/`Odd` swapped** — `Even (totient m)` and `Odd 1`, transport one
    along `totient m = 1`, apply `even_not_odd` to the other). `ex_falso`
    closes the goal.
  - `n > 2`: `totient_even(n)` gives `Even (totient n)`. **This is the one
    genuinely new piece**: from `Even (totient m)`, `Even (totient n)`, and
    `h : gcd (totient m)(totient n) = 1`, derive `False`. Route:
    1. `Even x -> dvd 2 x`: from `Exists k, x = k+k`, need `Eq (mul 2 k) (add
       k k)` to get a `dvd_intro` witness. `Nat.succ_mul` EXISTS in this
       prelude (`nat_prelude.rs:636`, unlike the mirrored `mul_succ` which
       is a pure `Eq.refl` — `succ_mul` is a real induction-proved theorem,
       confirmed present, not yet confirmed how it composes with
       `zero_mul`/`mul_zero` to close `mul 2 k = add k k` — budget the
       actual chain as ~10-15 lines: `mul two k = mul (succ one) k =
       add (mul one k) k` (`succ_mul(one,k)`) `= add k k` (needs `mul one k
       = k`, i.e. `one_mul` — check this field exists before assuming it;
       `mul_comm` + the already-used `one_mul` pattern from
       `dvd_two_of_totient_le_one`'s proof, which used `p.one_mul` at line
       ~985, confirms it exists).
    2. `2 | totient m`, `2 | totient n` from the two `Even` facts via step 1.
    3. `dvd_gcd(2, totient m, totient n, …) : 2 | gcd (totient m)(totient n)`,
       transported along `h` to `2 | 1`.
    4. `eq_one_of_dvd_one(2, that) : Eq 2 one`, refuted by the SAME pattern
       `n_ne_one_from_lt_two`/`totient_le_one_contradiction_above_two`
       already use: transport `le_refl 2` along the false equation to `Le 2
       one`, defeq `Lt one one`, refuted by `lt_irrefl(one)`.
    `ex_falso` closes the goal with this `False`.

**Sizing**: comparable to `totient_even`'s own construction, maybe 60-70%
of it (no general lemma to wire in, no well-founded induction — this is
pure case analysis over an already-closed toolkit). The one piece to
verify BEFORE writing Rust: confirm `mul two k = add k k` composes from
`succ_mul`/`one_mul`/`zero_mul` in the form assumed above by simulating in
Python first (this file's own convention, and CLAUDE.md's standing
"simulate before building" rule for anything touching a fuel/recursion
asymmetry — `mul` recurses on its RIGHT argument, so `succ_mul` genuinely
needs induction and is NOT free the way `mul_succ` is).

## Files

- `crates/axeyum-lean-kernel/src/nat_prelude/totient_lemmas.rs` — all three
  new declarations (`declare_totient_even`, `declare_odd_totient_iff_eq_one`,
  `declare_odd_totient_iff`), plus new local helpers (`nat_congr_bool`,
  `one_add_eq_succ`, `n_ne_one_from_lt_two`, `gcd_reflection_iff`,
  `reflection_pieces`, `bool_eq_of_iff_eq_one`, `odd_one_witness`,
  `even_zero_witness`).
- `crates/axeyum-lean-kernel/src/nat_prelude.rs` — three new `NameId` fields
  (`totient_even`, `odd_totient_iff_eq_one`, `odd_totient_iff`) and their
  dispatch (after `declare_count_range_reversal_even`/`declare_parity_all`,
  NOT inside `declare_totient_lemmas_all` — see the doc comment on that
  function for why).
- `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` — three
  new tests (concrete instances at `n` in `{1,2,6,9}` plus a genuinely free
  `n`/`hn` for each), all three added to `theorem_names` (the
  environment-derived coverage assertion), and the determinism pin moved
  `93+568 -> 93+571` across the two commits (each taken from the panic's own
  mismatch, never hand-incremented).
- `artifacts/facts/F-ml430-nat-totient-even-28e0415f.json`,
  `F-ml430-nat-odd-totient-iff-b6a6596f.json`,
  `F-ml430-nat-odd-totient-iff-eq-one-d0491d84.json` — flipped to `proved`,
  `depends_on` completed by `scripts/check-fact-depends-derived.py --fix`.

## Verification

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 177 passed, 0
  failed (174 baseline + 3 new).
- `cargo fmt --edition 2024` (per-file) and
  `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`: clean.
- `python3 scripts/check-test-attribute-integrity.py`: 0 findings.
- `python3 scripts/validate-facts.py`: 2114 facts, 0 errors.
- Both evidence `checker_command`s per flipped fact verified directly: pass
  on the real name (count 1), and the two `odd_totient_iff`/
  `odd_totient_iff_eq_one` anchored patterns confirmed to disambiguate their
  shared prefix (each counts exactly 1 against the same two-row
  `nat_theorem_inventory` output).

## Commits (not pushed)

- `26fcfdfc1` — wip, `Nat.totient_even` built but not yet kernel-verified
  (landed per "commit before any long check").
- `a4070da4d` — the working, kernel-verified `Nat.totient_even` (fixes the
  `pos_implies_succ_pred` bug above), plus its test and pin.
- `8c43039ae` — `F:ml430-nat-totient-even` flips to `proved`.
- `5e80a4856` — `Nat.odd_totient_iff_eq_one` and `Nat.odd_totient_iff`,
  verified, tests, pin.
- `36af6ba68` — both facts flip to `proved`.
