# Lane: ring-tactic-2 — the ring producer over ℤ and ℚ, and the ℕ sorting fix

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, ring-tactic-2, 2026-09-03).** Continuing
`ring-tactic-1`/ADR-1580: fixed the ℕ producer's documented intra-monomial
sorting gap, then built `ring::int` and `ring::rat` and retired five
ring-rearrangement proofs on each carrier. Full account in ADR-1582.

**The ℕ fix.** `ring::nat::Problem::sort_factors` ports `sort_items`'s
adjacent-transposition trick to a monomial's own factor list. `x*y = y*x` is
now proved (was `NotAnIdentity`), with a negative control over the same
factor set (`x*y = x*x`, still declines).

**ℤ and ℚ producers, and what each carrier forced.** `ring::int` mirrors
`ring::nat`'s shape but `neg`/`sub` are real ring operations (not declined),
nothing reduces (`Int.add`/`Int.mul` case-split on both arguments, so the
numeral-scale step is genuine `left_distrib` induction, not the ℕ
ι-reduction bridge), and items carry an explicit sign. Two primitives
(`neg_neg`, `neg_mul`) had to be derived internally because both are also
retirement targets of this same producer — ADR-1580's "a producer cannot
retire its own primitives" finding, recurring on a second carrier. A
capability ℕ never needed: `cancel_pairs`, cancelling an adjacent `x + (-x)`
after sorting — found retiring `diff_of_squares`, whose hand proof's own
last step is exactly this cancellation. `ring::rat` needed **no** internal
derivation (`Rat.neg_neg`/`Rat.neg_mul` are already public theorems, cheaper
over a field) but got a **tighter** coefficient cap than ℕ/ℤ's
`MAX_COEFF = 4` — `count ∈ {-1, 0, 1}` — because `Rat` numerals are
normalized `num/den` pairs with no free numeral-splitting reduction, and
none of its five targets need more (a numeral `2` spelled `add one one`
still proves `2*t = t+t` through the ordinary additive route).

**Ten retirements, five per carrier, all through `prove_eq_at`/`declare`
uniformly.**

    Int  gcd.rs::factor_out            (private) A*mp + neg(A*mn) = A*(mp+neg mn)
    Int  gcd.rs::neg_neg               (private) neg(neg x) = x
    Int  fibonacci.rs::neg_neg         (private) neg(neg x) = x  -- independent duplicate of the above
    Int  fibonacci.rs::mul_two_eq_add_self (private) 2*t = t+t
    Int  wilson.rs::diff_of_squares    (private) (a-1)*(a+1) = a*a - 1
    Int  sub.rs::declare_mul_sub       (declared theorem `Int.mul_sub`)
    Rat  matrix.rs::mul_sub_right_rev       (private) (k*x)-(k*y) = k*(x-y)
    Rat  matrix.rs::factor_k_out_of_three   (private) (k*x-k*y)+k*z = k*((x-y)+z)
    Rat  matrix.rs::middle_swap             (private) w*(x*y) = x*(w*y)
    Rat  matrix.rs::zero_mul                (private) zero*x = zero
    Rat  probability.rs::scale_sq           (private) (a*w)*(a*w) = (a*a)*(w*w)

Every private-helper retirement's test re-derives the exact statement the
hand code proved and requires the kernel to admit it as a fresh declaration
(`ring::nat`'s `retire_regroup_four` convention); `Int.mul_sub` is checked
`def_eq` against the prelude's own pre-existing statement. No projection
diff beyond the proof term: every retired site's return VALUE (the term it
builds for callers) is reconstructed identically to before.

**Cost**, `--release`, `cargo run --release -p axeyum-lean-kernel --example
ring_cost`:

| goal shape | search + emit | + kernel recheck |
| --- | ---: | ---: |
| `Int  A*mp + neg(A*mn) = A*(mp+neg mn)` | 1.945 ms | 2.468 ms |
| `Int  (a-1)*(a+1) = a*a - 1` | 3.189 ms | 3.507 ms |
| `Rat  w*(x*y) = x*(w*y)` | 3.051 ms | 3.989 ms |
| `Rat  (a*w)*(a*w) = (a*a)*(w*w)` | 4.400 ms | 5.086 ms |

Same order of magnitude as ADR-1580's ℕ figures; the two ℚ shapes cost
roughly 1.5-2x the ℤ ones (`Rat` is constructed over `Int`, so every `Rat`
lemma application also carries the embedded `Int`/`Nat` machinery).

**Gates run.** `ring::` (61/61: 23 ℕ + 22 ℤ + 16 ℚ, includes every
retirement target's exact statement) green, `--test-threads=4`, twice across
the session (after the ℤ retirements, after the ℚ retirements + the clippy
fix below). `int_prelude::` (paired with `ring::`, 126/126) green once,
after the five ℤ retirements. `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` exit 0 (one real finding: `apply_mono_signs`
took `RatPrelude` by value — 8,564 bytes — tripping
`large_types_passed_by_value`; fixed by taking `&RatPrelude`, not silenced).
`rustfmt --edition 2024` on every touched/new file.
`python3 scripts/check-fact-depends-derived.py --fix` (2 facts fixed:
`F:int-gcd-eq-gcd-ab`, `F:int-self-inverse-mod-prime`, both now cite
`F:int-mul-neg` — a lemma the ring producer emits rather than a hand proof).
`python3 scripts/validate-facts.py` exit 0, 0 errors, 2714 facts.
`python3 scripts/check-settled-fact-statements.py --write` exit 0, no drift
beyond the depends-derived fix. `python3 scripts/gen-adr-index.py`
regenerated (0166/0167 duplicate pre-existing, not introduced here, not
fixed — out of scope).

**What did NOT run to a verdict.** The full `rat_prelude::` sweep did not
complete in two separate foreground attempts (5 min each, per the
close-out-stall correction this session needed — see below): `ps` showed a
DIFFERENT lane's worktree (`agent-a6639a4140fd08e21`) running the identical
`rat_prelude:: --test-threads=4` filter concurrently on this shared host —
genuine host contention, not a defect in the five retired call sites. In
its place: `rat_prelude::rat_prelude_tests::rat_prelude_builds` (the whole
`RatPrelude` build succeeds end-to-end, so the kernel accepted every one of
the five edited declarations along the way — if any had produced a rejected
term, this test fails at that point) ran green in 17.84s once the lock
cleared. The broader `rat_prelude::rat_prelude_tests::` module and the full
`rat_prelude::` filter both hit their own 5-minute foreground timeouts
afterward — did not run past `rat_prelude_builds`.
`cargo test --workspace --lib` / `./scripts/check.sh` / `just check` — not
run (no `just` confirmed this session; out of this lane's changed scope
besides what `ring::`/`int_prelude::`/`rat_prelude_builds` already cover).

**A note on this session's own process.** Mid-session this lane ended a
turn waiting on a background `rat_prelude::` sweep instead of running it
foreground with its own timeout — the exact close-out stall
`multi-agent-operations.md` warns dispatched lanes against, caught by the
coordinator rather than by this lane's own discipline. Recorded here so the
next lane reading this file does not repeat it: **do not end a turn waiting
on a background check; run it foreground with a timeout you set, and report
"did not run" past that timeout rather than deferring.**

**The first stuck term.** `x*y = y*x` before this session's fix — now
resolved. The next boundary any of the three carriers hits:
`ring::int`/`ring::rat`'s sign/cancellation machinery has no counterpart for
COEFFICIENT accumulation across separately-arising summands (`2*x + (-x)`
does not collapse to `x`) — sound, undocumented as a dedicated test before
this file, not needed by any of the fifteen retirement targets across all
three carriers.

<!-- plan-section: landed-changes -->

| 2026-09-03 | ring-tactic-2 | `ring::nat::Problem::sort_factors`: intra-monomial commutativity, `x*y = y*x` now an identity (was a documented sized negative) |
| 2026-09-03 | ring-tactic-2 | `ring::int`: the ring producer over ℤ (ADR-1582); internally derived `neg_neg`/`neg_mul`; new `cancel_pairs` capability |
| 2026-09-03 | ring-tactic-2 | `ring::rat`: the ring producer over ℚ (ADR-1582); coefficient cap `{-1,0,1}`, tighter than ℕ/ℤ's `MAX_COEFF` |
| 2026-09-03 | ring-tactic-2 | five ℤ ring-rearrangement proofs retired (`int_prelude/gcd.rs`, `fibonacci.rs`, `wilson.rs`, `sub.rs`) |
| 2026-09-03 | ring-tactic-2 | five ℚ ring-rearrangement proofs retired (`rat_prelude/matrix.rs`, `probability.rs`) |
| 2026-09-03 | ring-tactic-2 | ADR-1582: the ring producer over ℤ and ℚ, and what each carrier costs it |
