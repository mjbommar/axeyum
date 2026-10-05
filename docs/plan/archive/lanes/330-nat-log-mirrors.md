# Lane: nat-log-mirrors — `Nat.log`/`Nat.clog` order mirrors

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (9 of 14 dispatchable log/clog mirrors closed;
5 remain open with a scoped handoff below -- log_le_clog is the cheapest
next target, its whole proof sketch is written out; the two AntitoneOn
facts are NOT blocked by a missing Set type the way this task's brief
assumed, they are blocked by a genuinely new monotonicity-in-the-base
lemma nobody has built)`, nat-log-mirrors, 2026-08-30).**

## Closed: 9 of 14

Four already existed as admitted kernel theorems before this lane started
(built by the `log.rs`/`clog.rs` lane on 2026-08-28, never flipped as `ml430`
mirrors): `Nat.log_one_left`, `Nat.log_one_right`, `Nat.clog_one_left`,
`Nat.clog_one_right`. No new proof work for these four — verified the
rendered kernel type against `formal.statement` character-by-character via
`nat_theorem_inventory --release` and flipped status.

Five are new kernel constructions, all in the new
`crates/axeyum-lean-kernel/src/nat_prelude/log_clog_order.rs`:

- **`Nat.div_le_div_right : ∀ n m b, Le n m → Le (div n b) (div m b)`** —
  infrastructure, not itself a mirror. At `b = 0` both sides are `0`
  (`div_zero`); at `b = succ bp`, `div_lt_of_lt_mul` fed `n ≤ m <
  b*(succ (div m b))` (the upper bound from `div_mod_lt_mul_iff`'s backward
  direction applied to `lt_succ_self`, via the canonical `div_mod_exec`
  witness) gives `div n b < succ (div m b)`, hence `≤` by `le_of_lt_succ`.
  **This did not exist anywhere in the tree** — neither `log.rs` nor
  `clog.rs` needed it before monotonicity.
- **`Nat.log_aux_mono`/`Nat.clog_aux_mono`** — the genuinely hard tier: a
  SINGLE induction on the fuel proves fuel- and value-monotonicity TOGETHER
  (`∀ f, ∀ g n m, f≤g → n≤m → Le (logAux b f n) (logAux b g m)`), with `g`,
  `n`, `m` generalized inside the motive (the same "quantify inside the
  motive" technique `logAux_le_fuel` uses for `n`). The step case
  case-splits the fuel-comparison hypothesis on `g`'s shape (`g = 0` is
  refuted by `not_succ_le_zero`), then reconciles each aux's TWO guard cuts
  against the corresponding comparison on the other side. **New combinator**
  `le_of_bool_select_mono` generalizes `log.rs`'s private `le_of_bool_select`
  from a single shared guard test to two DIFFERENT tests connected by an
  implication — needed because comparing two values makes each side's guard
  a different expression, not the literally-shared test `le_of_bool_select`
  assumes. Applied twice per step (once per guard level), with an identity
  implication where a cut is literally the same test on both sides (`log`'s
  inner `2 ≤ b`, `clog`'s outer `2 ≤ b`) and a derived one where it is not
  (`log`'s outer `b ≤ n`/`b ≤ m` via `le_of_ble_eq_true` + `le_trans` +
  `ble_eq_true_of_le`; `clog`'s inner `2 ≤ n`/`2 ≤ m` the same way).
  `clog_aux_mono`'s recursive-argument monotonicity
  (`(n+b-1)/b ≤ (m+b-1)/b`) comes from `add_le_add_right` then `pred_le_pred`
  (`sub x 1` is definitionally `pred x` — two iota steps through the
  structural definition of `Nat.sub`) then `div_le_div_right`.
- **`Nat.log_mono_right`/`Nat.clog_mono_right`** — `*_aux_mono` at
  `f := n, g := m`, the SAME hypothesis used for both the fuel and value
  comparison, since `log b n := logAux b n n` is diagonal.
- **`Nat.log_monotone`/`Nat.clog_monotone`** — `Monotone f` is Mathlib's own
  `def Monotone (f : α → β) := ∀ x y, x ≤ y → f x ≤ f y`, so with `b` fixed
  first this is the IDENTICAL core rendering as `*_mono_right` — the same
  "core-rendered unfolding" treatment this ledger already gave
  `Nat.choose_mono`. Trivial specialization, no new induction.
- **`Nat.clog_pos : ∀ b n, Lt 1 b → Lt 1 n → Lt 0 (clog b n)`** —
  case-split on `n` (`clog`'s fuel and value are diagonal, so ONE split
  gives both the succ-shaped fuel the unfolding needs and the succ-shaped
  value the guard needs); `n = 0` is refuted by `Lt 1 0` via
  `not_succ_le_zero`. At `n = succ n'` both guard cuts are already known
  TRUE from the hypotheses (`1 < b`/`1 < n` are literally `Le 2 b`/`Le 2 n`
  by defeq), so two direct `bool_transport`s at the known evidence (no case
  split needed — this is simpler than the monotonicity proofs, which don't
  have the evidence in hand ahead of time) reduce `clog b n` to a `succ`,
  positive by `zero_lt_succ`.

**A build-order bug cost one round-trip and is worth flagging for the next
lane that adds a `nat_prelude` module late in the pipeline.**
`declare_log_clog_order_all` used `Nat.div_lt_of_lt_mul`, which the builder
calls **last**, right before `Ok(p)` — my first placement (right after
`declare_clog_all`) referenced it before it existed, poisoning the WHOLE
`nat_prelude::` sweep (`UnknownConst`, all 181 tests failed, none of them
about `log`/`clog`). Fixed by moving the call to the very end of the
builder, after `declare_div_lt_of_lt_mul`. Bisected by disabling everything
in `declare_log_clog_order_all` except one function and re-running a single
fast test — the standing "bisect by toggling declarations" rule from
CLAUDE.md, and it found the answer in one step.

**Verification, all run in the foreground:**
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 181 passed, 0
  failed (was 181 before this lane; net +8 theorems registered in
  `theorem_names`, recounted the list directly rather than hand-incrementing
  the pin: `93 + 584 = 677` definitions+theorems rendered).
- `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D
  warnings` — clean.
- `rustfmt --edition 2024` on the new file.
- `python3 scripts/validate-facts.py` — 2219 facts, 0 errors (ran
  `scripts/check-fact-depends-derived.py --fix` first: two of the new
  theorems directly use other ledger-tracked lemmas in their proof term —
  `Nat.clog_pos` uses `Nat.ble_eq_true_of_le`/`Nat.not_succ_le_zero`/
  `Nat.zero_lt_succ`, `Nat.log_monotone` uses `Nat.log_mono_right` — and
  `depends_on` needed those edges added).
- Every new `checker_command` verified BOTH directions with
  `/usr/bin/grep`-equivalent exact matching (`awk -F'\t'` on the
  `nat_theorem_inventory` TSV, matched on name AND rendered type): the real
  kernel name matches exactly once, and the same query with the name
  suffixed `XYZFAKE` matches zero times, for all 9 facts.

## Open: 5 of 14, with a scoped handoff

**`F:ml430-nat-log-le-clog-ac8ab2d4` (`log b n ≤ clog b n`) — cheapest next
target, full proof sketch below.** Needs a THIRD double induction — this
time comparing the two DIFFERENT aux families (`logAux` vs `clogAux`) rather
than one family against itself — on a SHARED fuel (both diagonal at fuel = n,
so one fuel counter suffices, unlike the two-family monotonicity case).

Sketch of `logAux_le_clogAux : ∀ b f n, Le (logAux b f n) (clogAux b f n)`,
induction on `f`:
- Base `f = 0`: both sides `0`, `le_refl`.
- Step `f = succ f'`, `IH : ∀ n, Le (logAux b f' n) (clogAux b f' n)`. Three
  independent booleans this time, not two: `base_exceeds_one := ble 2 b`
  (log's inner cut, clog's outer cut — literally the SAME test), `base_fits
  := ble b n` (log's outer cut only), `value_exceeds_one := ble 2 n` (clog's
  inner cut only). Case on `base_exceeds_one`:
  - `false`: `clogAux` is `0` (its outer cut). `logAux`'s inner selector is
    the SAME false test, so its inner content is `0` too, and
    `bool_select_nat_same` (already in `ops.rs`) collapses the outer
    `base_fits` selector regardless of its value: `bool_select_nat base_fits
    0 0 = 0`. Both sides `0`.
  - `true`: `logAux` reduces to `bool_select_nat base_fits (succ (logAux b f'
    (n/b))) 0`; `clogAux` reduces to `bool_select_nat value_exceeds_one
    (succ (clogAux b f' ((n+b-1)/b))) 0`. Case on `base_fits`:
    - `false` (`n < b`): LHS is `0`, `zero_le` closes it regardless of RHS.
    - `true` (`b ≤ n`): with `2 ≤ b` (this branch) this gives `2 ≤ n`
      (`le_trans`), so `value_exceeds_one` is TRUE too (derive it the same
      way `clog_pos`/the monotonicity proofs do:
      `ble_eq_true_of_le`/`le_of_ble_eq_true`). Both sides are now
      `succ(...)`; need `Le (logAux b f' (n/b)) (clogAux b f' ((n+b-1)/b))`.
      Chain: `IH` at `n/b` gives `Le (logAux b f' (n/b)) (clogAux b f'
      (n/b))`; `clog_aux_mono` at the SAME fuel `f'` (via `le_refl f'`) and
      `n/b ≤ (n+b-1)/b` (from `n ≤ n+b-1`, itself from `add_le_add_left(n, 2,
      base, ...)`-style reasoning giving `add n 2 ≤ add n base` — defeq to
      `succ (succ n) ≤ add n base` — then `pred_le_pred` and `le_trans`
      through `le_succ`, THEN `div_le_div_right`) gives `Le (clogAux b f'
      (n/b)) (clogAux b f' ((n+b-1)/b))`. Chain the two with `le_trans`,
      then `le_succ_succ`.

  This reuses `le_of_bool_select_mono` for both selector levels (identity
  implication for the shared `base_exceeds_one`, a derived one for
  `base_fits → value_exceeds_one`) and needs ONE new small lemma:
  `Le n (sub (add n base) 1)` for `base ≥ 2` (the `n ≤ n+b-1` step above —
  sketched, not yet built).

**`F:ml430-nat-log-lt-self-529f89fa` (`x ≠ 0 → log b x < x`) — needs strong
(course-of-values) induction, which this lane did not build.** `log_le_self`
(already in the ledger) gives `≤`, not `<`. The standard argument (`b < 2`:
trivial since `log = 0 < x`; `b ≥ 2, x < b`: trivial since `log = 0 < x`;
`b ≥ 2, x ≥ b`: `log b x = log b (x/b) + 1`, and `x/b < x` lets a STRONG
induction hypothesis apply at `x/b`, giving `log b (x/b) < x/b`, hence
`log b x < x/b + 1 ≤ x`) needs a strong-induction principle over `Nat` — the
fuel-based structural induction this file's other proofs use is NOT strong
induction (each step only sees the immediately preceding fuel value's IH,
not an IH for every smaller value). Check whether a strong/course-of-values
induction combinator already exists in `nat_prelude` (this lane did not
search for one) before building one from scratch.

**`F:ml430-nat-log-antitone-left-20d1326c`/`F:ml430-nat-clog-antitone-left-44a87771`
(`AntitoneOn (fun b => log/clog b n) (Set.Ioi 1)`) — corrected finding: the
missing-`Set`-type story this task's brief anticipated is NOT the real
blocker.** This kernel has no `Set` type at all (confirmed: zero hits for
`Set`/`Set.Ioi` outside doc comments across `crates/axeyum-lean-kernel/src`).
But `AntitoneOn f s := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≤ b → f b ≤ f a` and
`x ∈ Set.Ioi c := c < x` are BOTH Mathlib `def`s that unfold to plain
propositions — exactly the same "Mathlib defines it as a pointwise
implication" situation that made `Monotone`/`choose_mono` an honest flip. So
a kernel `Set` type is not actually required; the core rendering
`∀ a b, 1 < a → 1 < b → a ≤ b → log b n ≤ log a n` (note the direction: a
LARGER base gives a SMALLER-or-equal log) would be the honest mirror content,
by the same criterion.

**The real blocker is that this is monotonicity in the BASE with the value
held FIXED, and every induction this lane built is monotonicity in the VALUE
with the base held fixed — a materially different argument.** It needs a new
`div_le_div_left`-shaped lemma (`a ≤ b → n/b ≤ n/a`, monotone DECREASING in
the divisor — the mirror image of `div_le_div_right`, not a corollary of it)
and a new fuel induction comparing `logAux a f n` against `logAux b g n` for
`a ≤ b` at a FIXED `n`. Correct this lane's sizing if you dispatch it: it is
comparable in size to `log_aux_mono`, not blocked by kernel capability.

**`F:ml430-nat-log2-eq-log-two-28085932` (`n.log2 = Nat.log 2 n`) — `Nat.log2`
<!-- was-absent: Nat.log2 -->
does not exist in this kernel at all.** It is Lean CORE (not Mathlib), and
its real definition is well-founded recursion on a `log2`-style measure —
structurally the same shape CLAUDE.md's `binaryRec` correction covers: a FUEL
encoding's non-dependence is forced, but this kernel DOES have
`WellFounded.fix` (used by `gcd`/`bezout_witnesses`/`modeq`/`wilson`), so
defining `Nat.log2` the well-founded way is not permanently blocked — it is
simply undone work, comparable in size to standing up a new recursive
definition plus its equation lemmas, which this lane did not attempt.

## Files

- `crates/axeyum-lean-kernel/src/nat_prelude/log_clog_order.rs` (new)
- `crates/axeyum-lean-kernel/src/nat_prelude.rs` (9 new `NameId` fields +
  `name_str` entries + one `declare_log_clog_order_all` call, moved to the
  very end of the builder)
- `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs`
  (`theorem_names` +8, `the_build_is_deterministic`'s pinned count
  recounted to `93 + 584`)
- 9 fact files under `artifacts/facts/F-ml430-nat-{log,clog}-*.json`
