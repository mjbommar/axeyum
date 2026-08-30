# Lane: log-clog-finish — finishing the `nat-log` / `nat-clog` mirrors

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (3 of 5 remaining log/clog mirrors closed --
log_le_clog, log_lt_self, log_antitone_left; 2 remain open with precise
obstacles below -- clog_antitone_left needs a genuinely new
ceiling-division-monotonicity lemma with a nontrivial numerator-form
bridging identity; log2_eq_log_two needs a new WellFounded.fix-based
Nat.log2 definition from scratch plus evaluation tests plus a mirror-flip
check)`, log-clog-finish, 2026-08-30).**

Picked up from `docs/plan/status/330-nat-log-mirrors.md`'s handoff (9 of 14
`nat-log`/`nat-clog` mirrors closed there). This lane closed 3 of the
remaining 5.

## Closed: 3 of 5

All in `crates/axeyum-lean-kernel/src/nat_prelude/log_clog_order.rs`.

- **`Nat.log_le_clog : ∀ b n, Le (log b n) (clog b n)`.** New
  `Nat.log_aux_le_clog_aux : ∀ b f n, Le (logAux b f n) (clogAux b f n)` —
  the two aux FAMILIES compared at a SHARED fuel (both `log`/`clog` are
  diagonal at `f := n`, unlike `log_aux_mono`/`clog_aux_mono`, which compare
  one family against itself at two DIFFERENT fuels). Induction on `f` (`n`
  generalized inside the motive), splitting on three booleans: `2 ≤ b`
  (log's inner cut, clog's outer cut — the SAME test), `b ≤ n` (log's outer
  cut only), `2 ≤ n` (clog's inner cut, derived from the first two via
  `le_trans` rather than split independently). New small helper
  `n_le_add_sub_one : Le n (sub (add n base) 1)` for `Le 1 base`
  (`add_le_add_left` then `pred_le_pred`, using that `sub x 1` is
  definitionally `pred x`), giving `n/b ≤ (n+b-1)/b` via `div_le_div_right`;
  the hard leaf chains the induction hypothesis at `n/b` through
  `clog_aux_mono` via `le_trans`, then `le_succ_succ`.

- **`Nat.log_lt_self : ∀ b x, x ≠ 0 → Lt (log b x) x`.** New
  `Nat.div_lt_self : Lt 0 n → Lt 1 b → Lt (div n b) n` (infrastructure, via
  `mul_lt_mul_right`'s backward direction plus `one_mul` then
  `div_lt_of_lt_mul`), and `Nat.log_aux_lt_of_pos : ∀ b f n, Le n f → n ≠ 0
  → Lt (logAux b f n) n` — **structural** induction on the fuel `f`, NOT
  well-founded recursion on `n` as the prior handoff sized it: `predecessor`
  is always sufficient fuel for `n/b`, since `div_lt_self` plus `Le n (succ
  predecessor)` gives `Lt (n/b) (succ predecessor)`, hence `Le (n/b)
  predecessor` via `le_of_lt_succ`. The hard leaf splits on whether `n/b` is
  `0` using `Nat.zero_or_succ` + `Or.rec` — **not** a `cases_zero_succ`/
  `Nat.rec` elimination directly on `n/b`, which would discard the
  connection between the exposed predecessor and the `n/b` expression every
  other derived fact (`le_q_pred`, `div_lt`) is stated about (the same
  "carry the equality explicitly" pattern `base_induction.rs`'s `qv_motive`
  uses — this cost one design iteration to get right). New private helper
  `log_aux_zero_value : Eq (logAux base fuel zero) zero` for any `fuel`
  given `Lt 0 base`, via ONE `bool_transport` at the OUTER guard's
  known-false evidence (`ble base zero = false` whenever `base > 0`) —
  collapses the whole term regardless of the inner guard, unlike the
  `log_aux_le_clog_aux` false-branch which needs `bool_select_nat_same`
  because there the known-false cut is the INNER one.

- **`Nat.log_antitone_left : ∀ {n}, AntitoneOn (fun b => log b n) (Set.Ioi
  1)`.** Confirmed the prior handoff's correction: no kernel `Set` type
  needed, `AntitoneOn`/`Set.Ioi` are Mathlib pointwise `def`s exactly like
  `Monotone`. New `Nat.div_le_div_left : Lt 0 a → Le a b → Le (div n b) (div
  n a)` — the mirror image of `div_le_div_right`, monotone DECREASING in the
  divisor. Case-splits `a` via `zero_or_succ` + `Or.rec` (contradiction at
  `a = 0`; reconstructs the `div_mod_lt_mul_iff`/`lt_succ_self`/
  `div_lt_of_lt_mul` chain at `a = succ k`, with the varying factor moved to
  the LEFT of the product via `mul_le_mul_left` + `mul_comm` twice, since
  `div_le_div_right`'s fixed factor is already on the left and this one
  isn't). New `Nat.log_aux_antitone_base : ∀ f n a b, Le a b → Lt 1 a → Lt 1
  b → Le (logAux b f n) (logAux a f n)` — monotonicity in the BASE with the
  value fixed, a materially different induction from `log_aux_mono` (base
  fixed, fuel/value varying): induction on the SHARED fuel (both sides
  diagonal at the same `n`). Because `1 < a`/`1 < b` are hypotheses of the
  statement itself, each side's inner `2 ≤ base` cut is already known true
  unconditionally — no case split on it. Only `b ≤ n` is split: `false`
  collapses the b-side to `0` regardless of the a-side (`zero_le` closes it,
  the a-side's value never inspected); `true` derives `a ≤ n` via
  `le_trans`, so the a-side's cut is true too. The recursive step compares
  `logAux b f' (n/b)` against `logAux a f' (n/a)` — different values at
  different bases — via `IH(n/b, a, b)` (bases at the SAME value `n/b`)
  chained through `log_aux_mono` at the SAME base `a` (values `n/b ≤ n/a`
  from `div_le_div_left`) and `le_trans`, then `le_succ_succ`.
  `Nat.log_antitone_left` is the diagonal `f := n`.

  **A build-order/arity bug cost one round-trip**, worth flagging: the first
  attempt at `declare_log_antitone_left`'s proof body applied
  `log_aux_antitone_base` at `[n, a, b, hab, ha, hb]` — missing the
  diagonal `f := n` argument (`log_aux_antitone_base`'s arity is 1, just
  `f`; `n` is a SEPARATE Pi-bound variable inside the motive, so the call
  needs `[n, n, a, b, hab, ha, hb]`, `f` and the diagonal `n` both). Off by
  one argument shifted every later argument into the wrong slot, poisoning
  all 181 `nat_prelude::` tests with one `TypeMismatch { expected:
  ExprId(3), ... }` (a tiny `expected` id — the sort-error tell). Isolated
  in one step by disabling the `declare_log_antitone_left` call and
  re-running a single fast test (the standing bisection rule), which
  immediately narrowed it to that declaration rather than
  `log_aux_antitone_base` itself.

**A fact-ledger paren-count bug caught by actually RUNNING the
checker_command, not just building it by string-substitution.** The first
draft of `F:ml430-nat-log-antitone-left`'s `checker_command` copied the
SAME wrapped string used for `kernel_statement`'s `"theorem X : (...)"`
suffix into the `checker_command`'s raw `$3` match — but `checker_command`
must match the UNWRAPPED `nat_theorem_inventory` column value, one fewer
leading/trailing paren than `kernel_statement`'s display form. Running the
checker (not eyeballing it) caught this before commit; the other two new
facts' checker_commands were verified the same way and were already
correct.

## Open: 2 of 5, with scoped obstacles

**`F:ml430-nat-clog-antitone-left-44a87771` (`AntitoneOn (fun b => clog b
n) (Set.Ioi 1)`) — needs a genuinely new ceiling-division-monotonicity
lemma.** `clog`'s guard structure is actually SIMPLER than `log`'s for this
purpose (both booleans — `2 ≤ base` outer, `2 ≤ n` inner — are either
unconditionally true from `ha`/`hb`, or the SAME shared expression `ble 2
n` on both sides, so no `le_trans`-derived cross-side fact is needed at
all). The blocker is purely arithmetic: the recursive step needs `Le
((n+b-1)/b) ((n+a-1)/a)` for `a ≤ b`, `1 < a` — ceiling-division
monotonicity, NOT covered by `div_le_div_left` (floor division), because
the numerators `n+b-1` and `n+a-1` also differ (not the same numerator `n`
as in the floor case).

The natural route: `Nat.add_div_right : ∀ x z, 0 < z → (x+z)/z = x/z+1`
already exists (`div_mod_lemmas.rs`) and would let `(n+base-1)/base` reduce
to `(n-1)/base + 1` (for `n ≥ 1`), turning the ceiling comparison into a
FLOOR comparison at the SAME numerator `n-1`, closable by `div_le_div_left`
directly. But `add_div_right`'s numerator is `x + z` (`z` bare, addend on
the RIGHT), while `clog`'s stored numerator is `sub (add n base) 1` — `(n +
base) - 1`, not `(n - 1) + base`. These are propositionally equal (for `n ≥
1`) but NOT the same expression, and no bridging equality between `(n +
base) - 1` and `(n - 1) + base` was found or built by this lane. Building
one needs either an `add_sub_assoc`-shaped lemma (if it exists elsewhere —
not checked exhaustively) or a fresh derivation via `pred`/`succ` identities
(care needed: `Nat.add` recurses on its RIGHT argument, so `pred (n +
base)` does not obviously relate to `pred n + base` by defeq alone for
symbolic `base` — check which argument the relevant reduction needs
constructor-shaped before assuming either direction reduces).

Sizing: comparable to `div_le_div_left` (one new arithmetic lemma) plus
`log_aux_antitone_base` transported to `clogAux` (mechanical once the
arithmetic lemma exists, following this lane's `log_aux_antitone_base`
almost line-for-line since `clog`'s guard nesting is simpler). Not
attempted here for lack of remaining budget, not for lack of a route.

**`F:ml430-nat-log2-eq-log-two-28085932` (`n.log2 = Nat.log 2 n`) —
`Nat.log2` does not exist in this kernel.** Unchanged from the prior
handoff's assessment: it is Lean CORE (not Mathlib), defined by
well-founded recursion on a `log2`-style measure with a DEPENDENT motive.
This kernel HAS `WellFounded.fix.{u,v}` with a checked `fix_eq` (used by
`gcd`, `bezout_witnesses`, `modeq`, `wilson`, `base_induction`), so this is
NOT permanently blocked — but building `Nat.log2` the well-founded way,
proving its equation lemmas, adding evaluation tests at concrete small
arguments (CLAUDE.md: the kernel cannot tell a `Definition` is WRONG, only
type-correct — a function returning garbage still type-checks), and then
applying the mirror-flip criterion (does our body match what Mathlib
*defines*, or only what Mathlib *proves* about a structurally different
`def`?) against Mathlib's actual `Nat.log2` source at the pinned commit —
none of this was attempted here. Comparable in size to standing up a new
recursive definition plus its infrastructure from scratch; not a small
increment.

## Verification, all run in the foreground

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 181 passed, 0
  failed throughout (recounted `the_build_is_deterministic`'s pin four
  times by RUNNING the test and reading the reported value, never by
  hand-incrementing: 93+598 → 93+600 → 93+603 → 93+604 → 93+606, +8
  theorems total across the four commits below).
- `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D
  warnings` — clean (one `doc_markdown` fix needed: an unbackticked
  identifier in a doc comment).
- `rustfmt --edition 2024` on every touched file; `cargo fmt --all --check`
  clean at the end.
- `python3 scripts/validate-facts.py` — 2220 facts, 0 errors (checked after
  each fact flip).
- `python3 scripts/check-fact-depends-derived.py --fix` — nothing to fix,
  each time.
- Every new `checker_command` verified by ACTUALLY RUNNING it (not just
  eyeballing the string), both directions (`/usr/bin/grep -cE` against a
  fresh `nat_theorem_inventory` TSV: the real name/type pair matches
  exactly once, the same query with an `XYZFAKE`-suffixed name matches zero
  times) — this is what caught the paren-count bug above.
- `bash scripts/check-merge-hygiene.sh` —
  `MERGE_HYGIENE|markers=0|adr_index=ok|generated=current|pinned_inventories=n/a
  (no live pin sites; see the note above)|PASS`.
- No `cargo test --workspace` / `./scripts/check.sh` run (per this lane's
  brief) — the coordinator re-verifies before merging.

## Facts flipped

- `F:ml430-nat-log-le-clog-ac8ab2d4` → `proved`
- `F:ml430-nat-log-lt-self-529f89fa` → `proved`
- `F:ml430-nat-log-antitone-left-20d1326c` → `proved`

## Files

- `crates/axeyum-lean-kernel/src/nat_prelude/log_clog_order.rs` (+8 new
  declarations: `n_le_add_sub_one`, `log_aux_le_clog_aux`, `log_le_clog`,
  `div_lt_self`, `log_aux_zero_value`, `log_aux_lt_of_pos`, `log_lt_self`,
  `div_le_div_left`, `log_aux_antitone_base`, `log_antitone_left` — ten
  actually, listing corrected)
- `crates/axeyum-lean-kernel/src/nat_prelude.rs` (10 new `NameId` fields +
  `name_str` entries + 8 new `declare_*` calls appended to
  `declare_log_clog_order_all`)
- `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs`
  (`theorem_names` +8, `the_build_is_deterministic`'s pin recounted four
  times to `93 + 606`)
- 3 fact files under `artifacts/facts/F-ml430-nat-log-{le-clog,lt-self,antitone-left}-*.json`
