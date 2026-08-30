# Lane: clog-log2-finish — the last two `nat-log`/`nat-clog` mirrors

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (both remaining facts closed --
clog_antitone_left, log2_eq_log_two; the 14-of-14 nat-log/nat-clog mirror
set started in 330-nat-log-mirrors.md is now complete)`, clog-log2-finish,
2026-08-30).**

Picked up from `docs/plan/status/337-log-clog-finish.md`'s handoff (12 of 14
`nat-log`/`nat-clog` mirrors closed there). This lane closed the remaining 2.

## Closed: 2 of 2

### `Nat.clog_antitone_left`

`Nat.clog_aux_antitone_base : ∀ f n a b, Le a b → Lt 1 a → Lt 1 b → Le
(clogAux b f n) (clogAux a f n)` in
`crates/axeyum-lean-kernel/src/nat_prelude/log_clog_order.rs`, mirroring
`log_aux_antitone_base` with the two guard cuts SWAPPED: `clogAux`'s outer
cut (`2 ≤ base`) is a pure base cut, individually known true from `ha`/`hb`
with no case split; its inner cut (`2 ≤ n`) is the SAME expression on both
sides (the value is fixed), needing exactly one case split instead of log's
two.

The `(n+b-1)`/`(n-1)+b` bridge **DID need a hypothesis** (`Le 1 n`) — the
handoff correctly flagged this. `Nat.sub` truncates: at `n = 0`, `sub(add(n,
base),1) = base - 1` while `add(sub(n,1),base) = base`, differing by exactly
one. New private helper `add_sub_one_swap` proves the bridge given `Le 1 n`
by reconstructing `n` as `succ (pred n)` via `succ_pred_of_pos` (passed
directly where `Lt 0 n` is expected — DEFEQ through `Nat.lt`'s definition,
the same subsumption `NatOps::zero_lt_succ`'s callers already rely on), then
cancelling the `succ` against the literal `1` on both sides via
`succ_add`/`succ_sub_succ`/`sub_zero`. A second helper, `ceil_div_succ_of_pos`,
composes this with the existing `Nat.add_div_right` to rewrite each side's
ceiling quotient to `(n-1)/base + 1`, turning the comparison into a floor
comparison at the shared numerator `n-1` (`div_le_div_left` +
`add_le_add_right`). From there the composition is `log_aux_antitone_base`'s:
IH at the SAME bases with the b-side's quotient, chained through
`clog_aux_mono` at the fixed base `a`, `le_trans`, then `le_succ_succ`.

`Nat.clog_antitone_left` is the diagonal `f := n`, exactly mirroring
`declare_log_antitone_left`.

### `Nat.log2_eq_log_two`

`Nat.log2` did NOT need a `WellFounded.fix` construction, contrary to two
prior handoffs' assessment (`330-nat-log-mirrors.md`'s original and
`337-log-clog-finish.md`'s repetition of it — **neither had actually read the
Lean source**). Read directly from the pinned toolchain
(`~/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Init/Data/Nat/Log2.lean`,
already provisioned on this host — `scripts/provision-lean-import-toolchain.sh
--verify` needs no network) before writing any code:

```lean
def log2 (n : Nat) : Nat :=
  n.rec (fun _ => nat_lit 0)
        (fun _ ih n => ((nat_lit 2).ble n).rec (nat_lit 0) ((ih (n.div (nat_lit 2))).succ))
        n
```

This is a **fuel-recursive `Nat.rec` with a NON-DEPENDENT motive `fun _ =>
Nat → Nat`, fuel = the value itself (diagonal), single guard `2 ≤ n`** —
exactly this prelude's own `log`/`logAux` device (fuel argument second,
motive the constant row `fun _ => Nat → Nat`), specialized to the LITERAL
base `2`: `logAux`'s recursive step `if b ≤ n then (if 2 ≤ b then succ
(logAux b f (n/b)) else 0) else 0` has its inner cut `2 ≤ b` become `2 ≤ 2`
at `b := 2`, a literal-literal `Nat.ble` comparison that reduces to
`Bool.true` by ι alone (independent of `f`/`n`), collapsing the whole guard
to the single outer cut `2 ≤ n` — Lean core's own `log2_def` equation,
verbatim. Confirmed against `log2`'s own doc-comment examples (`log2 0=0,
1=0, 2=1, 4=2, 7=2, 8=3`) BEFORE writing any code, and again as a kernel
evaluation test at seven concrete points plus a negative control.

**Mirror-flip determination: honest flip.** Lean core *defines* `log2` the
same way this prelude's `log` already works — it is not a *theorem* about a
structurally different `def`. So `Nat.log2` is declared directly as `fun n
=> Nat.log 2 n` (`crates/axeyum-lean-kernel/src/nat_prelude/log2.rs`) rather
than re-deriving a second, independent fuel recursor. This makes
`Nat.log2_eq_log_two` a **one-line `Eq.refl`** — Mathlib's own proof of the
same statement (`Mathlib/Data/Nat/Log.lean:309`) is not this short, because
ITS `Nat.log` is well-founded recursion, a genuinely different recursion
principle from ITS `log2` (its proof goes through `eq_of_forall_le_iff` plus
`le_log2`/`le_log_iff_pow_le`); this prelude's `Nat.log` is already
fuel-recursive at every base, so the two collapse to the identical term by
construction and no such argument is needed here.

## Verification, all run in the foreground

- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib nat_prelude::`
  — 189 passed after `clog_antitone_left` (+8 over the prior handoff's 181:
  `one_le_of_two_le`/`add_sub_one_swap`/`ceil_div_succ_of_pos` are private
  helpers, not registered theorems, so only `clog_aux_antitone_base` and
  `clog_antitone_left` add entries to `theorem_names`/`definition_names`,
  but the coverage assertion itself is one test), then 190 passed after
  `log2_eq_log_two` (+1 new `#[test]`,
  `log2_computes_and_equals_log_two`) — both times 0 failed.
- `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D
  warnings` — clean.
- `rustfmt --edition 2024` on every touched file; `cargo fmt --all --check`
  clean.
- `python3 scripts/validate-facts.py` — 2220 facts, 0 errors, checked after
  each fact flip (`open` count read `147` right after the `clog_antitone_left`
  flip and `146` right after the `log2_eq_log_two` flip — one lower each
  time, as expected).
- `python3 scripts/check-fact-depends-derived.py --fix` — nothing to fix,
  each time.
- Every new `checker_command` verified by ACTUALLY RUNNING it, both
  directions (`/usr/bin/grep -cE` against a fresh `nat_theorem_inventory`
  TSV: exactly one match on the real name/type pair, zero on an
  `XYZFAKE`-suffixed name).
- `bash scripts/check-merge-hygiene.sh` — see the line reported at the end
  of this lane's final message.
- No `cargo test --workspace` / `./scripts/check.sh` run (per this lane's
  brief) — the coordinator re-verifies before merging.

## Facts flipped

- `F:ml430-nat-clog-antitone-left-44a87771` → `proved`
- `F:ml430-nat-log2-eq-log-two-28085932` → `proved`

## Files

- `crates/axeyum-lean-kernel/src/nat_prelude/log_clog_order.rs` (+5 new
  items: `one_le_of_two_le`, `add_sub_one_swap`, `ceil_div_succ_of_pos`
  (private helpers) and `declare_clog_aux_antitone_base`/
  `declare_clog_antitone_left`, wired into `declare_log_clog_order_all`)
- `crates/axeyum-lean-kernel/src/nat_prelude/log2.rs` (new file:
  `declare_log2_all`, `Nat.log2` + `Nat.log2_eq_log_two`)
- `crates/axeyum-lean-kernel/src/nat_prelude.rs` (`mod log2;`, 4 new
  `NameId` fields + `name_str` entries, 2 new `declare_*` calls)
- `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs`
  (`definition_names`/`theorem_names` +4, new `#[test]`
  `log2_computes_and_equals_log_two`)
- 2 fact files under
  `artifacts/facts/F-ml430-nat-{clog-antitone-left,log2-eq-log-two}-*.json`

## What this leaves for the next `nat-log`/`nat-clog`-adjacent lane

Nothing — the 14-of-14 mirror set from `330-nat-log-mirrors.md` is closed.
A generalizable finding worth carrying forward: **a handoff's "needs
`WellFounded.fix`" claim about a specific Lean-core/Mathlib definition
should be re-verified by reading the actual source before being repeated a
second time.** Two lanes in a row propagated the same unread claim about
`Nat.log2`; the actual definition needed no new recursion principle at all,
only recognizing that it specializes this prelude's own `log` device at a
literal base.
