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

Detail moved to [`../notes/350-clog-log2-finish.md`](../notes/350-clog-log2-finish.md).

