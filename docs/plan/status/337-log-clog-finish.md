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

Detail moved to [`../notes/337-log-clog-finish.md`](../notes/337-log-clog-finish.md).

