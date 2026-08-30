# Lane: int-modeq — closing the `Int.ModEq` congruence backlog left by `int-modeq-kernel`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, int-modeq, 2026-08-28).** Closed all seven
backlog facts (`docs/plan/status/int-modeq-kernel.md` had flagged six of
these — `modeq-add-left`, `modeq-add-left-cancel`, `modeq-dvd-iff`,
`modeq-neg`, `modeq-of-dvd`, `modeq-of-mul-left` — as "not attempted…a
well-scoped next task"; the seventh, `neg-modeq-neg`, was the `Iff` around
`modeq-neg`).

**The hypothesis-mismatch finding was correct.** `declare_modeq_add_left`/
`declare_modeq_add_right` (`int_prelude/modeq.rs`) carried a `0 < n`
hypothesis Mathlib's `Int.ModEq.add_left`/`add_right` do not have. Verified
by reading the declared TYPE (`d.ilt(zero, n)` appears in `pos_ty`, which is
threaded into `stmt` via `d.arrow(pos_ty, inner_arrow)` — not just a local
proof-term detail) and by instantiating at `n = 0` and `n = -3`: the Mathlib
statement holds at both, unconditionally.

**Root cause, and why it generalizes past these two facts.** Re-reading
`declare_modeq_iff_dvd`'s `mp` half (`ModEq n a b → dvd n (b-a)`) shows
`h_pos`/`n_ne_zero` are used ONLY by `mpr` (which needs
`ediv_emod_unique`'s `0<=r<n` uniqueness bound, itself proved positive-only).
`mp` never touches either — it was scoped under `0 < n` only because it was
declared alongside `mpr` inside one `Iff`, not because it needs it. Extracted
as `modeq_to_dvd`, unconditional in `n`.

The converse (`dvd n (b-a) → ModEq n a b`) is ALSO unconditional, but via a
DIFFERENT route than `mpr`'s: a witness `c` with `b-a=n*c` gives `b=n*c+a`
directly (`cancel_neg_add`), and `Int.modEq_add_mul_left : ModEq n (n*q+a) a`
— already unconditional, built by `int-modeq-kernel` — closes it with no
bound at all. Extracted as `dvd_to_modeq`. So BOTH halves of the bridge are
unconditional; `0 < n` on the old `Iff` declaration was solely a proof-route
artifact of routing the converse through `ediv_emod_unique` instead of
`modEq_add_mul_left`.

Detail moved to [`../notes/190-int-modeq.md`](../notes/190-int-modeq.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | int-modeq | `Int.ModEq.add_left`/`add_right` generalized to drop `0<n` (Mathlib parity); five new unconditional facts (`add_left_cancel`, `neg`, `neg_modEq_neg`, `of_dvd`, `dvd_iff`, `of_mul_left`) landed via two new helpers `modeq_to_dvd`/`dvd_to_modeq`; all seven backlog facts flipped `open`→`proved`, axiom-free |
