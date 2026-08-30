# Notes: 190-int-modeq

Detail moved out of [`../status/190-int-modeq.md`](../status/190-int-modeq.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**What landed as a GENERALIZATION vs a new proof.** `add_right`/`add_left`
were REPLACED in place (not duplicated) — no other file in the tree called
the old 5-argument (`0<n`-carrying) signature, confirmed by grep before
touching them. The other five facts (`add_left_cancel`, `neg`,
`neg_modEq_neg`, `of_dvd`, `dvd_iff`, `of_mul_left`) are new declarations
built on `modeq_to_dvd`/`dvd_to_modeq` plus a handful of small ring-algebra
helpers (`ineg_neg`, `ineg_add`, `cancel_neg_add_left`, `eq_add_sub`).
`neg_modEq_neg` is stated as a genuine `Iff` (this kernel's `Iff.intro`,
already used by `modEq_iff_dvd` itself) rather than split into two
declarations — a stale doc comment elsewhere in `modeq_family.rs` claims "no
`Iff` in this kernel"; that's wrong, or at least not a constraint here.

**What the kernel REJECTED and why.** Nothing, on the version committed —
but two earlier drafts did not reach `add_declaration` at all: a first pass
at `ineg_neg` tried to isolate `neg(neg a)` from `Int.add_neg(neg_a)` via
`eq_solve_right`-style algebra and produced a circular identity (`nn_a =
izero + nn_a`) before I even built the term, because the tool I was
composing solves for the wrong variable when the target itself appears
negated on the right. Re-derived via `eq_neg_of_add_eq_zero` instead
(`x+y=0 → x=neg y`), which does isolate the right variable. Second, my first
`dvd_to_modeq` draft used `d.irefl` to "bridge" `Int.sub b a` and the raw
`add b (neg a)` form by hand; unnecessary — `itrans`/`icongr` already accept
a mismatch between the two forms via the kernel's own defeq check at
`add_declaration` time, exactly the `state folded, prove unfolded` idiom
`sub.rs`'s module doc already documents, and the ORIGINAL `modEq_iff_dvd`
already relies on. Simplified to rely on that instead once I re-read it.

**Did dropping positivity break any existing caller?** No. `grep` for
`mod_eq_add_right`/`mod_eq_add_left` across `int_prelude/*.rs` before editing
found exactly two non-definition sites: inside `declare_modeq_add_left`
itself (rewritten) and `int_prelude_tests.rs` (mine). `mod_eq_mul_left`/
`mul_right` (which `wilson.rs` calls heavily with an explicit `h_pos`
argument) were NOT touched — out of scope, and the fact ledger backlog never
asked for them.

**`int_prelude::` count.** 34/34 both before and after (one new test would
have made 35, but no test was added — coverage runs through the two
existing environment-derived assertions,
`every_int_declaration_is_checked_and_axiom_free` and
`derived_laws_have_no_axiom_footprint`, which is exactly the point of those
two tests: a new `declare_*` needs no bespoke test of its own to be checked).
`derived_laws`' pin recounted 132 → 138 (counted `^\s*p\.` lines in the
array body, not hand-incremented) for the six brand-new names (`add_right`/
`add_left` were already listed).

Verified foreground: `cargo test -p axeyum-lean-kernel --lib int_prelude::`
— 34 passed, 0 failed. Each of the seven facts' `checker_command`
(`int_theorem_inventory`, `--release`, grep'd for a THEOREM row with an
EMPTY footprint column) run individually against the built
`target/release/examples/int_theorem_inventory` binary, all `-ge 1`.
`python3 scripts/validate-facts.py`: 0 errors.

Did not run: `just check` / `./scripts/check.sh` (out of scope for a
single-crate change and multi-lane host contention; the coordinator's
merge gate re-verifies).
