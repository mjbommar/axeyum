# Notes: 324-ipc-soundness

Detail moved out of [`../status/324-ipc-soundness.md`](../status/324-ipc-soundness.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Whether the sat-shaped statement happens to be *true* for this algebra is a
separate question from whether it carries an induction. A brute-force search
over every formula of depth ≤ 2 in two variables found no counterexample, so it
may well be true; nothing here claims it.

## The eleven cases, and what each needed

All eleven checked **on the first attempt**. One minor premise of `Provable.rec`
each — the first use of that generated recursor anywhere.

| rule | closed by |
| --- | --- |
| `ax_head` | `ipc_meet3_le_left` |
| `weaken` | `ipc_meet3_le_right` + `le_trans` |
| `and_intro` | `ipc_le_meet3` |
| `and_elim1` / `and_elim2` | `ipc_meet3_le_left` / `_right` + `le_trans` |
| `or_intro1` / `or_intro2` | `ipc_le_join3_left` / `_right` + `le_trans` |
| `or_elim` | `ipc_or_elim_chain` (linearity) |
| `imp_intro` | `ipc_himp3_intro` (residuation) + `ipc_ctx_meet_le_top` |
| `imp_elim` | `ipc_himp3_elim` |
| `bot_elim` | `zero_le` + `le_trans` |

**Residuation needs `ipc_ctx_meet <= 2`, and that is a real side condition, not
decoration.** It fails at `m = 3`: `meet3 3 1 = 1 <= 1`, but
`3 <= himp3 1 1 = 2` is false. Found by brute-forcing all of `{0..4}³` before
writing any Rust, which is also what confirmed `or_elim` needs no such
condition (0 failures over the same range). `ipc_ctx_meet_le_top` discharges it
by `FormulaList.rec` — the meet starts at the top and only goes down.

Six of the nine chain lemmas are **branch-agnostic**: their `Bool.rec` on
`Nat.ble` needs no equation in hand, because whichever branch fires, the
selected value is one the hypotheses already cover. Only
`meet3_le_left`/`_right`, `le_join3_left`/`_right`, `himp3_intro` and
`himp3_elim` need `Eq Bool (ble a b) s` in the motive.

## What is checked, and what is not

**Checked by the kernel**: that `ipc_excluded_middle_not_provable` is a proof
term for `Not (Provable nil (p or not p))`, and that all **50** declarations
the package adds on top of the Nat prelude are axiom-free.

**Not checked by the kernel, and it cannot be**: that `Provable` is a faithful
encoding of IPC natural deduction. That is a meta-level judgement about the
rule set, and per the brief it is where an unsound shortcut would do the most
damage. I read all eleven constructor types before building anything on them.
They are exactly assumption (as `ax_head` + `weaken`, which between them
generate "the goal occurs anywhere in the context" — the kernel has no `Mem`
relation), `∧I`, `∧E1`, `∧E2`, `∨I1`, `∨I2`, `∨E`, `→I`, `→E`, `⊥E`, with
`not p` the standard abbreviation `imp p bot`. No classical rule is present.

The one point worth stating explicitly, since it is the place a weaker-than-IPC
encoding would hide: **contexts are lists and there is no exchange or
contraction rule.** That loses no derivation, because every use of a hypothesis
goes through membership rather than a positional assumption rule — `ax_head` +
`weaken` reach any position, so e.g. `Provable [A,B,f] f` is
`weaken(weaken(ax_head))`. This is the standard list-context presentation.
Recorded in the fact's `notes` so a referee can check it rather than take it.

Slice 2's non-kernel Rust forward-chaining search
(`ipc_provable::tests::finite_search_discriminates_between_derivable_and_pem`)
corroborates the rule set and is **not** a substitute: it derives `p -> p` and
`(p and q) -> p` and does not derive `p or not p` over the subformula closure
those three queries need. A sanity check on the encoding, not an adequacy
theorem.

## Verifying the checks can fail

Two mutations, both in this worktree, both restored:

- Swapping `ipc_meet3_le_left` for `ipc_meet3_le_right` in the `ax_head`
  case → **all 14 `ipc_soundness` tests fail**.
- Moving `declare_pem_not_provable`'s valuation from `1` to `2` — where
  `p or not p` **is** the top, so nothing is refutable → the kernel **rejects**
  the final theorem with a `TypeMismatch`. The headline result genuinely
  depends on the countermodel value, not on some vacuous route.

The fact's checker discriminates in both directions, as the brief required:

    ipc_soundness_inventory ipc_excluded_middle_not_provable --require-axiom-free  -> exit 0
    ipc_soundness_inventory ipc_excluded_middle_not_provable_FABRICATED ...        -> exit 1
    ipc_soundness_inventory --require-axiom-free --expect-count 50                 -> exit 0
    ipc_soundness_inventory --require-axiom-free --expect-count 49                 -> exit 1

That example lists **every declaration kind**, not just `Declaration::Theorem`:
a theorem inventory returns zero rows for a `Definition`, and `ipc_eval`,
`ipc_ctx_meet` and `ipc_sat` are all definitions, so a theorem-only checker
would answer the existence question wrongly in both directions. Its row set is
a set difference against a kernel carrying only `build_nat_prelude`, recomputed
every run — derived from the environment, not from a list someone has to
remember to update.

`ipc_sat` and `ipc_ctx_meet` are `Definition`s, so kernel admission proves only
well-formedness. Both are pinned by evaluation at concrete arguments against
hand-computed values (magnitudes kept to 0/1/2 — these numerals are unary), and
two of those checks are discriminating: the same list *shape* with head `var 0`
gives 0 and with head `var 1` gives 1, so a definition ignoring the head cannot
pass; `[var 1, var 0]` gives 0 where a tail-ignoring definition would give 1.
`ipc_sat` is pinned in **both** directions — a kernel theorem inhabits it at a
satisfying valuation, and `ipc_sat_not_vacuous` **refutes** it at a
non-satisfying one, so a constantly-true `sat` (which would make the corollary
vacuous) could not pass.

## Gotcha worth carrying

`build_ipc_provable_prelude` and `build_ipc_eval_prelude` **both** call
`build_ipc_heyting_prelude`, which is deliberately uncached, so calling both in
one kernel declares `Formula` twice and fails. Slice 4 needs `Provable` and
`ipc_eval` in one environment, so `ipc_eval::declare_eval` became `pub(crate)`
and this package re-declares it. Any slice 5 has the same constraint.

## Checks run

- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib ipc_` —
  **33 passed, 0 failed** (19 pre-existing `ipc_heyting`/`ipc_provable`/
  `ipc_eval` unaffected, 14 new).
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — clean.
  Needed `#![allow(clippy::many_single_char_names)]` (the chain lemmas are
  stated over `a`/`b`/`c`/`m`/`v`) alongside the `similar_names` allow the
  sibling `ipc_` modules already carry. Clippy also caught a wildcard match arm
  hiding `Declaration::Quotient` in the new example — named explicitly, since
  `Axiom` alone is not the trusted surface.
- `cargo fmt --all --check` — clean.
- `python3 scripts/validate-facts.py` — **2156 facts, 0 errors**, kernel-lean
  1926.
- Did not run `cargo test --workspace` or `./scripts/check.sh` per lane
  instructions; the coordinator re-verifies before merging.

## Commits

`8600a28db` (design record), `446e037df` (uncompiled WIP per protocol),
`63267a3ca` (working slice 4), `a455b3e26` (fact closure + checker).

## What is left

Nothing in this decomposition — slices 1–4 are complete and the fact is closed.
The natural continuations, none of them blocking anything:

- **Completeness** (`eval phi v = 2` for all `v` implies `Provable nil phi`) is
  the converse and is genuinely harder; nothing here needs it.
- More unprovability witnesses reuse everything: `not not p -> p` and Peirce's
  law both fail in this same chain at `p := 1`, and each is now one
  `declare_*` plus one evaluation check — the machinery is general, only the
  formula changes. That is the cheapest way to turn slice 4 into several more
  ADR-0603 row-2 facts.
- The route is `Formula`-generic, so a second countermodel algebra (a Kripke
  frame, or a larger chain) would slot in against the same `ipc_soundness`.
