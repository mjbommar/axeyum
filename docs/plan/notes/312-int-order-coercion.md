# Notes: 312-int-order-coercion

Detail moved out of [`../status/312-int-order-coercion.md`](../status/312-int-order-coercion.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Dispatch: both `declare_ofnat_order_coercions` and `declare_dest_elim` run
right after `order::declare_difference_lemmas` in `int_prelude.rs`'s build
list (their only prelude dependency).

## `crates/axeyum-lean-kernel/src/nat_prelude/add_pos.rs` (new)

`Nat.add_pos_right : ∀ {b} (a), 0 < b → 0 < a + b` — a case split on `b` via
`NatOps::induct` (the `ih` unused, same shape as `order_more.rs`'s
`zero_lt_of_ne_zero`): at `zero` the hypothesis `Lt 0 0` is impossible
(`Nat.not_lt_zero` at `zero`); at `succ k`, `add a (succ k)` is definitionally
`succ (add a k)` (`Nat.add` recurses on its RIGHT argument), so the
conclusion is exactly `NatOps::zero_lt_succ (add a k)`, independent of the
hypothesis. Dispatched right after `declare_order_more` in `nat_prelude.rs`.

## Mirror-flip check

All five are theorems about the SAME `Int.le`/`Int.lt`/`Int.add`/`Int.ofNat`
and `Nat.add`/`Nat.lt` this kernel already has — no new definition
introduced by any of them, so the definition-vs-theorem-about-a-different-
definition criterion is not in play; these are pure order/coercion
corollaries. Confirmed against the pinned Mathlib v4.30.0 source (commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`) via the fact files'
`formal.statement`.

## Evidence

Each of the five facts got a three-row shape, mirroring `int-order-add`'s
convention from the same day (`docs/plan/status/281-int-order-add.md`):

1. `kernel-<Name>` — the kernel's own rendered Pi type (`int_theorem_inventory`
   for the four `Int` facts, `nat_theorem_inventory` for `Nat.add_pos_right`,
   both `--release`), matched on exact columns.
2. `footprint-<Name>` — `nat_axiom_inventory --include-constructed
   --require-axiom-free integer` (or `nat`), backed by
   `derived_laws_have_no_axiom_footprint` (`int_prelude_tests.rs`, pin
   recounted 187 → 191 with `scripts/recount-pinned-inventory.py`) or
   `theorem_axiom_footprint -- Nat.add_pos_right` directly.
3. `coverage-<Name>` — `every_int_declaration_is_checked_and_axiom_free` /
   `every_nat_declaration_is_checked_and_axiom_free`, derived from
   `kernel.environment()` directly.

**Every checker_command was executed twice before being written into a fact
file** — once against the real name (must exit 0) and once against a
fabricated name substituted in place of the real one (must exit nonzero) —
not merely constructed by analogy to the template. All ten pairs
discriminated correctly.

`python3 scripts/check-fact-depends-derived.py --fix` added three missing
edges to `F:ml430-nat-add-pos-right-e43374dc`'s `depends_on`
(`F:nat-le-succ-succ`, `F:nat-not-lt-zero`, `F:nat-zero-le` — the concrete
proof-term dependencies of `NatOps::zero_lt_succ`/`Nat.not_lt_zero`); the
four `Int` facts needed no fix. `python3 scripts/validate-facts.py`: 0
errors. `scripts/check-mirror-statement-fidelity.py`: PASS, 0 violations.

## Checks run (foreground, this session)

- `cargo check -p axeyum-lean-kernel --lib --tests` — clean (caught the
  `derived_laws` array-size mismatch immediately: plain `cargo check`
  without `--tests` does not compile `#[cfg(test)]` code and would have
  missed it).
- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib int_prelude::`
  — **49 passed, 0 failed** (includes `every_int_declaration_is_checked_and_axiom_free`,
  `derived_laws_have_no_axiom_footprint`).
- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib nat_prelude::`
  — first run: **176 passed, 1 failed** (`the_build_is_deterministic`,
  pinned count `93 + 571` vs actual `665`); fixed to `93 + 572` (one new
  theorem, `Nat.add_pos_right`) from the panic message, never incremented by
  hand; second run: **177 passed, 0 failed**.
- `cargo fmt --edition 2024 <file>` on each touched/new file (never
  `cargo fmt -p`/`cargo fmt --all`, per the shared-worktree rule — though
  this worktree is not currently shared, the habit costs nothing).
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — clean.
- Did **not** run the workspace-wide gate (`just check` / `check.sh`), per
  the task's scope.

## Commits

- `a70e2dc4d` — the five new theorems (`order_coercion.rs`, `add_pos.rs`),
  `derived_laws` recount 187 → 191, nat determinism pin `93+571` → `93+572`.
- `c97b93bc2` — all five facts: evidence attached, `epistemic_status` →
  `proved`, `depends_on` auto-fixed for the `Nat` fact.

## Remaining work in this family

None dispatched. `order_coercion.rs`'s local `shift_predicate` re-derivation
is available if another `Exists.elim`-over-`le_dest`/`lt_dest` construction
is needed later — check there before widening `order.rs`'s private one or
re-deriving a third copy.
