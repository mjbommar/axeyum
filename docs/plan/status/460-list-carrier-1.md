# Lane: list-carrier-1 — `List` as a real prelude inductive (ADR-1495/1520/1577 follow-on)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for the theorems and definitions asked for; two
sized negatives`, list-carrier-1, 2026-09-03).**

`List.{u} : Type u -> Type u` (`nil`/`cons`) lands as an ordinary
universe-polymorphic inductive, admitted through the same trusted
`add_inductive` gate as `Nat`/`Bool`/`Exists`/`Acc`, instantiated at `u := 0`
for every operation and theorem — no permutation quotient needed, unlike
Mathlib's `List`-backed `Multiset`/`Finset`, which is exactly why ADR-1520
and ADR-1577 computed ℕ-only carriers instead. See ADR-1579.

**Landed:** the inductive + `length`/`append`/`map`/`foldr`/`reverse`
(`list_prelude.rs`/`ops.rs`); six theorems needing nothing beyond `List` and
`Eq` — `append_assoc`, `append_nil`, `reverse_append` (an internal lemma
`reverse_reverse` needs), `reverse_reverse`, `length_map`, `foldr_append`
(`theorems.rs`); the `List`/`Nat` bridge — `sum`, `length_append`,
`length_reverse`, `sum_append`, `toMultiset`, `count` (`bridge.rs`, after
`build_nat_prelude`, since these need the real named `Nat.add`). All nine
non-private theorems are axiom-free (`Kernel::axiom_footprint = []`, read
from the kernel). 17 new tests (evaluation with negative controls, plus
axiom-footprint coverage), all passing; clippy clean; `nat_prelude::` (422
tests) unaffected. Nine facts registered, one per distinct statement
(`F:list-*`); `validate-facts.py` exits 0; `check-settled-fact-statements.py
--write` regenerated the pin file additively.

Two bugs the kernel caught while landing this (both recorded in ADR-1579,
each a known family from `kernel-proof-engineering.md`): every `Eq`/
congruence call was first built at the recursor's motive level instead of
the carrier's own sort level; `reverse_append`'s base case had
`append_nil`'s direction swapped into `symm_of` backwards.

**Sized negative 1: `List.count_toMultiset` did not land.** The `cons` case
needs a case split on `Nat.beq head a` and a bridge from `Nat.beq head a =
false` to `head <> a` to invoke `Nat.Multiset.count_singleton_of_ne`; that
bridge lemma was not located or built. `bridge.rs`'s
`declare_count_to_multiset` deliberately returns `Err` so
`ListNatBridge::count_to_multiset` is `None` rather than a stub that looks
landed. `List.Perm`/`perm_reverse` (marked "if time remains" in the brief)
were not attempted either.

**Sized negative 2: no ledger-wide registration.** `crates/axeyum-py/src/
kernel/prelude_fields.rs`, `gen-py-prelude-fields.py`, and
`gen-theorem-production-ledger.py`'s `EXPECTED_PRELUDES` were NOT updated —
`prelude_theorem_inventory.rs`'s `build_groups` does not call
`build_list_prelude`/`build_list_nat_bridge`, so `List`'s theorems are
invisible to those tools (a coverage gap, not a red gate: verified
`python3 scripts/gen-theorem-production-ledger.py --check` reports the SAME
staleness — "distinct theorems ROSE 2340 -> 2521" — that exists independent
of this lane, from concurrent lanes' merges to main; `List` contributes zero
to that number since it is not counted at all). A future lane wiring `List`
into `prelude_theorem_inventory.rs` should follow the `characterization`/
`ipc` precedent in that file's own comments (add a `build_list_nat_bridge`
group, add `"list"` to `EXPECTED_PRELUDES`, regenerate).

**`foldl`/`nth` not built** — neither is needed by any landed theorem;
`foldl` needs the "fold as a function, apply at the end" encoding and `nth`
needs a nested `Nat.rec` inside `List.rec`'s cons case, both ordinary work
on top of this module.

**Did not run:** the full workspace `--lib`/`--tests` sweep, `cargo deny
check`, `just foundational-resources`, `just check`/`./scripts/check.sh` in
full.

<!-- plan-section: landed-changes -->

| 2026-09-03 | list-carrier-1 | status stub opened |
| 2026-09-03 | list-carrier-1 | `List` inductive + `length`/`append`/`map`/`foldr`/`reverse` + 6 pure-`List` theorems (`e11654eed`) |
| 2026-09-03 | list-carrier-1 | `List`/`Nat.Multiset` bridge: `sum`/`length_append`/`length_reverse`/`sum_append`/`toMultiset`/`count` (`2bc7f83af`) |
| 2026-09-03 | list-carrier-1 | ADR-1579 (`df42b7dc0`) |
| 2026-09-03 | list-carrier-1 | 9 `F:list-*` facts registered, `validate-facts.py` exit 0 (`cf63af1b6`) |
