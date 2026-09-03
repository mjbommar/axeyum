# Lane: list-carrier-2 — `List.count_toMultiset` and `List.Perm` (ADR-1579 follow-on)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for everything asked`, list-carrier-2, 2026-09-03).**
Closes both sized negatives ADR-1579 (`list-carrier-1`) left open:
`List.count_toMultiset` landed, and `List.Perm` landed with all four
requested theorems (`perm_refl`, `perm_symm`, `perm_reverse`,
`perm_append_comm`). `List` is also registered in every cross-prelude
inventory tool for the first time. See ADR-1583.

**The `Nat.beq` bridge — no new lemma needed.** `Nat.ne_of_beq_eq_false`/
`Nat.beq_eq_false_of_ne` already existed in `nat_prelude` (predating this
lane), and `List.count_toMultiset`'s proof does not even consume them:
`Nat.Multiset.count_singleton_of_ne` is already stated directly in terms of
`beq` (`beq x a = false -> count (singleton a) x = 0`), not `Not (Eq _ _)`,
so the whole beq-to-ne detour list-carrier-1's handoff named as the blocker
was unnecessary. Only `Nat.beq_comm` was needed, to flip the case split's
own hypothesis direction.

**Landed:** `List.count_toMultiset` (bridge.rs); two new prerequisites,
`List.count_append` and `List.count_reverse` (perm.rs); `List.max`,
`List.Perm`, and its four theorems `perm_refl`/`perm_symm`/`perm_reverse`/
`perm_append_comm` (perm.rs). All seven new theorems are axiom-free
(`Kernel::axiom_footprint = []`, read from the kernel). `List.Perm` reuses
`Nat.Finset.allBelow` and its two reflection theorems directly (ADR-1577)
rather than rebuilding an equivalent bounded loop. None of the four `Perm`
theorems needed `List.max` proved to be an actual upper bound (their
pointwise count identities hold unconditionally in the compared index);
`perm_symm` is the one exception, needing `Nat.add_comm` + a `succ`
congruence to relate the two lists' bounds, plus a new small combinator
`ops::transport_along` to move the bound-membership hypothesis across that
equality. Evaluation tests include the requested negative controls by
direct `def_eq` computation: `Perm [1,2] [2,1] = true`,
`Perm [1,2] [1,2,2] = false` (and explicitly not `true`).

**Six direction bugs found and fixed**, all the same `symm_of`'s-`(a,b)`-
must-match-its-hypothesis's-own-direction class CLAUDE.md's own gotchas
already name as the single most common bug here. Found by instantiating a
proof step at free (not yet abstracted) fvars pushed into an explicit
`LocalContext`, comparing `Kernel::infer_in` against the expected type via
`Kernel::render_lean` side by side — exactly `kernel-proof-engineering.md`'s
prescribed technique, since the kernel's own `TypeMismatch { expected:
ExprId(..), got: ExprId(..) }` names neither side by value.

**Inventory registration (deliverable 5):** `prelude_theorem_inventory.rs`,
`kernel_declaration_projection.rs`, and `theorem_dependency_inventory.rs`
all gain a `list` group (verified `--require-declaration
List.count_toMultiset`/`List.perm_symm` found, a nonexistent name errors
and exits 1). `theorem_dependency_inventory.rs`'s addition mattered
specifically for `check-fact-depends-derived.py --fix`: without `List` in
its shared kernel build, `List.count_reverse`'s direct use of
`List.count_append` was invisible to it and `--fix` would report
`missing_edges=0` for the wrong reason. `gen-theorem-production-ledger.py`'s
`EXPECTED_PRELUDES` gains `list` (verified `--check` raised `coverage
changed` first, against the old tuple). `gen-py-prelude-fields.py` gains
`ListPrelude` only (all-`NameId` fields, parses cleanly) — `ListNatBridge`/
`ListPerm` are deliberately NOT registered there: `ListNatBridge::
count_to_multiset` is `Option<NameId>`, a type that generator's `collect()`
does not classify, and teaching it optional fields is out of this lane's
scope. Added a matching `build_list_prelude` PyO3 method to
`crates/axeyum-py/src/kernel.rs` so the generated `list()` field-table
function has a real caller (an unregistered `kind` compiles to a `never
used` warning, which `-D warnings` turns into a build failure).

**Headline numbers after registration:** `docs/plan/generated/
theorem-production-ledger.md`: distinct theorems 2340 -> 2539 (17 of that
rise is `list`'s own originated theorems -- 9 from list-carrier-1 plus 8
this lane; the rest is concurrent lanes' merges to `main` since the ledger
was last regenerated, per `docs/plan/status/460-list-carrier-1.md`'s own
note that this figure was already stale independent of the `List` work).
`artifacts/ledger-coverage.json`: `kernel_theorems` 2340 -> 2539, matching
(both ledgers read the same kernel measurement and must agree, per
`check-merge-hygiene.sh`'s own cross-consistency check).

**Facts (deliverable 6):** seven facts registered, one per distinct
statement (`F:list-count-to-multiset`, `F:list-count-append`,
`F:list-count-reverse`, `F:list-perm-refl`, `F:list-perm-symm`,
`F:list-perm-reverse`, `F:list-perm-append-comm`), all `epistemic_status:
proved`, `axiom_footprint: []`. `depends_on` populated by
`check-fact-depends-derived.py --fix` (not hand-written) once
`theorem_dependency_inventory.rs` could see `List` at all --
`missing_edges=0` after. `python3 scripts/validate-facts.py` exits 0 (2730
facts checked, 0 errors). `check-settled-fact-statements.py --write` wrote
2461 pins, 0 unpinned. ADR-1583 (amending ADR-1579) records the whole
session.

**Did not run:** the full workspace `--lib`/`--tests` sweep, `cargo deny
check`, `just foundational-resources`, `just check`/`./scripts/check.sh` in
full.

<!-- plan-section: landed-changes -->

| 2026-09-03 | list-carrier-2 | status stub opened (`a2601231a`) |
| 2026-09-03 | list-carrier-2 | `List.count_toMultiset` landed -- the beq bridge already existed (`fc6494f48`) |
| 2026-09-03 | list-carrier-2 | `List.Perm` landed with all four theorems, `ops::transport_along` added (`c1ed177ef`) |
| 2026-09-03 | list-carrier-2 | `list` registered in the theorem/coverage ledgers, `build_list_prelude` PyO3 method added (`a27b965cc`) |
| 2026-09-03 | list-carrier-2 | `list_theorem_inventory`/axiom-footprint coverage extended to Perm (`0217c3338`) |
| 2026-09-03 | list-carrier-2 | ADR-1583, seven facts, `theorem_dependency_inventory` registration, `check-fact-depends-derived.py --fix` (`6a0e13fcb`) |
