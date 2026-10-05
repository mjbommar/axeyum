# Lane: denominator — closing the `Nat.Peano`/`Int.Characterization` gap between the two theorem inventories

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, denominator, 2026-08-27).**
[143-fact-gen-nat](143-fact-gen-nat.md) found and reported, without fixing, a
9-theorem gap between `kernel_declaration_projection` (338 `Nat.*` theorems)
and `prelude_theorem_inventory --include-constructed` (329) — the ledger
coverage denominator. This lane found the root cause, fixed the tool that was
actually wrong, and added a standing check so it cannot silently recur.

**Root cause, read from `kernel.environment()`, not from either tool's
output or from the name.** `Nat.Peano.*` (10 declarations: 1 `Definition`
— `iter` — and 9 `Theorem`s) and `Int.Characterization.*` (24 declarations:
1 `Definition` — also named `iter` — and 23 `Theorem`s) are declared by
`build_characterization()`
(`crates/axeyum-lean-kernel/src/characterization.rs`), which
`kernel_declaration_projection.rs` has always built (as the `characterization`
group) and `prelude_theorem_inventory.rs`'s `build_groups` **never called at
all** — not one of that tool's documented, deliberate kind exclusions
(`Axiom`/`Definition`/`Opaque`/`Inductive`/`Constructor`/`Recursor`/
`Quotient`), just a whole prelude group nobody wired in. Confirmed directly:
every `Nat.Peano.*`/`Int.Characterization.*` name in the kernel is
`Declaration::Theorem` (9 + 23 = 32 rows, one `Definition` each for `iter`,
correctly excluded by both tools) with an empty `axiom_footprint` — genuine,
axiom-free, already-proved theorems, exactly the population this ledger's
denominator claims to count.

**Verdict: `prelude_theorem_inventory` was the tool at fault, not the
generator.** `kernel_declaration_projection` was already correct.

**Fix: added a `characterization` group to `prelude_theorem_inventory.rs`'s
`build_groups`**, in the same dependency-order position
`kernel_declaration_projection` uses (after `integer`, before `rat`), and
**unconditional** rather than gated on `--include-constructed` (it costs no
more than the already-unconditional `integer` group, since it is exactly
`build_int_prelude` plus 32 more theorems). Mechanical follow-ons, both
necessary consequences of that fix rather than separately-scoped work:
`scripts/gen-theorem-production-ledger.py`'s `EXPECTED_PRELUDES` gained
`"characterization"` (else its own `--check` gate goes red on the new group),
and `docs/plan/generated/theorem-production-ledger.md` was regenerated.

**New standing check:
`scripts/check-theorem-inventory-completeness.py`.** Runs both
`kernel_declaration_projection` (unfiltered) and `prelude_theorem_inventory
--include-constructed`, extracts each tool's distinct `Declaration::Theorem`
name set, and fails — naming every offending theorem — on any name present in
one and absent from the other, in **either** direction (either tool omitting
a group is the same defect class). `--kdp-tsv`/`--pti-tsv` substitute files
for testing. Against a saved pre-fix TSV pair it correctly reproduces the
original failure (`32 in kernel_declaration_projection only: Int.
Characterization.cases, ... Nat.Peano.categorical, ...`); against the fixed
tree it passes (`1448 distinct theorem names agree`). Unit tests:
`scripts/tests/test_theorem_inventory_completeness.py`, 9 cases. Every guard
mutation-verified in an isolated scratch copy (never the shared checkout,
per CLAUDE.md) by deleting it and confirming exactly the expected test(s)
die — one round found a genuine false-kill (the malformed-row guards were
initially indistinguishable from the empty-result guard because a
single-malformed-line input made both guards fire) and the tests were
corrected to co-occur a well-formed row, isolating each guard properly; all
six guards now killed cleanly with no overlap. Not wired into
`scripts/tests/mutation_controls.py` this round — that registry is a large,
actively-appended shared file and this check's own manual mutation evidence
already satisfies the "guard nothing kills is decoration" bar; a future lane
can fold it in.

**Numbers, before → after (same tree, isolated by rebuilding
`prelude_theorem_inventory` with and without the fix — the committed
`artifacts/ledger-coverage.json` predates this session's other merges and is
NOT a valid baseline on its own):**

| | before (broken tool, this tree) | after (fixed tool) |
|---|---:|---:|
| `kernel_theorems` (pti distinct) | 1,416 | **1,448** (+32, exactly the characterization group) |
| `registered` | 1,026 | **1,035** (+9 — the 9 already-registered `Nat.Peano.*` facts now counted) |
| `curated` | 474 | **474 — unmoved**, as required |
| `unregistered` | 390 | 413 (+23 — the 23 `Int.Characterization.*` theorems, none registered by any fact, are now VISIBLE as unregistered rather than invisible) |
| `registered_kernel_theorems_not_in_denominator` | 36 (incl. all 9 `Nat.Peano.*`) | 27 (the 9 dropped; none were `Int.Characterization.*` since no fact names those yet) |

`Nat.*` bucket: 329 → 338 (+9, exactly `Nat.Peano.*`). `Int.*`/`integer`
bucket: 153 → 176 (+23, exactly `Int.Characterization.*`). Both diffs
confirmed by exact name-set diff against `kernel_declaration_projection`,
zero unexplained names either direction.

`python3 scripts/validate-facts.py`: **1,379 facts, 0 errors**, unchanged by
this lane (no fact files touched, as scoped) — confirmed both before and
after.

**Checked for the SAME defect elsewhere, since the 9 were found by
accident and nobody had checked whether other families differ.** Diffed the
full distinct theorem-name sets of both tools (not just `Nat.`/`Int.`):
**exactly 32 names differ, all `Nat.Peano.*`/`Int.Characterization.*`, zero
in the other direction.** No other prelude has this gap — `axreal`, `rat`,
`string`, `creal`, `complex`, `cpoint` all agree between the two tools once
`characterization` is added.

**Also noticed, not fixed (out of scope — not creal/rat_prelude, but not one
of the three explicitly-scoped files either):**
`crates/axeyum-lean-kernel/src/cross_prelude_collision_tests.rs` has the
identical gap one layer over: its own `build_groups` doc comment claims to
"mirror `examples/prelude_theorem_inventory.rs`'s `build_groups`: same
prelude list" and also never builds `build_characterization`. So
`Nat.Peano.*`/`Int.Characterization.*` names have never been checked for a
cross-prelude declaration-name collision against any other prelude — the
exact incident class that test file exists to catch (see its own module
doc). Left alone this round since it is a `src/` test file outside this
lane's granted scope and outside the three "no-touch" crate paths, so
touching it needs its own authorization.

<!-- plan-section: landed-changes -->

| 2026-08-27 | denominator | Added the missing `characterization` group (`Nat.Peano.*`, `Int.Characterization.*`, 32 axiom-free theorems) to `prelude_theorem_inventory`'s `build_groups`, confirming `kernel_declaration_projection` was already correct; updated `gen-theorem-production-ledger.py`'s `EXPECTED_PRELUDES` and regenerated its ledger doc; regenerated `artifacts/ledger-coverage.json` (kernel_theorems 1,416→1,448, registered 1,026→1,035, curated unmoved at 474); added `scripts/check-theorem-inventory-completeness.py` + 9 unit tests, mutation-verified, so the two tools' theorem-name-set agreement is a standing, checkable guard rather than a fact-generation lane's accidental find |
